(** * Surface: declarative elaboration rules (milestone M6)

    The specification of elaboration: a bidirectional relation between a
    surface expression and its Core translation.

    - [Γ ⊩[E;L] s ⇒ τ ⇝ e] : [s] synthesizes the type [τ] and elaborates
      to the Core expression [e];
    - [Γ ⊩[E;L] s ⇐ τ ⇝ e] : [s] is checked against the expected type [τ];
    - [Γ ⊩*[E;L] ss ⇒ τs ⇝ es], [Γ ⊩*[E;L] ss ⇐ τs ⇝ es] : lists;
    - [Γ ⊩[E;L] s ⦂ a ⇒ τ ⇝ e] : the right-hand side of a binding with an
      optional type annotation [a].

    [E] is the global information (data types, function signatures,
    traits), [L] the control environment (enclosing labels, the error type
    that may escape) and [Γ] the local variables with their names.

    Checking falls back on synthesis followed by an implicit conversion
    [⊩ᶜ[E] e : τ' ≼ τ ⇝ e'] (equality, or the promotion of a suberror to
    [Error]).  The type arguments of a generic function are not determined
    by the rules: finding them is the elaborator's business (decision 65).

    [ElabTyped.v] proves that every elaborated expression is well typed in
    Core ([elab_typed]).

    Patterns have their own judgment [⊩ᵖ[E] sp : τ ⇝ q ⊣ Δ]: the surface
    pattern [sp] matches values of type [τ], elaborates to the Core
    pattern [q] and binds the named variables [Δ].

    Covered so far: the core language of milestone M1 (variables,
    literals, operators, [let], [if], tuples, functions and calls), the
    builtins [not], [ignore], [panic] and [abort], and from milestone M2
    constructors, records, patterns, [match], field access and the
    projections of tuple structs; from milestone M3 [let mut], assignment,
    arrays, [Ref::new], [Array::make], [while], [for], [for .. in] over
    integer ranges and arrays, labelled blocks and [break]/[continue]/[return]. *)

From Stdlib Require Import List ZArith String Bool.
From MoonRocq.Prelude Require Import Result EqDec Ident.
From MoonRocq.Core Require Import Syntax Prim Subst Typing.
From MoonRocq.Surface Require Import Syntax Base.
Import ListNotations.

Local Open Scope string_scope.

(** ** Global information *)

Record senv : Type := mk_senv {
  se_tys   : list (ident * nat);           (** data types in scope, with their arity *)
  se_hdr   : genv;                         (** data types and function signatures *)
  se_sinfo : list (ident * list ident);    (** field names of record structs *)
  se_tps   : list ident;                   (** type parameters in scope *)
  se_x     : xenv                          (** traits and instances *)
}.

(** The Core type denoted by a surface type. *)
Definition ety (E : senv) (t : sty) : result ty elab_error :=
  elab_ty (se_tys E) (se_tps E) t.

(** An optional annotation, if present, denotes [τ]. *)
Definition ann_ok (E : senv) (a : option sty) (τ : ty) : Prop :=
  match a with
  | Some t => ety E t = Ok τ
  | None => True
  end.

(** The effect annotation of a lambda: none, [noraise], or [raise t]. *)
Definition eff_ann (E : senv) (a : option (option sty)) (ε : ty) : Prop :=
  match a with
  | None => True
  | Some None => ε = TNever
  | Some (Some t) => ety E t = Ok ε
  end.

(** Without annotation nor expected type, a lambda does not raise. *)
Definition eff_syn (E : senv) (a : option (option sty)) (ε : ty) : Prop :=
  match a with
  | None => ε = TNever
  | Some _ => eff_ann E a ε
  end.

(** Trait bounds of a global function (milestone M5). *)
Definition sbounds (E : senv) (g : ident) : list (ident * nat) :=
  match assoc g (x_bounds (se_x E)) with Some b => b | None => [] end.

(** [T] is an error type ([suberror]). *)
Definition err_type (E : senv) (T : ident) : Prop :=
  exists td, lookup_ty (se_hdr E) T = Some td /\ td_err td = true.

(** A name that is neither local nor a global function: a builtin. *)
Definition builtin (E : senv) (Γ : lctx) (g : ident) : Prop :=
  lookup_local g Γ = None /\ lookup_fn (se_hdr E) g = None.

(** The Core view of the environments. *)
Definition ctx_of (Γ : lctx) : ctx := map snd Γ.
Definition cc_of (L : cenv) : cctx := mk_cctx (core_labels (ce_labs L)) (ce_exn L).

(** The control environment of a function body with result [r] and effect
    [ε]: the body is a block, the target of [return]. *)
Definition fun_env (r ε : ty) : cenv := mk_cenv [mk_lab None LKFun [] r] ε.

(** The parameters of a lambda, innermost (first parameter) first. *)
Definition lam_ctx (ps : list (ident * option sty)) (τs : list ty) : lctx :=
  combine (map (fun xa => Some (fst xa)) ps) τs.

(** Parameter types, given by the annotations where present... *)
Definition params_ann (E : senv) (ps : list (ident * option sty)) (τs : list ty) : Prop :=
  Forall2 (fun xa τ => ann_ok E (snd xa) τ) ps τs.

(** ... or by annotations only. *)
Definition params_syn (E : senv) (ps : list (ident * option sty)) (τs : list ty) : Prop :=
  Forall2 (fun xa τ => exists t, snd xa = Some t /\ ety E t = Ok τ) ps τs.

(** The type of the global function [fd] at type arguments [ts]. *)
Definition fn_inst (fd : fdef) (ts : list ty) : ty :=
  TArrow (map (tsubst (inst ts)) (fd_params fd)) (tsubst (inst ts) (fd_ret fd))
         (tsubst (inst ts) (fd_eff fd)).

(** A local variable of cell type is a [let mut] variable. *)
Definition is_cell (τ : ty) : bool := match τ with TRef _ => true | _ => false end.

Definition int_lit (s : sexpr) : bool :=
  match s with SLit _ (SLInt _ _) => true | _ => false end.

(** A literal on its own: an unsuffixed integer is an [Int]. *)
Definition lit_of (l : slit) : option lit :=
  match l with
  | SLUnit => Some LUnit
  | SLBool b => Some (LBool b)
  | SLInt ko z =>
      let k := match ko with Some k => k | None => I32 end in
      if int_in_range k z then Some (LInt k z) else None
  | SLChar c => Some (LChar c)
  | SLDouble b => Some (LDouble b)
  | SLFloat b => Some (LFloat b)
  | SLString s => Some (LString s)
  end.

(** The result type of the binary operator [op] on operands of type [τ]
    (see [elab_binop]). *)
Definition binop_res (op : ident) (τ : ty) : ty :=
  match assoc op arith_ops, τ with
  | Some _, TBase (BInt _) => τ
  | Some AAdd, TBase BString => τ
  | _, _ => TBool
  end.

(** The callee of [f(args)] is an ordinary expression: not a global
    function, builtin, constructor or [T::m]. *)
Definition callee (Γ : lctx) (f : sexpr) : Prop :=
  match f with
  | SVar _ g => lookup_local g Γ <> None
  | SConstr _ _ _ | SQual _ _ _ => False
  | _ => True
  end.

(** ** Calls

    A call raising [ε] is allowed where [ε] may escape; a call raising a
    suberror [T] is also allowed where [Error] may escape, and then its
    error is promoted.  The callee and the arguments are evaluated first,
    into a tuple, so that only the call itself is inside the [try]
    (decision 66). *)

Definition call_allowed (E : senv) (ε ρ : ty) : Prop :=
  match ε, ρ with
  | TData T [], TError => err_type E T
  | _, _ => eff_le ε ρ
  end.

Definition call_ok (E : senv) (L : cenv) (ε : ty) : Prop := call_allowed E ε (ce_exn L).

Definition promote_call (T : ident) (ε r : ty) (f : expr) (es : list expr) : expr :=
  ELet (ETuple (f :: es))
       (ETry (EApp (EProj (EVar 0) 0) (map (fun i => EProj (EVar 0) i) (seq 1 (List.length es))))
             ε (ERaise (EUp T (EVar 0)) r) (EVar 0)).

Definition wrap_call (L : cenv) (ε r : ty) (f : expr) (es : list expr) : expr :=
  match ε, ce_exn L with
  | TData T [], TError => promote_call T ε r f es
  | _, _ => EApp f es
  end.

(** ** Implicit conversions *)

Reserved Notation "⊩ᶜ[ E ] e : τ ≼ τ' ⇝ e'"
  (at level 70, E at level 200, e at level 60, τ at level 60, τ' at level 60,
   e' at level 60, no associativity, format "⊩ᶜ[ E ]  e  :  τ  ≼  τ'  ⇝  e'").

Inductive coerce_rel (E : senv) : expr -> ty -> ty -> expr -> Prop :=
| Co_Refl e τ :
    ⊩ᶜ[E] e : τ ≼ τ ⇝ e
| Co_Up e T :
    err_type E T ->
    ⊩ᶜ[E] e : TData T [] ≼ TError ⇝ EUp T e
where "⊩ᶜ[ E ] e : τ ≼ τ' ⇝ e'" := (coerce_rel E e τ τ' e').

(** ** Data types *)

Definition ctor_in (c : ident) (td : tdef) : bool :=
  match lookup_ctor td c with Some _ => true | None => false end.

(** A record struct (built with [{ .. }], not by its constructor name). *)
Definition is_rec (E : senv) (T : ident) : bool :=
  match assoc T (se_sinfo E) with Some _ => true | None => false end.

Definition tq_ok (tq : option ident) (T : ident) : Prop :=
  match tq with Some T' => T' = T | None => True end.

(** The data type of the constructor [tq::c] when nothing is expected: the
    named type, or the only type (other than record structs) declaring a
    constructor [c]. *)
Definition ctor_pick (E : senv) (tq : option ident) (c T : ident) : Prop :=
  match tq with
  | Some T' => T' = T
  | None =>
      map td_name (filter (fun td => negb (is_rec E (td_name td)) && ctor_in c td)
                          (ge_types (se_hdr E))) = [T]
  end.

(** The error type of a constructor pattern on [Error]: the named type, or
    the only error type declaring [c]. *)
Definition err_owner (E : senv) (tq : option ident) (c T : ident) : Prop :=
  match tq with
  | Some T' => T' = T
  | None =>
      map td_name (filter (fun td => td_err td && ctor_in c td) (ge_types (se_hdr E))) = [T]
  end.

(** Field [i] of a value [e] of a single-constructor type [T[ts]]: a
    one-branch [match]; a [mut] field holds a cell, whose content is read. *)
Definition proj_pats (i : nat) (q : pat) (k n : nat) : list pat :=
  map (fun j => if Nat.eqb j i then q else PWild) (seq k n).

Definition field_proj (E : senv) (T : ident) (ts : list ty) (i : nat) (e : expr) :
    option (expr * ty) :=
  match lookup_ty (se_hdr E) T with
  | Some td =>
      match td_ctors td with
      | [cd] =>
          let fs := map (tsubst (inst ts)) (cd_fields cd) in
          match nth_error fs i with
          | Some τ =>
              let '(q, τr) := match τ with TRef t => (PRef PVar, t) | _ => (PVar, τ) end in
              Some (EMatch e τr [(PConstr (cd_name cd) (proj_pats i q 0 (List.length fs)), EVar 0)], τr)
          | None => None
          end
      | _ => None
      end
  | None => None
  end.

(** The sub-patterns of a record pattern, put in field order: field [j]
    gets the pattern written for it, or [_] if the pattern is open ([..]). *)
Fixpoint assemble (op : bool) (given : list (nat * pat * lctx)) (j : nat) (fs : list ty) :
    option (list pat * lctx) :=
  match fs with
  | [] => Some ([], [])
  | _ :: fs' =>
      match match find (fun x => Nat.eqb (fst (fst x)) j) given with
            | Some (_, q, Δ) => Some (q, Δ)
            | None => if op then Some (PWild, []) else None
            end,
            assemble op given (S j) fs' with
      | Some (q, Δ), Some (qs, Δs) => Some (q :: qs, List.app Δ Δs)
      | _, _ => None
      end
  end.

(** The record struct built by [{ fields }] when nothing is expected: the
    named one, or the only record struct with exactly these field names. *)
Definition same_fields (declared written : list ident) : bool :=
  Nat.eqb (List.length declared) (List.length written) &&
  forallb (fun f => match index_of f declared with Some _ => true | None => false end) written.

Definition rec_pick (E : senv) (tq : option ident) (written : list ident) (T : ident) : Prop :=
  match tq with
  | Some T' => T' = T
  | None => map fst (filter (fun tf => same_fields (snd tf) written) (se_sinfo E)) = [T]
  end.

(** The first position of [j] in [is]. *)
Fixpoint pos_of (j : nat) (ixs : list nat) : option nat :=
  match ixs with
  | [] => None
  | i :: ixs' => if Nat.eqb i j then Some 0 else option_map S (pos_of j ixs')
  end.

(** A record [{ f1: e1, .., fm: em }] evaluates its fields in source order,
    into a tuple bound to [EVar 0]; field [j] of the constructor is the
    component of the field written for it.  [ixs] are the field indices in
    source order; every field must be written ([m = n]). *)
Definition rec_vars (ixs : list nat) (n : nat) : option (list expr) :=
  if Nat.eqb (List.length ixs) n then
    all_some (map (fun j => option_map (fun k => EProj (EVar 0) k) (pos_of j ixs)) (seq 0 n))
  else None.

(** The arm of a [match] that gives its type: the first one that does not
    certainly jump away, else the first one. *)
Definition pick_arm (cases : list (spat * sexpr)) : option (spat * sexpr) :=
  match find (fun c => negb (diverges (snd c))) cases with
  | Some c => Some c
  | None => hd_error cases
  end.

(** ** State and loops (milestone M3) *)

(** The right-hand side of [x = v] or [x op= v] ([cur] reads the old value). *)
Definition upd_rhs (p : pos) (op : option ident) (τ : ty) (cur v e : expr) : Prop :=
  match op with
  | None => e = v
  | Some o => binop_res o τ = τ /\ elab_binop p o τ cur v = Ok e
  end.

(** The [mut] field [i] of [T[ts]]: its constructor, number of fields and
    content type. *)
Definition field_cell (E : senv) (T : ident) (ts : list ty) (i : nat) : option (ident * nat * ty) :=
  match lookup_ty (se_hdr E) T with
  | Some td =>
      match td_ctors td with
      | [cd] =>
          let fs := map (tsubst (inst ts)) (cd_fields cd) in
          match nth_error fs i with
          | Some (TRef t) => Some (cd_name cd, List.length fs, t)
          | _ => None
          end
      | _ => None
      end
  | None => None
  end.

(** The builtin [struct Ref[T] { mut val : T }] is declared. *)
Definition ref_ok (E : senv) : Prop :=
  exists td cd, lookup_ty (se_hdr E) "Ref" = Some td /\ td_tparams td = 1 /\
                lookup_ctor td "Ref" = Some cd /\ cd_fields cd = [TRef (TVar 0)].

(** Named local variables, the first one innermost. *)
Definition names_ctx (xs : list ident) (τs : list ty) : lctx := combine (map Some xs) τs.

(** A loop seen from its condition, update or [nobreak] clause. *)
Definition hd_env (ps : list ty) (τ : ty) (L : cenv) : cenv := push_lab (mk_lab None LKHead ps τ) L.

Definition while_loop (τ : ty) (c b nb : expr) : expr :=
  ELoop (ETuple []) [] τ (EIf c (ELet b (EJump CCont 0 (ETuple []) τ)) nb).

(** The next values of loop variables: the update written for variable
    [i], else the variable itself, which is [EVar (off + i)]. *)
Definition upd_next (off : nat) (names : list ident) (us : list (ident * expr)) : list expr :=
  map (fun i => match find (fun yu => match index_of (fst yu) names with
                                      | Some j => Nat.eqb j i
                                      | None => false
                                      end) us with
                | Some (_, u) => u
                | None => EVar (off + i)
                end) (seq 0 (List.length names)).

(** The next values of the variables of a [for] loop, under the binder of
    the body's result. *)
Definition for_next (names : list ident) (us : list (ident * expr)) : list expr :=
  upd_next 1 names us.

Definition for_loop (es : list expr) (τs : list ty) (τ : ty) (c : option expr) (b : expr)
    (names : list ident) (us : list (ident * expr)) (nb : expr) : expr :=
  let step := ELet (eblock TUnit b) (EJump CCont 0 (ETuple (for_next names us)) τ) in
  ELoop (ETuple es) τs τ (match c with Some c0 => EIf c0 step nb | None => step end).

(** *** [for .. in]

    A source (integer range or array) is bound to two hidden variables
    before the loop: a range to its start and bound, an array to itself
    and its length.  The loop variables are the iteration variables
    ([fi_ivs]: the position, and for an inclusive range a [done] flag),
    then the state variables.  Inside, the body is a block within the
    block that computes the next state, as for [for]. *)

Definition range_of (s : sexpr) : option range_kind :=
  match s with SInfix _ op _ _ => range_op op | _ => None end.

Definition fi_t1 (it : iter_src) : ty :=
  match it with IRange _ kk => TInt kk | IArray k t => TArray k t end.
Definition fi_t2 (it : iter_src) : ty :=
  match it with IRange _ kk => TInt kk | IArray _ _ => TIndex end.

Definition fi_ivs (it : iter_src) : list ty :=
  match it with
  | IRange RUpIncl kk | IRange RDownIncl kk => [TInt kk; TBool]
  | IRange _ kk => [TInt kk]
  | IArray _ _ => [TIndex]
  end.

(** Initial iteration variables, under the two hidden variables. *)
Definition fi_init (it : iter_src) : list expr :=
  match it with
  | IRange RUpIncl _ | IRange RDownIncl _ => [EVar 1; e_false]
  | IRange _ _ => [EVar 1]
  | IArray _ _ => [ELit (LInt I32 0)]
  end.

(** Inside the loop the position is [EVar 0], the [done] flag [EVar 1],
    the bound (or length) [EVar n] and the array [EVar (S n)], where [n]
    is the number of loop variables. *)
Definition fi_n (it : iter_src) (τs : list ty) : nat := List.length (fi_ivs it) + List.length τs.

Definition fi_cond (it : iter_src) (n : nat) : expr :=
  let v := EVar 0 in
  let bound := EVar n in
  match it with
  | IRange RUpExcl kk => icmp CLt kk v bound
  | IRange RUpIncl kk => EIf (EVar 1) e_false (icmp CLe kk v bound)
  | IRange RDownExcl kk => icmp CGt kk v bound
  | IRange RDownIncl kk => EIf (EVar 1) e_false (icmp CGe kk v bound)
  | IArray _ _ => icmp CLt I32 v bound
  end.

Definition fi_elem (it : iter_src) (n : nat) : expr :=
  match it with
  | IRange RDownExcl kk => iarith ASub kk (EVar 0) (int1 kk)
  | IRange _ _ => EVar 0
  | IArray k t => EMem (MIndex k t) [EVar (S n); EVar 0]
  end.

Definition fi_elem_ty (it : iter_src) : ty :=
  match it with IRange _ kk => TInt kk | IArray _ t => t end.

(** The next iteration variables, after the state block's binder and the
    pattern's [d] bindings; inclusive ranges stop at the bound without
    stepping past it. *)
Definition fi_next (it : iter_src) (d n : nat) : list expr :=
  let vv := EVar (1 + d) in
  let bb := EVar (1 + d + n) in
  match it with
  | IRange RUpExcl kk => [iarith AAdd kk vv (int1 kk)]
  | IRange RDownExcl kk => [iarith ASub kk vv (int1 kk)]
  | IRange RUpIncl kk => [EIf (icmp CEq kk vv bb) vv (iarith AAdd kk vv (int1 kk)); icmp CEq kk vv bb]
  | IRange RDownIncl kk => [EIf (icmp CEq kk vv bb) vv (iarith ASub kk vv (int1 kk)); icmp CEq kk vv bb]
  | IArray _ _ => [iarith AAdd I32 vv (int1 I32)]
  end.

(** The contexts: outside the loop (two hidden variables), and inside. *)
Definition fo_ctx (it : iter_src) (Γ : lctx) : lctx := (None, fi_t2 it) :: (None, fi_t1 it) :: Γ.
Definition fl_ctx (it : iter_src) (names : list ident) (τs : list ty) (Γ : lctx) : lctx :=
  List.app (map (fun t => (None, t)) (fi_ivs it)) (List.app (names_ctx names τs) (fo_ctx it Γ)).

(** The control environments: the loop, the state block, the body. *)
Definition fi_loop_env (it : iter_src) (τs : list ty) (τ : ty) (L : cenv) : cenv :=
  hd_env (List.app (fi_ivs it) τs) τ L.
Definition fi_state_env (it : iter_src) (τs : list ty) (τ : ty) (L : cenv) : cenv :=
  push_lab (mk_lab None LKHead [] (TTuple τs)) (fi_loop_env it τs τ L).
Definition fi_body_env (x : option ident) (it : iter_src) (τs : list ty) (τ : ty) (L : cenv) : cenv :=
  push_lab (mk_lab x LKForInBody [] TUnit) (fi_state_env it τs τ L).

Definition forin_loop (it : iter_src) (e1 e2 : expr) (es : list expr) (τs : list ty) (τ : ty)
    (q : pat) (scrut : expr) (d : nat) (b : expr) (names : list ident) (us : list (ident * expr))
    (nb : expr) : expr :=
  let n := fi_n it τs in
  let state := upd_next (1 + d + List.length (fi_ivs it)) names us in
  let blk := eblock (TTuple τs) (ELet (eblock TUnit b) (ETuple state)) in
  let next := List.app (fi_next it d n) (map (fun j => EProj (EVar 0) j) (seq 0 (List.length names))) in
  let step := ELet blk (EJump CCont 0 (ETuple next) τ) in
  ELet e1 (ELet e2
    (ELoop (ETuple (List.app (fi_init it) es)) (List.app (fi_ivs it) τs) τ
           (EIf (fi_cond it n) (EMatch scrut τ [(q, step)]) nb))).

Definition is_jump (s : sexpr) : bool :=
  match s with SBreak _ _ _ | SContinue _ _ _ | SReturn _ _ => true | _ => false end.

(** ** Patterns

    - [⊩ᵖ[E] sp : τ ⇝ q ⊣ Δ] : pattern [sp] against type [τ];
    - [⊩ᶠ[E] sp : τ ⇝ q ⊣ Δ] : against a field of type [τ]: a [mut] field
      holds a cell, and the pattern applies to its content;
    - [⊩ᶠ*[E] sps : τs ⇝ qs ⊣ Δ] : a list of fields;
    - [⊩ⁿ[E] fps : names ; fs ⇝ given] : named fields of a record pattern,
      in source order, with their field index. *)

Reserved Notation "⊩ᵖ[ E ] sp : τ ⇝ q ⊣ Δ"
  (at level 70, E at level 200, sp at level 60, τ at level 60, q at level 60,
   Δ at level 60, no associativity, format "⊩ᵖ[ E ]  sp  :  τ  ⇝  q  ⊣  Δ").
Reserved Notation "⊩ᶠ[ E ] sp : τ ⇝ q ⊣ Δ"
  (at level 70, E at level 200, sp at level 60, τ at level 60, q at level 60,
   Δ at level 60, no associativity, format "⊩ᶠ[ E ]  sp  :  τ  ⇝  q  ⊣  Δ").
Reserved Notation "⊩ᶠ*[ E ] sps : τs ⇝ qs ⊣ Δ"
  (at level 70, E at level 200, sps at level 60, τs at level 60, qs at level 60,
   Δ at level 60, no associativity, format "⊩ᶠ*[ E ]  sps  :  τs  ⇝  qs  ⊣  Δ").
Reserved Notation "⊩ⁿ[ E ] fps : names ; fs ⇝ given"
  (at level 70, E at level 200, fps at level 60, names at level 60, fs at level 60,
   given at level 60, no associativity, format "⊩ⁿ[ E ]  fps  :  names ;  fs  ⇝  given").

Inductive spat_ok (E : senv) : spat -> ty -> pat -> lctx -> Prop :=
| SP_Wild p τ :
    ⊩ᵖ[E] SPWild p : τ ⇝ PWild ⊣ []
| SP_Var p x τ :
    ⊩ᵖ[E] SPVar p x : τ ⇝ PVar ⊣ [(Some x, τ)]
| SP_Lit p l l' τ :
    elab_lit p (Some τ) l = Ok l' ->
    TBase (lit_ty l') = τ ->
    ⊩ᵖ[E] SPLit p l : τ ⇝ PLit l' ⊣ []
| SP_Tuple p sps τs qs Δ :
    ⊩ᶠ*[E] sps : τs ⇝ qs ⊣ Δ ->
    ⊩ᵖ[E] SPTuple p sps : TTuple τs ⇝ PTuple qs ⊣ Δ
(** [T::c(ps)]; an open pattern [c(ps, ..)] may omit trailing fields *)
| SP_Constr p tq c sps op T ts td cd fs1 fs2 qs Δ :
    tq_ok tq T ->
    lookup_ty (se_hdr E) T = Some td ->
    lookup_ctor td c = Some cd ->
    map (tsubst (inst ts)) (cd_fields cd) = List.app fs1 fs2 ->
    ⊩ᶠ*[E] sps : fs1 ⇝ qs ⊣ Δ ->
    (op = false -> fs2 = []) ->
    ⊩ᵖ[E] SPConstr p tq c sps op : TData T ts ⇝ PConstr c (List.app qs (map (fun _ => PWild) fs2)) ⊣ Δ
(** on [Error], a constructor pattern names its error type *)
| SP_Up p tq c sps op T td cd fs1 fs2 qs Δ :
    err_owner E tq c T ->
    lookup_ty (se_hdr E) T = Some td ->
    lookup_ctor td c = Some cd ->
    map (tsubst (inst [])) (cd_fields cd) = List.app fs1 fs2 ->
    ⊩ᶠ*[E] sps : fs1 ⇝ qs ⊣ Δ ->
    (op = false -> fs2 = []) ->
    ⊩ᵖ[E] SPConstr p tq c sps op : TError
      ⇝ PUp T (PConstr c (List.app qs (map (fun _ => PWild) fs2))) ⊣ Δ
| SP_Record p fps op T ts names td cd given qs Δ :
    assoc T (se_sinfo E) = Some names ->
    lookup_ty (se_hdr E) T = Some td ->
    td_ctors td = [cd] ->
    ⊩ⁿ[E] fps : names ; map (tsubst (inst ts)) (cd_fields cd) ⇝ given ->
    assemble op given 0 (map (tsubst (inst ts)) (cd_fields cd)) = Some (qs, Δ) ->
    ⊩ᵖ[E] SPRecord p fps op : TData T ts ⇝ PConstr (cd_name cd) qs ⊣ Δ
| SP_Annot p sp t τ q Δ :
    ety E t = Ok τ ->
    ⊩ᵖ[E] sp : τ ⇝ q ⊣ Δ ->
    ⊩ᵖ[E] SPAnnot p sp t : τ ⇝ q ⊣ Δ

with fpat_ok (E : senv) : spat -> ty -> pat -> lctx -> Prop :=
| FP_Cell sp t q Δ :
    ⊩ᵖ[E] sp : t ⇝ q ⊣ Δ ->
    ⊩ᶠ[E] sp : TRef t ⇝ PRef q ⊣ Δ
| FP_Plain sp τ q Δ :
    is_cell τ = false ->
    ⊩ᵖ[E] sp : τ ⇝ q ⊣ Δ ->
    ⊩ᶠ[E] sp : τ ⇝ q ⊣ Δ

with fpats_ok (E : senv) : list spat -> list ty -> list pat -> lctx -> Prop :=
| FPs_nil :
    ⊩ᶠ*[E] [] : [] ⇝ [] ⊣ []
| FPs_cons sp sps τ τs q qs Δ1 Δ2 :
    ⊩ᶠ[E] sp : τ ⇝ q ⊣ Δ1 ->
    ⊩ᶠ*[E] sps : τs ⇝ qs ⊣ Δ2 ->
    ⊩ᶠ*[E] sp :: sps : τ :: τs ⇝ q :: qs ⊣ List.app Δ1 Δ2

with named_ok (E : senv) : list (ident * spat) -> list ident -> list ty -> list (nat * pat * lctx) -> Prop :=
| FN_nil names fs :
    ⊩ⁿ[E] [] : names ; fs ⇝ []
| FN_cons f sp fps names fs i τ q Δ given :
    index_of f names = Some i ->
    nth_error fs i = Some τ ->
    ⊩ᶠ[E] sp : τ ⇝ q ⊣ Δ ->
    ⊩ⁿ[E] fps : names ; fs ⇝ given ->
    ⊩ⁿ[E] (f, sp) :: fps : names ; fs ⇝ (i, q, Δ) :: given

where "⊩ᵖ[ E ] sp : τ ⇝ q ⊣ Δ" := (spat_ok E sp τ q Δ)
  and "⊩ᶠ[ E ] sp : τ ⇝ q ⊣ Δ" := (fpat_ok E sp τ q Δ)
  and "⊩ᶠ*[ E ] sps : τs ⇝ qs ⊣ Δ" := (fpats_ok E sps τs qs Δ)
  and "⊩ⁿ[ E ] fps : names ; fs ⇝ given" := (named_ok E fps names fs given).

Scheme spat_ok_mut := Minimality for spat_ok Sort Prop
  with fpat_ok_mut := Minimality for fpat_ok Sort Prop
  with fpats_ok_mut := Minimality for fpats_ok Sort Prop
  with named_ok_mut := Minimality for named_ok Sort Prop.
Combined Scheme spat_mutind from spat_ok_mut, fpat_ok_mut, fpats_ok_mut, named_ok_mut.

(** The patterns of [for p in src] (the element) or [for i, x in array]
    (index and element): Core pattern, bindings, scrutinee and its type. *)
Inductive fi_pat (E : senv) (it : iter_src) : list spat -> expr -> pat -> lctx -> expr -> ty -> Prop :=
| FIP_One sp elem q Δ :
    ⊩ᵖ[E] sp : fi_elem_ty it ⇝ q ⊣ Δ ->
    fi_pat E it [sp] elem q Δ elem (fi_elem_ty it)
| FIP_Two k t sp1 sp2 elem q1 q2 Δ1 Δ2 :
    it = IArray k t ->
    ⊩ᵖ[E] sp1 : TIndex ⇝ q1 ⊣ Δ1 ->
    ⊩ᵖ[E] sp2 : t ⇝ q2 ⊣ Δ2 ->
    fi_pat E it [sp1; sp2] elem (PTuple [q1; q2]) (List.app Δ1 Δ2) (ETuple [EVar 0; elem]) (TTuple [TIndex; t]).

(** ** Expressions *)

Reserved Notation "Γ ⊩[ E ; L ] s ⇒ τ ⇝ e"
  (at level 70, E at level 200, L at level 200, s at level 60, τ at level 60,
   e at level 60, no associativity, format "Γ  ⊩[ E ; L ]  s  ⇒  τ  ⇝  e").
Reserved Notation "Γ ⊩[ E ; L ] s ⇐ τ ⇝ e"
  (at level 70, E at level 200, L at level 200, s at level 60, τ at level 60,
   e at level 60, no associativity, format "Γ  ⊩[ E ; L ]  s  ⇐  τ  ⇝  e").
Reserved Notation "Γ ⊩[ E ; L ] s ⦂ a ⇒ τ ⇝ e"
  (at level 70, E at level 200, L at level 200, s at level 60, a at level 60,
   τ at level 60, e at level 60, no associativity,
   format "Γ  ⊩[ E ; L ]  s  ⦂  a  ⇒  τ  ⇝  e").
Reserved Notation "Γ ⊩*[ E ; L ] ss ⇒ τs ⇝ es"
  (at level 70, E at level 200, L at level 200, ss at level 60, τs at level 60,
   es at level 60, no associativity, format "Γ  ⊩*[ E ; L ]  ss  ⇒  τs  ⇝  es").
Reserved Notation "Γ ⊩ᵇ[ E ; L ] cs : τs ⇐ τ ⇝ bs"
  (at level 70, E at level 200, L at level 200, cs at level 60, τs at level 60,
   τ at level 60, bs at level 60, no associativity,
   format "Γ  ⊩ᵇ[ E ; L ]  cs  :  τs  ⇐  τ  ⇝  bs").
Reserved Notation "Γ ⊩ʳ[ E ; L ] fes : names ; fs ⇝ es ; ixs"
  (at level 70, E at level 200, L at level 200, fes at level 60, names at level 60,
   fs at level 60, es at level 60, ixs at level 60, no associativity,
   format "Γ  ⊩ʳ[ E ; L ]  fes  :  names ;  fs  ⇝  es ;  ixs").
Reserved Notation "Γ ⊩ⁱ[ E ; L ] inits ⇒ τs ⇝ es"
  (at level 70, E at level 200, L at level 200, inits at level 60, τs at level 60,
   es at level 60, no associativity, format "Γ  ⊩ⁱ[ E ; L ]  inits  ⇒  τs  ⇝  es").
Reserved Notation "Γ ⊩ᵘ[ E ; L ] upds : names ; τs ⇝ us"
  (at level 70, E at level 200, L at level 200, upds at level 60, names at level 60,
   τs at level 60, us at level 60, no associativity,
   format "Γ  ⊩ᵘ[ E ; L ]  upds  :  names ;  τs  ⇝  us").
Reserved Notation "Γ ⊩ˢ[ E ; L ] src ⇝ e1 ; e2 ; it"
  (at level 70, E at level 200, L at level 200, src at level 60, e1 at level 60,
   e2 at level 60, it at level 60, no associativity,
   format "Γ  ⊩ˢ[ E ; L ]  src  ⇝  e1 ;  e2 ;  it").
Reserved Notation "Γ ⊩ᵒ[ E ; L ] os ⇐ τ ⇝ oe"
  (at level 70, E at level 200, L at level 200, os at level 60, τ at level 60,
   oe at level 60, no associativity, format "Γ  ⊩ᵒ[ E ; L ]  os  ⇐  τ  ⇝  oe").
Reserved Notation "Γ ⊩*[ E ; L ] ss ⇐ τs ⇝ es"
  (at level 70, E at level 200, L at level 200, ss at level 60, τs at level 60,
   es at level 60, no associativity, format "Γ  ⊩*[ E ; L ]  ss  ⇐  τs  ⇝  es").

Inductive syn (E : senv) : cenv -> lctx -> sexpr -> ty -> expr -> Prop :=
(* variables *)
| S_Var L Γ p x i τ :
    lookup_local x Γ = Some i ->
    nth_error (ctx_of Γ) i = Some τ ->
    is_cell τ = false ->
    Γ ⊩[E;L] SVar p x ⇒ τ ⇝ EVar i
(** a [let mut] variable is read from its cell *)
| S_VarMut L Γ p x i τ :
    lookup_local x Γ = Some i ->
    nth_error (ctx_of Γ) i = Some (TRef τ) ->
    Γ ⊩[E;L] SVar p x ⇒ τ ⇝ EMem (MGet τ) [EVar i]
(** a global function used as a value, at some type arguments [ts] *)
| S_Global L Γ p x fd ts :
    lookup_local x Γ = None ->
    lookup_fn (se_hdr E) x = Some fd ->
    sbounds E x = [] ->
    List.length ts = fd_tparams fd ->
    Γ ⊩[E;L] SVar p x ⇒ fn_inst fd ts ⇝ EGlobal x ts
(* literals and operators *)
| S_Lit L Γ p l l' :
    lit_of l = Some l' ->
    Γ ⊩[E;L] SLit p l ⇒ TBase (lit_ty l') ⇝ ELit l'
(** [-1] is a literal *)
| S_NegLit L Γ p q k z τ e :
    Γ ⊩[E;L] SLit q (SLInt k (Z.opp z)) ⇒ τ ⇝ e ->
    Γ ⊩[E;L] SUnary p "-" (SLit q (SLInt k z)) ⇒ τ ⇝ e
| S_Neg L Γ p a k a' :
    int_lit a = false ->
    Γ ⊩[E;L] a ⇒ TInt k ⇝ a' ->
    Γ ⊩[E;L] SUnary p "-" a ⇒ TInt k ⇝ EPrim (PIntNeg k) [a']
| S_Not L Γ p a a' :
    Γ ⊩[E;L] a ⇐ TBool ⇝ a' ->
    Γ ⊩[E;L] SUnary p "!" a ⇒ TBool ⇝ EPrim PBoolNot [a']
| S_And L Γ p a b a' b' :
    Γ ⊩[E;L] a ⇐ TBool ⇝ a' ->
    Γ ⊩[E;L] b ⇐ TBool ⇝ b' ->
    Γ ⊩[E;L] SInfix p "&&" a b ⇒ TBool ⇝ EIf a' b' e_false
| S_Or L Γ p a b a' b' :
    Γ ⊩[E;L] a ⇐ TBool ⇝ a' ->
    Γ ⊩[E;L] b ⇐ TBool ⇝ b' ->
    Γ ⊩[E;L] SInfix p "||" a b ⇒ TBool ⇝ EIf a' e_true b'
(** the left operand decides the operator... *)
| S_BinL L Γ p op a b τ a' b' e :
    (flexible a && negb (flexible b))%bool = false ->
    Γ ⊩[E;L] a ⇒ τ ⇝ a' ->
    Γ ⊩[E;L] b ⇐ τ ⇝ b' ->
    elab_binop p op τ a' b' = Ok e ->
    Γ ⊩[E;L] SInfix p op a b ⇒ binop_res op τ ⇝ e
(** ... unless it is an unsuffixed integer literal and the right one is not *)
| S_BinR L Γ p op a b τ a' b' e :
    flexible a = true ->
    flexible b = false ->
    Γ ⊩[E;L] b ⇒ τ ⇝ b' ->
    Γ ⊩[E;L] a ⇐ τ ⇝ a' ->
    elab_binop p op τ a' b' = Ok e ->
    Γ ⊩[E;L] SInfix p op a b ⇒ binop_res op τ ⇝ e
(* binding and control *)
| S_Let L Γ p x a s1 s2 τ1 τ e1 e2 :
    Γ ⊩[E;L] s1 ⦂ a ⇒ τ1 ⇝ e1 ->
    (x, τ1) :: Γ ⊩[E;L] s2 ⇒ τ ⇝ e2 ->
    Γ ⊩[E;L] SLet p x a s1 s2 ⇒ τ ⇝ ELet e1 e2
| S_Annot L Γ p s t τ e :
    ety E t = Ok τ ->
    Γ ⊩[E;L] s ⇐ τ ⇝ e ->
    Γ ⊩[E;L] SAnnot p s t ⇒ τ ⇝ e
(** the type of an [if] comes from its [then] branch... *)
| S_If L Γ p c t f τ c' t' f' :
    (diverges t && negb (diverges f))%bool = false ->
    Γ ⊩[E;L] c ⇐ TBool ⇝ c' ->
    Γ ⊩[E;L] t ⇒ τ ⇝ t' ->
    Γ ⊩[E;L] f ⇐ τ ⇝ f' ->
    Γ ⊩[E;L] SIf p c t (Some f) ⇒ τ ⇝ EIf c' t' f'
(** ... unless that branch certainly jumps away and the other does not *)
| S_IfR L Γ p c t f τ c' t' f' :
    diverges t = true ->
    diverges f = false ->
    Γ ⊩[E;L] c ⇐ TBool ⇝ c' ->
    Γ ⊩[E;L] f ⇒ τ ⇝ f' ->
    Γ ⊩[E;L] t ⇐ τ ⇝ t' ->
    Γ ⊩[E;L] SIf p c t (Some f) ⇒ τ ⇝ EIf c' t' f'
| S_If1 L Γ p c t c' t' :
    Γ ⊩[E;L] c ⇐ TBool ⇝ c' ->
    Γ ⊩[E;L] t ⇐ TUnit ⇝ t' ->
    Γ ⊩[E;L] SIf p c t None ⇒ TUnit ⇝ EIf c' t' (ELit LUnit)
(* tuples *)
| S_Tuple L Γ p ss τs es :
    Γ ⊩*[E;L] ss ⇒ τs ⇝ es ->
    Γ ⊩[E;L] STup p ss ⇒ TTuple τs ⇝ ETuple es
| S_Proj L Γ p s i τs τ e :
    Γ ⊩[E;L] s ⇒ TTuple τs ⇝ e ->
    nth_error τs i = Some τ ->
    Γ ⊩[E;L] SProj p s i ⇒ τ ⇝ EProj e i
(* functions *)
(** a lambda with annotated parameters and result: the body is a block,
    the target of [return] *)
| S_LamRet L Γ p ps t a body τs r ε b :
    params_syn E ps τs ->
    ety E t = Ok r ->
    eff_syn E a ε ->
    List.app (lam_ctx ps τs) Γ ⊩[E;fun_env r ε] body ⇐ r ⇝ b ->
    Γ ⊩[E;L] SLam p ps (Some t) a body ⇒ TArrow τs r ε ⇝ ELam τs r ε (eblock r b)
(** without a result annotation, the result type is synthesized (and
    [return] is not available) *)
| S_Lam L Γ p ps a body τs r ε b :
    params_syn E ps τs ->
    eff_syn E a ε ->
    List.app (lam_ctx ps τs) Γ ⊩[E;mk_cenv [] ε] body ⇒ r ⇝ b ->
    Γ ⊩[E;L] SLam p ps None a body ⇒ TArrow τs r ε ⇝ ELam τs r ε b
(** a call of a global function at type arguments [ts] *)
| S_Call L Γ p q g args fd ts es :
    lookup_local g Γ = None ->
    lookup_fn (se_hdr E) g = Some fd ->
    sbounds E g = [] ->
    List.length ts = fd_tparams fd ->
    Γ ⊩*[E;L] args ⇐ map (tsubst (inst ts)) (fd_params fd) ⇝ es ->
    call_ok E L (tsubst (inst ts) (fd_eff fd)) ->
    Γ ⊩[E;L] SApp p (SVar q g) args ⇒ tsubst (inst ts) (fd_ret fd)
      ⇝ wrap_call L (tsubst (inst ts) (fd_eff fd)) (tsubst (inst ts) (fd_ret fd))
                  (EGlobal g ts) es
(** a call of any other function value *)
| S_CallExpr L Γ p f args ps r ε f' es :
    callee Γ f ->
    Γ ⊩[E;L] f ⇒ TArrow ps r ε ⇝ f' ->
    Γ ⊩*[E;L] args ⇐ ps ⇝ es ->
    call_ok E L ε ->
    Γ ⊩[E;L] SApp p f args ⇒ r ⇝ wrap_call L ε r f' es
(* builtins *)
| S_BNot L Γ p q a a' :
    builtin E Γ "not" ->
    Γ ⊩[E;L] a ⇐ TBool ⇝ a' ->
    Γ ⊩[E;L] SApp p (SVar q "not") [a] ⇒ TBool ⇝ EPrim PBoolNot [a']
| S_Ignore L Γ p q a τ a' :
    builtin E Γ "ignore" ->
    Γ ⊩[E;L] a ⇒ τ ⇝ a' ->
    Γ ⊩[E;L] SApp p (SVar q "ignore") [a] ⇒ TUnit ⇝ ELet a' (ELit LUnit)
(** [panic()] and [abort(msg)] stop the program; on their own they are
    [Unit] *)
| S_Panic L Γ p q :
    builtin E Γ "panic" ->
    Γ ⊩[E;L] SApp p (SVar q "panic") [] ⇒ TUnit ⇝ EAbort TUnit
| S_Abort L Γ p q a a' :
    builtin E Γ "abort" ->
    Γ ⊩[E;L] a ⇐ TString ⇝ a' ->
    Γ ⊩[E;L] SApp p (SVar q "abort") [a] ⇒ TUnit ⇝ ELet a' (EAbort TUnit)
(* data types (milestone M2) *)
(** a constructor, at some type arguments [ts] *)
| S_Ctor L Γ p q tq c args T td cd ts es :
    ctor_pick E tq c T ->
    lookup_ty (se_hdr E) T = Some td ->
    lookup_ctor td c = Some cd ->
    List.length ts = td_tparams td ->
    Γ ⊩*[E;L] args ⇐ map (tsubst (inst ts)) (cd_fields cd) ⇝ es ->
    Γ ⊩[E;L] SApp p (SConstr q tq c) args ⇒ TData T ts ⇝ EConstr T c ts (ETuple es)
| S_Ctor0 L Γ p tq c T td cd ts :
    ctor_pick E tq c T ->
    lookup_ty (se_hdr E) T = Some td ->
    lookup_ctor td c = Some cd ->
    List.length ts = td_tparams td ->
    cd_fields cd = [] ->
    Γ ⊩[E;L] SConstr p tq c ⇒ TData T ts ⇝ EConstr T c ts (ETuple [])
| S_Field L Γ p s f T ts e names i e' τ :
    Γ ⊩[E;L] s ⇒ TData T ts ⇝ e ->
    assoc T (se_sinfo E) = Some names ->
    index_of f names = Some i ->
    field_proj E T ts i e = Some (e', τ) ->
    Γ ⊩[E;L] SField p s f ⇒ τ ⇝ e'
(** [e.0] on a tuple struct *)
| S_ProjData L Γ p s i T ts e e' τ :
    Γ ⊩[E;L] s ⇒ TData T ts ⇝ e ->
    field_proj E T ts i e = Some (e', τ) ->
    Γ ⊩[E;L] SProj p s i ⇒ τ ⇝ e'
(** a record [T::{ fields }] *)
| S_Record L Γ p tq fes T ts names td cd es ixs vs :
    rec_pick E tq (map fst fes) T ->
    assoc T (se_sinfo E) = Some names ->
    lookup_ty (se_hdr E) T = Some td ->
    td_ctors td = [cd] ->
    List.length ts = td_tparams td ->
    List.length (cd_fields cd) = List.length names ->
    Γ ⊩ʳ[E;L] fes : names ; map (tsubst (inst ts)) (cd_fields cd) ⇝ es ; ixs ->
    rec_vars ixs (List.length names) = Some vs ->
    Γ ⊩[E;L] SRecord p tq fes ⇒ TData T ts ⇝ ELet (ETuple es) (EConstr T (cd_name cd) ts (ETuple vs))
(* state (milestone M3) *)
(** [let mut x = e]: [x] names a new cell *)
| S_LetMut L Γ p x a s1 s2 τ1 τ e1 e2 :
    Γ ⊩[E;L] s1 ⦂ a ⇒ τ1 ⇝ e1 ->
    (Some x, TRef τ1) :: Γ ⊩[E;L] s2 ⇒ τ ⇝ e2 ->
    Γ ⊩[E;L] SLetMut p x a s1 s2 ⇒ τ ⇝ ELet (EMem (MRef τ1) [e1]) e2
| S_Assign L Γ p x op s i τ v e :
    lookup_local x Γ = Some i ->
    nth_error (ctx_of Γ) i = Some (TRef τ) ->
    Γ ⊩[E;L] s ⇐ τ ⇝ v ->
    upd_rhs p op τ (EMem (MGet τ) [EVar i]) v e ->
    Γ ⊩[E;L] SAssign p x op s ⇒ TUnit ⇝ EMem (MSet τ) [EVar i; e]
(** an array literal takes the type of its first element *)
| S_Array L Γ p s ss t e es :
    Γ ⊩[E;L] s ⇒ t ⇝ e ->
    Γ ⊩*[E;L] ss ⇐ repeat t (List.length ss) ⇝ es ->
    Γ ⊩[E;L] SArray p (s :: ss) ⇒ TArray AGrow t ⇝ EMem (MArray AGrow t (S (List.length ss))) (e :: es)
| S_Index L Γ p a i k t a' i' :
    Γ ⊩[E;L] a ⇒ TArray k t ⇝ a' ->
    Γ ⊩[E;L] i ⇐ TIndex ⇝ i' ->
    Γ ⊩[E;L] SIndex p a i ⇒ t ⇝ EMem (MIndex k t) [a'; i']
| S_IndexSet L Γ p a i v k t a' i' v' :
    Γ ⊩[E;L] a ⇒ TArray k t ⇝ a' ->
    Γ ⊩[E;L] i ⇐ TIndex ⇝ i' ->
    Γ ⊩[E;L] v ⇐ t ⇝ v' ->
    Γ ⊩[E;L] SIndexSet p a i None v ⇒ TUnit ⇝ EMem (MSetIndex k t) [a'; i'; v']
(** [a[i] op= v] evaluates [a] and [i] once *)
| S_IndexUpd L Γ p a i o v k t a' i' v' rhs :
    Γ ⊩[E;L] a ⇒ TArray k t ⇝ a' ->
    (None, TArray k t) :: Γ ⊩[E;L] i ⇐ TIndex ⇝ i' ->
    (None, TIndex) :: (None, TArray k t) :: Γ ⊩[E;L] v ⇐ t ⇝ v' ->
    binop_res o t = t ->
    elab_binop p o t (EMem (MIndex k t) [EVar 1; EVar 0]) v' = Ok rhs ->
    Γ ⊩[E;L] SIndexSet p a i (Some o) v ⇒ TUnit
      ⇝ ELet a' (ELet i' (EMem (MSetIndex k t) [EVar 1; EVar 0; rhs]))
(** [e.f = v] on a [mut] field: bind the field's cell, then write it *)
| S_FieldSet L Γ p s f op v T ts e names i c n t v' rhs :
    Γ ⊩[E;L] s ⇒ TData T ts ⇝ e ->
    assoc T (se_sinfo E) = Some names ->
    index_of f names = Some i ->
    field_cell E T ts i = Some (c, n, t) ->
    (None, TRef t) :: Γ ⊩[E;L] v ⇐ t ⇝ v' ->
    upd_rhs p op t (EMem (MGet t) [EVar 0]) v' rhs ->
    Γ ⊩[E;L] SFieldSet p s f op v ⇒ TUnit
      ⇝ EMatch e TUnit [(PConstr c (proj_pats i PVar 0 n), EMem (MSet t) [EVar 0; rhs])]
| S_Length L Γ p s k t e :
    Γ ⊩[E;L] s ⇒ TArray k t ⇝ e ->
    Γ ⊩[E;L] SMethod p s "length" [] ⇒ TIndex ⇝ EMem (MLength k t) [e]
| S_Push L Γ p s a t e a' :
    Γ ⊩[E;L] s ⇒ TArray AGrow t ⇝ e ->
    Γ ⊩[E;L] a ⇐ t ⇝ a' ->
    Γ ⊩[E;L] SMethod p s "push" [a] ⇒ TUnit ⇝ EMem (MPush t) [e; a']
| S_RefNew L Γ p q v t v' :
    ref_ok E ->
    Γ ⊩[E;L] v ⇒ t ⇝ v' ->
    Γ ⊩[E;L] SApp p (SQual q "Ref" "new") [v] ⇒ TData "Ref" [t]
      ⇝ EConstr "Ref" "Ref" [t] (ETuple [EMem (MRef t) [v']])
| S_Make L Γ p q T n v k t n' v' :
    array_kind_of T = Some k ->
    Γ ⊩[E;L] n ⇐ TIndex ⇝ n' ->
    Γ ⊩[E;L] v ⇒ t ⇝ v' ->
    Γ ⊩[E;L] SApp p (SQual q T "make") [n; v] ⇒ TArray k t ⇝ EMem (MMake k t) [n'; v']
(* loops and jumps (milestone M3) *)
(** a loop's type: [Unit], or that of its [nobreak] clause *)
| S_While L Γ p x c body c' b' :
    Γ ⊩[E;hd_env [] TUnit L] c ⇐ TBool ⇝ c' ->
    Γ ⊩[E;push_lab (mk_lab x LKWhile [] TUnit) L] body ⇐ TUnit ⇝ b' ->
    Γ ⊩[E;L] SWhile p x c body None ⇒ TUnit ⇝ while_loop TUnit c' b' (ELit LUnit)
| S_WhileNb L Γ p x c body nb τ nb0 c' b' nb' :
    Γ ⊩[E;hd_env [] TUnit L] nb ⇒ τ ⇝ nb0 ->
    Γ ⊩[E;hd_env [] τ L] c ⇐ TBool ⇝ c' ->
    Γ ⊩[E;push_lab (mk_lab x LKWhile [] τ) L] body ⇐ TUnit ⇝ b' ->
    Γ ⊩[E;hd_env [] τ L] nb ⇐ τ ⇝ nb' ->
    Γ ⊩[E;L] SWhile p x c body (Some nb) ⇒ τ ⇝ while_loop τ c' b' nb'
| S_For L Γ p x inits c upds body τs es c' b' us :
    Γ ⊩ⁱ[E;L] inits ⇒ τs ⇝ es ->
    List.app (names_ctx (map fst inits) τs) Γ ⊩ᵒ[E;hd_env τs TUnit L] c ⇐ TBool ⇝ c' ->
    List.app (names_ctx (map fst inits) τs) Γ
      ⊩[E;push_lab (mk_lab x LKForBody [] TUnit) (hd_env τs TUnit L)] body ⇐ TUnit ⇝ b' ->
    (None, TUnit) :: List.app (names_ctx (map fst inits) τs) Γ
      ⊩ᵘ[E;hd_env τs TUnit L] upds : map fst inits ; τs ⇝ us ->
    Γ ⊩[E;L] SFor p x inits c upds body None ⇒ TUnit
      ⇝ for_loop es τs TUnit c' b' (map fst inits) us (ELit LUnit)
| S_ForNb L Γ p x inits c upds body nb τs es τ nb0 c' b' us nb' :
    Γ ⊩ⁱ[E;L] inits ⇒ τs ⇝ es ->
    List.app (names_ctx (map fst inits) τs) Γ ⊩[E;hd_env τs TUnit L] nb ⇒ τ ⇝ nb0 ->
    List.app (names_ctx (map fst inits) τs) Γ ⊩ᵒ[E;hd_env τs τ L] c ⇐ TBool ⇝ c' ->
    List.app (names_ctx (map fst inits) τs) Γ
      ⊩[E;push_lab (mk_lab x LKForBody [] TUnit) (hd_env τs τ L)] body ⇐ TUnit ⇝ b' ->
    (None, TUnit) :: List.app (names_ctx (map fst inits) τs) Γ
      ⊩ᵘ[E;hd_env τs τ L] upds : map fst inits ; τs ⇝ us ->
    List.app (names_ctx (map fst inits) τs) Γ ⊩[E;hd_env τs τ L] nb ⇐ τ ⇝ nb' ->
    Γ ⊩[E;L] SFor p x inits c upds body (Some nb) ⇒ τ
      ⇝ for_loop es τs τ c' b' (map fst inits) us nb'
| S_ForIn L Γ p x pats src inits upds body e1 e2 it τs es q Δ scrut sty b' us :
    Γ ⊩ˢ[E;L] src ⇝ e1 ; e2 ; it ->
    fo_ctx it Γ ⊩ⁱ[E;L] inits ⇒ τs ⇝ es ->
    fi_pat E it pats (fi_elem it (fi_n it τs)) q Δ scrut sty ->
    List.app Δ (fl_ctx it (map fst inits) τs Γ) ⊩[E;fi_body_env x it τs TUnit L] body ⇐ TUnit ⇝ b' ->
    (None, TUnit) :: List.app Δ (fl_ctx it (map fst inits) τs Γ)
      ⊩ᵘ[E;fi_state_env it τs TUnit L] upds : map fst inits ; τs ⇝ us ->
    Γ ⊩[E;L] SForIn p x pats src inits upds body None ⇒ TUnit
      ⇝ forin_loop it e1 e2 es τs TUnit q scrut (List.length Δ) b' (map fst inits) us (ELit LUnit)
| S_ForInNb L Γ p x pats src inits upds body nb e1 e2 it τs es τ nb0 q Δ scrut sty b' us nb' :
    Γ ⊩ˢ[E;L] src ⇝ e1 ; e2 ; it ->
    fo_ctx it Γ ⊩ⁱ[E;L] inits ⇒ τs ⇝ es ->
    fl_ctx it (map fst inits) τs Γ ⊩[E;fi_loop_env it τs TUnit L] nb ⇒ τ ⇝ nb0 ->
    fi_pat E it pats (fi_elem it (fi_n it τs)) q Δ scrut sty ->
    List.app Δ (fl_ctx it (map fst inits) τs Γ) ⊩[E;fi_body_env x it τs τ L] body ⇐ TUnit ⇝ b' ->
    (None, TUnit) :: List.app Δ (fl_ctx it (map fst inits) τs Γ)
      ⊩ᵘ[E;fi_state_env it τs τ L] upds : map fst inits ; τs ⇝ us ->
    fl_ctx it (map fst inits) τs Γ ⊩[E;fi_loop_env it τs τ L] nb ⇐ τ ⇝ nb' ->
    Γ ⊩[E;L] SForIn p x pats src inits upds body (Some nb) ⇒ τ
      ⇝ forin_loop it e1 e2 es τs τ q scrut (List.length Δ) b' (map fst inits) us nb'
| S_Block L Γ p x body b :
    Γ ⊩[E;push_lab (mk_lab (Some x) LKBlock [] TUnit) L] body ⇐ TUnit ⇝ b ->
    Γ ⊩[E;L] SBlock p x body ⇒ TUnit ⇝ eblock TUnit b
(** on their own, jumps are [Unit] *)
| S_Jump L Γ s e :
    is_jump s = true ->
    Γ ⊩[E;L] s ⇐ TUnit ⇝ e ->
    Γ ⊩[E;L] s ⇒ TUnit ⇝ e
(** the type of a [match] is that of the arm chosen by [pick_arm] *)
| S_Match L Γ p s cases τs τ e bs sp b q Δ b' :
    Γ ⊩[E;L] s ⇒ τs ⇝ e ->
    pick_arm cases = Some (sp, b) ->
    ⊩ᵖ[E] sp : τs ⇝ q ⊣ Δ ->
    List.app Δ Γ ⊩[E;L] b ⇒ τ ⇝ b' ->
    Γ ⊩ᵇ[E;L] cases : τs ⇐ τ ⇝ bs ->
    Γ ⊩[E;L] SMatch p s cases ⇒ τ ⇝ EMatch e τ bs

with chk (E : senv) : cenv -> lctx -> sexpr -> ty -> expr -> Prop :=
(** subsumption: synthesize, then convert *)
| C_Sub L Γ s τ' τ e e' :
    Γ ⊩[E;L] s ⇒ τ' ⇝ e ->
    ⊩ᶜ[E] e : τ' ≼ τ ⇝ e' ->
    Γ ⊩[E;L] s ⇐ τ ⇝ e'
(** an unsuffixed integer literal takes the expected integer type *)
| C_Lit L Γ p z k :
    int_in_range k z = true ->
    Γ ⊩[E;L] SLit p (SLInt None z) ⇐ TInt k ⇝ ELit (LInt k z)
| C_NegLit L Γ p q k z τ e :
    Γ ⊩[E;L] SLit q (SLInt k (Z.opp z)) ⇐ τ ⇝ e ->
    Γ ⊩[E;L] SUnary p "-" (SLit q (SLInt k z)) ⇐ τ ⇝ e
(** arithmetic: the expected type flows into both operands *)
| C_Bin L Γ p op a b τ a' b' e :
    binop_res op τ = τ ->
    Γ ⊩[E;L] a ⇐ τ ⇝ a' ->
    Γ ⊩[E;L] b ⇐ τ ⇝ b' ->
    elab_binop p op τ a' b' = Ok e ->
    Γ ⊩[E;L] SInfix p op a b ⇐ τ ⇝ e
| C_Let L Γ p x a s1 s2 τ1 τ e1 e2 :
    Γ ⊩[E;L] s1 ⦂ a ⇒ τ1 ⇝ e1 ->
    (x, τ1) :: Γ ⊩[E;L] s2 ⇐ τ ⇝ e2 ->
    Γ ⊩[E;L] SLet p x a s1 s2 ⇐ τ ⇝ ELet e1 e2
| C_If L Γ p c t f τ c' t' f' :
    Γ ⊩[E;L] c ⇐ TBool ⇝ c' ->
    Γ ⊩[E;L] t ⇐ τ ⇝ t' ->
    Γ ⊩[E;L] f ⇐ τ ⇝ f' ->
    Γ ⊩[E;L] SIf p c t (Some f) ⇐ τ ⇝ EIf c' t' f'
| C_Tuple L Γ p ss τs es :
    Γ ⊩*[E;L] ss ⇐ τs ⇝ es ->
    Γ ⊩[E;L] STup p ss ⇐ TTuple τs ⇝ ETuple es
(** a lambda against a function type: unannotated parameters, result and
    effect come from the expected type *)
| C_Lam L Γ p ps ret a body τs r ε b :
    params_ann E ps τs ->
    ann_ok E ret r ->
    eff_ann E a ε ->
    List.app (lam_ctx ps τs) Γ ⊩[E;fun_env r ε] body ⇐ r ⇝ b ->
    Γ ⊩[E;L] SLam p ps ret a body ⇐ TArrow τs r ε ⇝ ELam τs r ε (eblock r b)
(** the same, when the body's type is synthesized ([return] is not
    available) *)
| C_LamSyn L Γ p ps a body τs r ε b :
    params_ann E ps τs ->
    eff_ann E a ε ->
    List.app (lam_ctx ps τs) Γ ⊩[E;mk_cenv [] ε] body ⇒ r ⇝ b ->
    Γ ⊩[E;L] SLam p ps None a body ⇐ TArrow τs r ε ⇝ ELam τs r ε b
| C_Panic L Γ p q τ :
    builtin E Γ "panic" ->
    Γ ⊩[E;L] SApp p (SVar q "panic") [] ⇐ τ ⇝ EAbort τ
| C_Abort L Γ p q a a' τ :
    builtin E Γ "abort" ->
    Γ ⊩[E;L] a ⇐ TString ⇝ a' ->
    Γ ⊩[E;L] SApp p (SVar q "abort") [a] ⇐ τ ⇝ ELet a' (EAbort τ)
(** a constructor of the expected data type takes its type arguments *)
| C_Ctor L Γ p q tq c args T ts td cd es :
    tq_ok tq T ->
    lookup_ty (se_hdr E) T = Some td ->
    lookup_ctor td c = Some cd ->
    List.length ts = td_tparams td ->
    Γ ⊩*[E;L] args ⇐ map (tsubst (inst ts)) (cd_fields cd) ⇝ es ->
    Γ ⊩[E;L] SApp p (SConstr q tq c) args ⇐ TData T ts ⇝ EConstr T c ts (ETuple es)
| C_Ctor0 L Γ p tq c T ts td cd :
    tq_ok tq T ->
    lookup_ty (se_hdr E) T = Some td ->
    lookup_ctor td c = Some cd ->
    List.length ts = td_tparams td ->
    cd_fields cd = [] ->
    Γ ⊩[E;L] SConstr p tq c ⇐ TData T ts ⇝ EConstr T c ts (ETuple [])
| C_Record L Γ p tq fes T ts names td cd es ixs vs :
    tq_ok tq T ->
    assoc T (se_sinfo E) = Some names ->
    lookup_ty (se_hdr E) T = Some td ->
    td_ctors td = [cd] ->
    List.length ts = td_tparams td ->
    List.length (cd_fields cd) = List.length names ->
    Γ ⊩ʳ[E;L] fes : names ; map (tsubst (inst ts)) (cd_fields cd) ⇝ es ; ixs ->
    rec_vars ixs (List.length names) = Some vs ->
    Γ ⊩[E;L] SRecord p tq fes ⇐ TData T ts ⇝ ELet (ETuple es) (EConstr T (cd_name cd) ts (ETuple vs))
| C_LetMut L Γ p x a s1 s2 τ1 τ e1 e2 :
    Γ ⊩[E;L] s1 ⦂ a ⇒ τ1 ⇝ e1 ->
    (Some x, TRef τ1) :: Γ ⊩[E;L] s2 ⇐ τ ⇝ e2 ->
    Γ ⊩[E;L] SLetMut p x a s1 s2 ⇐ τ ⇝ ELet (EMem (MRef τ1) [e1]) e2
| C_Array L Γ p ss k t es :
    Γ ⊩*[E;L] ss ⇐ repeat t (List.length ss) ⇝ es ->
    Γ ⊩[E;L] SArray p ss ⇐ TArray k t ⇝ EMem (MArray k t (List.length ss)) es
| C_RefNew L Γ p q v t v' :
    ref_ok E ->
    Γ ⊩[E;L] v ⇐ t ⇝ v' ->
    Γ ⊩[E;L] SApp p (SQual q "Ref" "new") [v] ⇐ TData "Ref" [t]
      ⇝ EConstr "Ref" "Ref" [t] (ETuple [EMem (MRef t) [v']])
| C_Make L Γ p q T n v k t n' v' :
    array_kind_of T = Some k ->
    Γ ⊩[E;L] n ⇐ TIndex ⇝ n' ->
    Γ ⊩[E;L] v ⇐ t ⇝ v' ->
    Γ ⊩[E;L] SApp p (SQual q T "make") [n; v] ⇐ TArray k t ⇝ EMem (MMake k t) [n'; v']
| C_ArrNew L Γ p q T k t :
    array_kind_of T = Some k ->
    Γ ⊩[E;L] SApp p (SQual q T "new") [] ⇐ TArray k t ⇝ EMem (MArray k t 0) []
| C_WhileNb L Γ p x c body nb τ c' b' nb' :
    Γ ⊩[E;hd_env [] τ L] c ⇐ TBool ⇝ c' ->
    Γ ⊩[E;push_lab (mk_lab x LKWhile [] τ) L] body ⇐ TUnit ⇝ b' ->
    Γ ⊩[E;hd_env [] τ L] nb ⇐ τ ⇝ nb' ->
    Γ ⊩[E;L] SWhile p x c body (Some nb) ⇐ τ ⇝ while_loop τ c' b' nb'
| C_ForNb L Γ p x inits c upds body nb τs es τ c' b' us nb' :
    Γ ⊩ⁱ[E;L] inits ⇒ τs ⇝ es ->
    List.app (names_ctx (map fst inits) τs) Γ ⊩ᵒ[E;hd_env τs τ L] c ⇐ TBool ⇝ c' ->
    List.app (names_ctx (map fst inits) τs) Γ
      ⊩[E;push_lab (mk_lab x LKForBody [] TUnit) (hd_env τs τ L)] body ⇐ TUnit ⇝ b' ->
    (None, TUnit) :: List.app (names_ctx (map fst inits) τs) Γ
      ⊩ᵘ[E;hd_env τs τ L] upds : map fst inits ; τs ⇝ us ->
    List.app (names_ctx (map fst inits) τs) Γ ⊩[E;hd_env τs τ L] nb ⇐ τ ⇝ nb' ->
    Γ ⊩[E;L] SFor p x inits c upds body (Some nb) ⇐ τ
      ⇝ for_loop es τs τ c' b' (map fst inits) us nb'
(** a [for] loop without condition nor [nobreak] only stops by jumping *)
| C_ForInf L Γ p x inits upds body τs es τ b' us :
    Γ ⊩ⁱ[E;L] inits ⇒ τs ⇝ es ->
    List.app (names_ctx (map fst inits) τs) Γ
      ⊩[E;push_lab (mk_lab x LKForBody [] TUnit) (hd_env τs τ L)] body ⇐ TUnit ⇝ b' ->
    (None, TUnit) :: List.app (names_ctx (map fst inits) τs) Γ
      ⊩ᵘ[E;hd_env τs τ L] upds : map fst inits ; τs ⇝ us ->
    Γ ⊩[E;L] SFor p x inits None upds body None ⇐ τ
      ⇝ for_loop es τs τ None b' (map fst inits) us (ELit LUnit)
| C_ForInNb L Γ p x pats src inits upds body nb e1 e2 it τs es τ q Δ scrut sty b' us nb' :
    Γ ⊩ˢ[E;L] src ⇝ e1 ; e2 ; it ->
    fo_ctx it Γ ⊩ⁱ[E;L] inits ⇒ τs ⇝ es ->
    fi_pat E it pats (fi_elem it (fi_n it τs)) q Δ scrut sty ->
    List.app Δ (fl_ctx it (map fst inits) τs Γ) ⊩[E;fi_body_env x it τs τ L] body ⇐ TUnit ⇝ b' ->
    (None, TUnit) :: List.app Δ (fl_ctx it (map fst inits) τs Γ)
      ⊩ᵘ[E;fi_state_env it τs τ L] upds : map fst inits ; τs ⇝ us ->
    fl_ctx it (map fst inits) τs Γ ⊩[E;fi_loop_env it τs τ L] nb ⇐ τ ⇝ nb' ->
    Γ ⊩[E;L] SForIn p x pats src inits upds body (Some nb) ⇐ τ
      ⇝ forin_loop it e1 e2 es τs τ q scrut (List.length Δ) b' (map fst inits) us nb'
| C_Block L Γ p x body τ b :
    Γ ⊩[E;push_lab (mk_lab (Some x) LKBlock [] τ) L] body ⇐ τ ⇝ b ->
    Γ ⊩[E;L] SBlock p x body ⇐ τ ⇝ eblock τ b
(** [break], [continue], [return]: the target is found by name, and is an
    enclosing loop of the given type *)
| C_Break L Γ p x a τ k ps τt a' :
    break_target x (ce_labs L) 0 = Some (k, τt) ->
    nth_error (core_labels (ce_labs L)) k = Some (ps, τt) ->
    Γ ⊩[E;L] a ⇐ τt ⇝ a' ->
    Γ ⊩[E;L] SBreak p x (Some a) ⇐ τ ⇝ EJump CBreak k a' τ
| C_Break0 L Γ p x τ k ps :
    break_target x (ce_labs L) 0 = Some (k, TUnit) ->
    nth_error (core_labels (ce_labs L)) k = Some (ps, TUnit) ->
    Γ ⊩[E;L] SBreak p x None ⇐ τ ⇝ EJump CBreak k (ELit LUnit) τ
| C_ContWhile L Γ p x τ k r :
    cont_target_of x (ce_labs L) 0 = Some (CTWhile k) ->
    nth_error (core_labels (ce_labs L)) k = Some ([], r) ->
    Γ ⊩[E;L] SContinue p x [] ⇐ τ ⇝ EJump CCont k (ETuple []) τ
(** [continue] in a [for] body leaves the body (the updates then apply)... *)
| C_ContFor0 L Γ p x τ k ps pk :
    cont_target_of x (ce_labs L) 0 = Some (CTFor k ps) ->
    nth_error (core_labels (ce_labs L)) k = Some (pk, TUnit) ->
    Γ ⊩[E;L] SContinue p x [] ⇐ τ ⇝ EJump CBreak k (ELit LUnit) τ
(** ... or gives the next values directly *)
| C_ContFor L Γ p x args τ k ps r es :
    cont_target_of x (ce_labs L) 0 = Some (CTFor k ps) ->
    args <> [] ->
    nth_error (core_labels (ce_labs L)) (S k) = Some (ps, r) ->
    Γ ⊩*[E;L] args ⇐ ps ⇝ es ->
    Γ ⊩[E;L] SContinue p x args ⇐ τ ⇝ EJump CCont (S k) (ETuple es) τ
| C_ContForIn0 L Γ p x τ k ss pk :
    cont_target_of x (ce_labs L) 0 = Some (CTForIn k ss) ->
    nth_error (core_labels (ce_labs L)) k = Some (pk, TUnit) ->
    Γ ⊩[E;L] SContinue p x [] ⇐ τ ⇝ EJump CBreak k (ELit LUnit) τ
| C_ContForIn L Γ p x args τ k ss pk es :
    cont_target_of x (ce_labs L) 0 = Some (CTForIn k ss) ->
    args <> [] ->
    nth_error (core_labels (ce_labs L)) (S k) = Some (pk, TTuple ss) ->
    Γ ⊩*[E;L] args ⇐ ss ⇝ es ->
    Γ ⊩[E;L] SContinue p x args ⇐ τ ⇝ EJump CBreak (S k) (ETuple es) τ
| C_Return L Γ p a τ k ps r a' :
    return_target (ce_labs L) 0 = Some (k, r) ->
    nth_error (core_labels (ce_labs L)) k = Some (ps, r) ->
    Γ ⊩[E;L] a ⇐ r ⇝ a' ->
    Γ ⊩[E;L] SReturn p (Some a) ⇐ τ ⇝ EJump CBreak k a' τ
| C_Return0 L Γ p τ k ps :
    return_target (ce_labs L) 0 = Some (k, TUnit) ->
    nth_error (core_labels (ce_labs L)) k = Some (ps, TUnit) ->
    Γ ⊩[E;L] SReturn p None ⇐ τ ⇝ EJump CBreak k (ELit LUnit) τ
| C_Match L Γ p s cases τs τ e bs :
    Γ ⊩[E;L] s ⇒ τs ⇝ e ->
    Γ ⊩ᵇ[E;L] cases : τs ⇐ τ ⇝ bs ->
    Γ ⊩[E;L] SMatch p s cases ⇐ τ ⇝ EMatch e τ bs

with sbind (E : senv) : cenv -> lctx -> sexpr -> option sty -> ty -> expr -> Prop :=
| B_Syn L Γ s τ e :
    Γ ⊩[E;L] s ⇒ τ ⇝ e ->
    Γ ⊩[E;L] s ⦂ None ⇒ τ ⇝ e
| B_Ann L Γ s t τ e :
    ety E t = Ok τ ->
    Γ ⊩[E;L] s ⇐ τ ⇝ e ->
    Γ ⊩[E;L] s ⦂ Some t ⇒ τ ⇝ e

with arms (E : senv) : cenv -> lctx -> list (spat * sexpr) -> ty -> ty -> list (pat * expr) -> Prop :=
| Ar_nil L Γ τs τ :
    Γ ⊩ᵇ[E;L] [] : τs ⇐ τ ⇝ []
| Ar_cons L Γ sp b cases τs τ q Δ b' bs :
    ⊩ᵖ[E] sp : τs ⇝ q ⊣ Δ ->
    List.app Δ Γ ⊩[E;L] b ⇐ τ ⇝ b' ->
    Γ ⊩ᵇ[E;L] cases : τs ⇐ τ ⇝ bs ->
    Γ ⊩ᵇ[E;L] (sp, b) :: cases : τs ⇐ τ ⇝ (q, b') :: bs

(** the fields of a record, in source order; a [mut] field gets a new cell *)
with rfields (E : senv) : cenv -> lctx -> list (ident * sexpr) -> list ident -> list ty ->
                          list expr -> list nat -> Prop :=
| RF_nil L Γ names fs :
    Γ ⊩ʳ[E;L] [] : names ; fs ⇝ [] ; []
| RF_cell L Γ f fe fes names fs i t e es ixs :
    index_of f names = Some i ->
    nth_error fs i = Some (TRef t) ->
    Γ ⊩[E;L] fe ⇐ t ⇝ e ->
    Γ ⊩ʳ[E;L] fes : names ; fs ⇝ es ; ixs ->
    Γ ⊩ʳ[E;L] (f, fe) :: fes : names ; fs ⇝ EMem (MRef t) [e] :: es ; i :: ixs
| RF_plain L Γ f fe fes names fs i τ e es ixs :
    index_of f names = Some i ->
    nth_error fs i = Some τ ->
    is_cell τ = false ->
    Γ ⊩[E;L] fe ⇐ τ ⇝ e ->
    Γ ⊩ʳ[E;L] fes : names ; fs ⇝ es ; ixs ->
    Γ ⊩ʳ[E;L] (f, fe) :: fes : names ; fs ⇝ e :: es ; i :: ixs

(** the variables of a [for] loop, from their initial values *)
with sinits (E : senv) : cenv -> lctx -> list (ident * sexpr) -> list ty -> list expr -> Prop :=
| In_nil L Γ :
    Γ ⊩ⁱ[E;L] [] ⇒ [] ⇝ []
| In_cons L Γ x s inits τ τs e es :
    Γ ⊩[E;L] s ⇒ τ ⇝ e ->
    Γ ⊩ⁱ[E;L] inits ⇒ τs ⇝ es ->
    Γ ⊩ⁱ[E;L] (x, s) :: inits ⇒ τ :: τs ⇝ e :: es

(** the update clauses of a [for] loop *)
with supds (E : senv) : cenv -> lctx -> list (ident * sexpr) -> list ident -> list ty ->
                        list (ident * expr) -> Prop :=
| Up_nil L Γ names τs :
    Γ ⊩ᵘ[E;L] [] : names ; τs ⇝ []
| Up_cons L Γ y s upds names τs i τ u us :
    index_of y names = Some i ->
    nth_error τs i = Some τ ->
    Γ ⊩[E;L] s ⇐ τ ⇝ u ->
    Γ ⊩ᵘ[E;L] upds : names ; τs ⇝ us ->
    Γ ⊩ᵘ[E;L] (y, s) :: upds : names ; τs ⇝ (y, u) :: us

(** the source of a [for .. in] loop *)
with fsrc (E : senv) : cenv -> lctx -> sexpr -> expr -> expr -> iter_src -> Prop :=
(** a range: its start fixes the integer type *)
| Fs_Range L Γ q op lo hi rk kk lo' hi' :
    range_op op = Some rk ->
    Γ ⊩[E;L] lo ⇒ TInt kk ⇝ lo' ->
    (None, TInt kk) :: Γ ⊩[E;L] hi ⇐ TInt kk ⇝ hi' ->
    Γ ⊩ˢ[E;L] SInfix q op lo hi ⇝ lo' ; hi' ; IRange rk kk
(** an array, and its length *)
| Fs_Array L Γ src k t a :
    range_of src = None ->
    Γ ⊩[E;L] src ⇒ TArray k t ⇝ a ->
    Γ ⊩ˢ[E;L] src ⇝ a ; EMem (MLength k t) [EVar 0] ; IArray k t

(** an optional expression *)
with ochk (E : senv) : cenv -> lctx -> option sexpr -> ty -> option expr -> Prop :=
| Oc_None L Γ τ :
    Γ ⊩ᵒ[E;L] None ⇐ τ ⇝ None
| Oc_Some L Γ s τ e :
    Γ ⊩[E;L] s ⇐ τ ⇝ e ->
    Γ ⊩ᵒ[E;L] Some s ⇐ τ ⇝ Some e

with syns (E : senv) : cenv -> lctx -> list sexpr -> list ty -> list expr -> Prop :=
| Ss_nil L Γ :
    Γ ⊩*[E;L] [] ⇒ [] ⇝ []
| Ss_cons L Γ s ss τ τs e es :
    Γ ⊩[E;L] s ⇒ τ ⇝ e ->
    Γ ⊩*[E;L] ss ⇒ τs ⇝ es ->
    Γ ⊩*[E;L] s :: ss ⇒ τ :: τs ⇝ e :: es

with chks (E : senv) : cenv -> lctx -> list sexpr -> list ty -> list expr -> Prop :=
| Cs_nil L Γ :
    Γ ⊩*[E;L] [] ⇐ [] ⇝ []
| Cs_cons L Γ s ss τ τs e es :
    Γ ⊩[E;L] s ⇐ τ ⇝ e ->
    Γ ⊩*[E;L] ss ⇐ τs ⇝ es ->
    Γ ⊩*[E;L] s :: ss ⇐ τ :: τs ⇝ e :: es

where "Γ ⊩[ E ; L ] s ⇒ τ ⇝ e" := (syn E L Γ s τ e)
  and "Γ ⊩[ E ; L ] s ⇐ τ ⇝ e" := (chk E L Γ s τ e)
  and "Γ ⊩[ E ; L ] s ⦂ a ⇒ τ ⇝ e" := (sbind E L Γ s a τ e)
  and "Γ ⊩ᵇ[ E ; L ] cs : τs ⇐ τ ⇝ bs" := (arms E L Γ cs τs τ bs)
  and "Γ ⊩ʳ[ E ; L ] fes : names ; fs ⇝ es ; ixs" := (rfields E L Γ fes names fs es ixs)
  and "Γ ⊩ⁱ[ E ; L ] inits ⇒ τs ⇝ es" := (sinits E L Γ inits τs es)
  and "Γ ⊩ᵘ[ E ; L ] upds : names ; τs ⇝ us" := (supds E L Γ upds names τs us)
  and "Γ ⊩ˢ[ E ; L ] src ⇝ e1 ; e2 ; it" := (fsrc E L Γ src e1 e2 it)
  and "Γ ⊩ᵒ[ E ; L ] os ⇐ τ ⇝ oe" := (ochk E L Γ os τ oe)
  and "Γ ⊩*[ E ; L ] ss ⇒ τs ⇝ es" := (syns E L Γ ss τs es)
  and "Γ ⊩*[ E ; L ] ss ⇐ τs ⇝ es" := (chks E L Γ ss τs es).

Scheme syn_mut := Minimality for syn Sort Prop
  with chk_mut := Minimality for chk Sort Prop
  with sbind_mut := Minimality for sbind Sort Prop
  with arms_mut := Minimality for arms Sort Prop
  with rfields_mut := Minimality for rfields Sort Prop
  with sinits_mut := Minimality for sinits Sort Prop
  with supds_mut := Minimality for supds Sort Prop
  with fsrc_mut := Minimality for fsrc Sort Prop
  with ochk_mut := Minimality for ochk Sort Prop
  with syns_mut := Minimality for syns Sort Prop
  with chks_mut := Minimality for chks Sort Prop.
Combined Scheme elab_mutind from syn_mut, chk_mut, sbind_mut, arms_mut, rfields_mut,
  sinits_mut, supds_mut, fsrc_mut, ochk_mut, syns_mut, chks_mut.
