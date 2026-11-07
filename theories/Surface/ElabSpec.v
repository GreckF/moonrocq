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
    constructors, patterns, [match], field access and the projections of
    tuple structs. *)

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

(** The arm of a [match] that gives its type: the first one that does not
    certainly jump away, else the first one. *)
Definition pick_arm (cases : list (spat * sexpr)) : option (spat * sexpr) :=
  match find (fun c => negb (diverges (snd c))) cases with
  | Some c => Some c
  | None => hd_error cases
  end.

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
  and "Γ ⊩*[ E ; L ] ss ⇒ τs ⇝ es" := (syns E L Γ ss τs es)
  and "Γ ⊩*[ E ; L ] ss ⇐ τs ⇝ es" := (chks E L Γ ss τs es).

Scheme syn_mut := Minimality for syn Sort Prop
  with chk_mut := Minimality for chk Sort Prop
  with sbind_mut := Minimality for sbind Sort Prop
  with arms_mut := Minimality for arms Sort Prop
  with syns_mut := Minimality for syns Sort Prop
  with chks_mut := Minimality for chks Sort Prop.
Combined Scheme elab_mutind from syn_mut, chk_mut, sbind_mut, arms_mut, syns_mut, chks_mut.
