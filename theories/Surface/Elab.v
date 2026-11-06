(** * Elaboration: Surface → Core (preliminary)

    Turns a named [sprog] into a Core global environment and entry
    expression.  It does
    - name resolution: locals become de Bruijn indices, other names become
      globals, builtin type names become Core base types, declared types
      become [TData], type parameters become [TVar];
    - constructor resolution: [T::C], else the constructor of the expected
      type, else the unique type declaring [C];
    - desugaring: records become constructors (fields evaluated in source
      order), field access and tuple-struct projection become a one-branch
      [match], [&&]/[||] become [if];
    - operator resolution: [+], [==], ... are picked from the type of the
      left operand;
    - local type inference, bidirectional style: an expected type flows into
      literals, lambdas, tuples, constructors and branches; the type
      arguments of a generic call or constructor are found by first-order
      *matching* of the parameter types against the (already known)
      argument types.

    Types of already elaborated sub-terms are obtained from the certified
    Core checker [infer], run against a *header* environment that has the
    data types and the signatures of all top-level functions (bodies are
    irrelevant to [infer]).  So there is a single definition of typing: the
    elaborator never decides a type on its own.

    Elaboration is *not* trusted: its output is checked again by
    [check_program].  What is not yet stated (milestone M6) is the
    specification of elaboration itself, i.e. surface typing rules and a
    proof that elaboration is faithful to them.  Full MoonBit inference
    (unification variables, decision 11 in [docs/decisions.md]) is also
    future work: a lambda parameter needs either an annotation or an
    expected type. *)

From Stdlib Require Import List ZArith NArith String Bool Arith.
From MoonRocq.Prelude Require Import Result EqDec Ident.
From MoonRocq.Core Require Import Syntax Prim Subst Typing Check.
From MoonRocq.Surface Require Import Syntax.
Import ListNotations.

Local Open Scope string_scope.

Inductive elab_error : Type :=
| EE_Unbound       (p : pos) (x : ident)
| EE_UnknownType   (p : pos) (n : ident)
| EE_TypeArgs      (p : pos) (n : ident) (expected got : nat)  (** wrong number of type arguments *)
| EE_CannotInfer   (p : pos) (f : ident)       (** type arguments of a generic function / constructor *)
| EE_LambdaParam   (p : pos) (x : ident)       (** lambda parameter without known type *)
| EE_IntRange      (p : pos) (k : int_kind) (z : Z)
| EE_NoOperator    (p : pos) (op : ident) (t : ty)
| EE_Annot         (p : pos) (expected got : ty)
| EE_Type          (p : pos) (e : type_error)
| EE_UnknownCtor   (p : pos) (c : ident)
| EE_AmbiguousCtor (p : pos) (c : ident)
| EE_CtorArity     (p : pos) (c : ident) (expected got : nat)
| EE_NotRecord     (p : pos) (t : ty)
| EE_UnknownField  (p : pos) (f : ident)
| EE_MissingField  (p : pos) (f : ident)
| EE_PatType       (p : pos) (t : ty)          (** pattern shape does not fit the type *)
| EE_EmptyMatch    (p : pos).                  (** [match] without arms nor expected type *)

(** ** Small utilities *)

Fixpoint assoc {A} (x : ident) (l : list (ident * A)) : option A :=
  match l with
  | [] => None
  | (y, a) :: l' => if eqb x y then Some a else assoc x l'
  end.

Fixpoint index_of (x : ident) (l : list ident) : option nat :=
  match l with
  | [] => None
  | y :: l' => if eqb x y then Some 0 else option_map S (index_of x l')
  end.

Fixpoint set_nth {A} (i : nat) (x : A) (l : list A) : list A :=
  match l, i with
  | [], _ => []
  | _ :: l', 0 => x :: l'
  | y :: l', S i' => y :: set_nth i' x l'
  end.

Fixpoint all_some {A} (l : list (option A)) : option (list A) :=
  match l with
  | [] => Some []
  | Some a :: l' => option_map (cons a) (all_some l')
  | None :: _ => None
  end.

Definition of_opt {A} (o : option A) (e : elab_error) : result A elab_error :=
  match o with Some a => Ok a | None => Err e end.

Definition tvars (n : nat) : list ty := map TVar (seq 0 n).

(** ** Types *)

Definition builtin_types : list (ident * ty) :=
  [ ("Unit", TUnit); ("Bool", TBool);
    ("Int", TInt I32); ("Int16", TInt I16); ("Int64", TInt I64);
    ("UInt", TInt U32); ("UInt16", TInt U16); ("UInt64", TInt U64);
    ("Byte", TInt IByte); ("BigInt", TInt IBigInt);
    ("Char", TBase BChar); ("Double", TBase BDouble); ("Float", TBase BFloat);
    ("String", TString) ].

(** The builtin data type [Option[T] { None; Some(T) }]. *)
Definition option_tdef : tdef :=
  mk_tdef "Option" 1 [mk_cdef "None" []; mk_cdef "Some" [TVar 0]].

(** [tys]: the data types in scope with their number of parameters.
    Type parameters shadow everything else, then builtin types. *)
Fixpoint elab_ty (tys : list (ident * nat)) (tps : list ident) (t : sty) : result ty elab_error :=
  match t with
  | SName p n args =>
      match index_of n tps, assoc n builtin_types, assoc n tys with
      | Some i, _, _ =>
          match args with [] => Ok (TVar i) | _ => Err (EE_TypeArgs p n 0 (List.length args)) end
      | None, Some τ, _ =>
          match args with [] => Ok τ | _ => Err (EE_TypeArgs p n 0 (List.length args)) end
      | None, None, Some k =>
          if Nat.eqb k (List.length args) then
            τs <- mapM (elab_ty tys tps) args ;;
            Ok (TData n τs)
          else Err (EE_TypeArgs p n k (List.length args))
      | None, None, None => Err (EE_UnknownType p n)
      end
  | STuple _ ts =>
      τs <- mapM (elab_ty tys tps) ts ;;
      Ok (TTuple τs)
  | SArrow _ ps r =>
      τs <- mapM (elab_ty tys tps) ps ;;
      τ <- elab_ty tys tps r ;;
      Ok (TArrow τs τ)
  end.

(** ** Matching, for the type arguments of generic calls

    [tmatch p t s] extends the partial instantiation [s] (one slot per type
    parameter of the callee) so that [p] instantiated by [s] becomes [t].
    Mismatches are ignored here: the Core checker reports them later with a
    precise error.  The type variables of [t] (those of the caller) are
    never bound. *)
Fixpoint tmatch (p t : ty) (s : list (option ty)) {struct p} : list (option ty) :=
  let fix go (ps ts : list ty) (s : list (option ty)) : list (option ty) :=
    match ps, ts with
    | p :: ps', t :: ts' => go ps' ts' (tmatch p t s)
    | _, _ => s
    end in
  match p, t with
  | TVar i, _ =>
      match nth_error s i with
      | Some None => set_nth i (Some t) s
      | _ => s
      end
  | TTuple ps, TTuple ts => go ps ts s
  | TArrow ps r, TArrow ts u => tmatch r u (go ps ts s)
  | TData T ps, TData U ts => if eqb T U then go ps ts s else s
  | _, _ => s
  end.

(** [p] under [s], if all its type variables are determined. *)
Fixpoint resolve (s : list (option ty)) (p : ty) {struct p} : option ty :=
  let fix go (ps : list ty) : option (list ty) :=
    match ps with
    | [] => Some []
    | p :: ps' =>
        match resolve s p, go ps' with
        | Some t, Some ts => Some (t :: ts)
        | _, _ => None
        end
    end in
  match p with
  | TBase b => Some (TBase b)
  | TVar i => match nth_error s i with Some (Some t) => Some t | _ => None end
  | TTuple ps => option_map TTuple (go ps)
  | TArrow ps r =>
      match go ps, resolve s r with
      | Some ts, Some t => Some (TArrow ts t)
      | _, _ => None
      end
  | TData T ps => option_map (TData T) (go ps)
  end.

(** ** Literals and operators *)

Definition int_in_range (k : int_kind) (z : Z) : bool := Z.eqb (wrap k z) z.

Definition elab_lit (p : pos) (exp : option ty) (l : slit) : result lit elab_error :=
  let int k z :=
    if int_in_range k z then Ok (LInt k z) else Err (EE_IntRange p k z) in
  match l with
  | SLUnit => Ok LUnit
  | SLBool b => Ok (LBool b)
  | SLInt (Some k) z => int k z
  | SLInt None z =>
      match exp with
      | Some (TBase (BInt k)) => int k z
      | _ => int I32 z
      end
  | SLChar c => Ok (LChar c)
  | SLDouble b => Ok (LDouble b)
  | SLFloat b => Ok (LFloat b)
  | SLString s => Ok (LString s)
  end.

Definition arith_ops : list (ident * arith_op) :=
  [("+", AAdd); ("-", ASub); ("*", AMul); ("/", ADiv); ("%", AMod)].

Definition cmp_ops : list (ident * cmp_op) :=
  [("==", CEq); ("!=", CNe); ("<", CLt); ("<=", CLe); (">", CGt); (">=", CGe)].

Definition e_true  := ELit (LBool true).
Definition e_false := ELit (LBool false).

(** Resolve a binary operator from the type [ta] of its left operand. *)
Definition elab_binop (p : pos) (op : ident) (ta : ty) (a b : expr) : result expr elab_error :=
  match assoc op arith_ops, assoc op cmp_ops, ta with
  | Some o, _, TBase (BInt k) => Ok (EPrim (PIntArith o k) [a; b])
  | Some AAdd, _, TBase BString => Ok (EPrim PStrConcat [a; b])
  | _, Some c, TBase (BInt k) => Ok (EPrim (PIntCmp c k) [a; b])
  | _, Some c, TBase BChar => Ok (EPrim (PCharCmp c) [a; b])
  | _, Some CEq, TBase BBool => Ok (EPrim PBoolEq [a; b])
  | _, Some CNe, TBase BBool => Ok (EPrim PBoolNot [EPrim PBoolEq [a; b]])
  | _, Some CEq, TBase BString => Ok (EPrim PStrEq [a; b])
  | _, Some CNe, TBase BString => Ok (EPrim PBoolNot [EPrim PStrEq [a; b]])
  | _, _, _ => Err (EE_NoOperator p op ta)
  end.

(** An unsuffixed integer literal: its type is decided by the context. *)
Definition flexible (e : sexpr) : bool :=
  match e with
  | SLit _ (SLInt None _) => true
  | _ => false
  end.

(** ** Expressions *)

(** Local context: innermost binding first, [None] for [_]/sequencing. *)
Definition lctx : Type := list (option ident * ty).

Fixpoint lookup_local (x : ident) (Γ : lctx) : option nat :=
  match Γ with
  | [] => None
  | (Some y, _) :: Γ' => if eqb x y then Some 0 else option_map S (lookup_local x Γ')
  | (None, _) :: Γ' => option_map S (lookup_local x Γ')
  end.

Section Elab.
  Variable tys : list (ident * nat).               (** data types in scope *)
  Variable hdr : genv.                             (** data types + signatures of functions *)
  Variable sinfo : list (ident * list ident).      (** field names of record structs *)
  Variable tps : list ident.                       (** type parameters in scope *)

  Definition type_of (p : pos) (Γ : lctx) (e : expr) : result ty elab_error :=
    match infer hdr (map snd Γ) e with
    | Ok (exist _ τ _) => Ok τ
    | Err err => Err (EE_Type p err)
    end.

  Definition arrow_params (t : ty) (n : nat) : list (option ty) :=
    match t with
    | TArrow ps _ => if Nat.eqb (List.length ps) n then map Some ps else repeat None n
    | _ => repeat None n
    end.

  (** A global function used as a value (not called): its type arguments
      come from the expected type. *)
  Definition elab_global (p : pos) (f : ident) (fd : fdef) (exp : option ty) :
      result expr elab_error :=
    match fd_tparams fd with
    | 0 => Ok (EGlobal f [])
    | n =>
        let s := match exp with
                 | Some t => tmatch (TArrow (fd_params fd) (fd_ret fd)) t (repeat None n)
                 | None => repeat None n
                 end in
        match all_some s with
        | Some ts => Ok (EGlobal f ts)
        | None => Err (EE_CannotInfer p f)
        end
    end.

  (** *** Data types *)

  Definition is_record (T : ident) : bool :=
    match assoc T sinfo with Some _ => true | None => false end.

  Definition has_ctor (c : ident) (td : tdef) : bool :=
    match lookup_ctor td c with Some _ => true | None => false end.

  (** Record structs are built with [{ .. }], not by their constructor name. *)
  Definition resolve_ctor (p : pos) (tq : option ident) (c : ident) (exp : option ty) :
      result (tdef * cdef) elab_error :=
    let in_type td :=
      match lookup_ctor td c with
      | Some cd => Ok (td, cd)
      | None => Err (EE_UnknownCtor p c)
      end in
    match tq with
    | Some T =>
        td <- of_opt (lookup_ty hdr T) (EE_UnknownType p T) ;;
        in_type td
    | None =>
        let from_exp :=
          match exp with
          | Some (TData T _) =>
              match lookup_ty hdr T with
              | Some td => if has_ctor c td then Some td else None
              | None => None
              end
          | _ => None
          end in
        match from_exp with
        | Some td => in_type td
        | None =>
            match filter (fun td => negb (is_record (td_name td)) && has_ctor c td)
                         (ge_types hdr) with
            | [td] => in_type td
            | [] => Err (EE_UnknownCtor p c)
            | _ => Err (EE_AmbiguousCtor p c)
            end
        end
    end.

  (** The record struct built by [{ fields }]: named, from the expected
      type, or the unique struct with exactly these field names. *)
  Definition resolve_record (p : pos) (tq : option ident) (names : list ident)
      (exp : option ty) : result ident elab_error :=
    let same fs := Nat.eqb (List.length fs) (List.length names) &&
                   forallb (fun f => match index_of f fs with Some _ => true | None => false end)
                           names in
    match tq, exp with
    | Some T, _ => Ok T
    | None, Some (TData T _) => if is_record T then Ok T else Err (EE_NotRecord p (TData T []))
    | None, _ =>
        match filter (fun tf => same (snd tf)) sinfo with
        | [(T, _)] => Ok T
        | _ => Err (EE_NotRecord p TUnit)
        end
    end.

  (** Field [i] of a single-constructor type, as a one-branch [match]. *)
  Definition proj_field (p : pos) (T : ident) (ts : list ty) (i : nat) (e : expr) :
      result expr elab_error :=
    td <- of_opt (lookup_ty hdr T) (EE_UnknownType p T) ;;
    match td_ctors td with
    | [cd] =>
        let fs := map (tsubst (inst ts)) (cd_fields cd) in
        τ <- of_opt (nth_error fs i) (EE_Type p (E_TupleIndex i (TData T ts))) ;;
        let ps := map (fun j => if Nat.eqb j i then PVar else PWild) (seq 0 (List.length fs)) in
        Ok (EMatch e τ [(PConstr (cd_name cd) ps, EVar 0)])
    | _ => Err (EE_NotRecord p (TData T ts))
    end.

  (** *** Patterns

      [elab_pat τ sp] elaborates [sp] against the scrutinee type [τ] and
      returns the Core pattern with its bindings, leftmost first (the order
      of [⊢ᵖ]). *)
  Fixpoint elab_pat (τ : ty) (sp : spat) {struct sp} : result (pat * lctx) elab_error :=
    (* sub-patterns against field types; [open]: missing ones are wildcards *)
    let fix go (p : pos) (open : bool) (sps : list spat) (τs : list ty) :
        result (list pat * lctx) elab_error :=
      match sps, τs with
      | [], [] => Ok ([], [])
      | [], _ :: _ =>
          if open then Ok (map (fun _ => PWild) τs, [])
          else Err (EE_PatType p τ)
      | sp :: sps', τ0 :: τs' =>
          '(q, Δ1) <- elab_pat τ0 sp ;;
          '(qs, Δ2) <- go p open sps' τs' ;;
          Ok (q :: qs, List.app Δ1 Δ2)
      | _ :: _, [] => Err (EE_PatType p τ)
      end in
    (* named sub-patterns, in source order: (field index, pattern, bindings) *)
    let fix named (p : pos) (names : list ident) (fs : list ty) (fps : list (ident * spat)) :
        result (list (nat * pat * lctx)) elab_error :=
      match fps with
      | [] => Ok []
      | (f, sp) :: fps' =>
          i <- of_opt (index_of f names) (EE_UnknownField p f) ;;
          τi <- of_opt (nth_error fs i) (EE_UnknownField p f) ;;
          '(q, Δ) <- elab_pat τi sp ;;
          rest <- named p names fs fps' ;;
          Ok ((i, q, Δ) :: rest)
      end in
    match sp with
    | SPWild _ => Ok (PWild, [])
    | SPVar _ x => Ok (PVar, [(Some x, τ)])
    | SPLit p l => l' <- elab_lit p (Some τ) l ;; Ok (PLit l', [])
    | SPTuple p sps =>
        match τ with
        | TTuple τs => '(qs, Δ) <- go p false sps τs ;; Ok (PTuple qs, Δ)
        | _ => Err (EE_PatType p τ)
        end
    | SPConstr p tq c sps open =>
        match τ with
        | TData T ts =>
            td <- of_opt (lookup_ty hdr T) (EE_UnknownType p T) ;;
            _ <- match tq with
                 | Some T' => if eqb T T' then Ok tt else Err (EE_PatType p τ)
                 | None => Ok tt
                 end ;;
            cd <- of_opt (lookup_ctor td c) (EE_UnknownCtor p c) ;;
            '(qs, Δ) <- go p open sps (map (tsubst (inst ts)) (cd_fields cd)) ;;
            Ok (PConstr c qs, Δ)
        | _ => Err (EE_PatType p τ)
        end
    | SPRecord p fps open =>
        match τ with
        | TData T ts =>
            names <- of_opt (assoc T sinfo) (EE_NotRecord p τ) ;;
            td <- of_opt (lookup_ty hdr T) (EE_UnknownType p T) ;;
            match td_ctors td with
            | [cd] =>
                let fs := map (tsubst (inst ts)) (cd_fields cd) in
                given <- named p names fs fps ;;
                let pick j :=
                  match find (fun x => Nat.eqb (fst (fst x)) j) given with
                  | Some (_, q, Δ) => Ok (q, Δ)
                  | None =>
                      if open then Ok (PWild, [])
                      else Err (EE_MissingField p (nth j names ""))
                  end in
                qΔs <- mapM pick (seq 0 (List.length fs)) ;;
                Ok (PConstr (cd_name cd) (map fst qΔs), List.concat (map snd qΔs))
            | _ => Err (EE_NotRecord p τ)
            end
        | _ => Err (EE_NotRecord p τ)
        end
    | SPAnnot p q t =>
        τ' <- elab_ty tys tps t ;;
        if eqb τ' τ then elab_pat τ q else Err (EE_Annot p τ' τ)
    end.

  (** *** Lambdas *)

  (** Types of lambda parameters: annotation, else expectation. *)
  Fixpoint param_tys (p : pos) (ps : list (ident * option sty)) (exps : list (option ty)) :
      result (list ty) elab_error :=
    match ps with
    | [] => Ok []
    | (x, ann) :: ps' =>
        let (ex, exps') := match exps with
                           | [] => (None, [])
                           | y :: ys => (y, ys)
                           end in
        τ <- match ann, ex with
             | Some t, _ => elab_ty tys tps t
             | None, Some τ => Ok τ
             | None, None => Err (EE_LambdaParam p x)
             end ;;
        τs <- param_tys p ps' exps' ;;
        Ok (τ :: τs)
    end.

  (** A lambda, from (possibly partial) expectations [pexps] for its
      parameter types and [rexp] for its result type; [elab_body] elaborates
      the body in the extended context. *)
  Definition elab_lam (Γ : lctx) (p : pos) (ps : list (ident * option sty)) (ret : option sty)
      (pexps : list (option ty)) (rexp : option ty)
      (elab_body : lctx -> option ty -> result expr elab_error) : result expr elab_error :=
    τs <- param_tys p ps pexps ;;
    let Γ' := List.app (combine (map (fun x => Some (fst x)) ps) τs) Γ in
    τr <- match ret with
          | Some t => map_result Some (elab_ty tys tps t)
          | None => Ok rexp
          end ;;
    body' <- elab_body Γ' τr ;;
    r <- match τr with
         | Some r => Ok r
         | None => type_of p Γ' body'
         end ;;
    Ok (ELam τs r body').

  (** A lambda whose parameter types must come from the context. *)
  Definition needs_context (e : sexpr) : bool :=
    match e with
    | SLam _ ps _ _ => existsb (fun xa => match snd xa with None => true | Some _ => false end) ps
    | _ => false
    end.

  (** Instantiation of a data type from the expected type. *)
  Definition data_inst (T : ident) (n : nat) (exp : option ty) : list (option ty) :=
    match exp with
    | Some t => tmatch (TData T (tvars n)) t (repeat None n)
    | None => repeat None n
    end.

  (** *** Expressions *)

  Fixpoint elab (Γ : lctx) (exp : option ty) (e : sexpr) {struct e} : result expr elab_error :=
    (* elaborate a list against a list of expected types *)
    let fix elab_args (es : list sexpr) (exps : list (option ty)) : result (list expr) elab_error :=
      match es with
      | [] => Ok []
      | e :: es' =>
          let (x, exps') := match exps with
                            | [] => (None, [])
                            | x :: xs => (x, xs)
                            end in
          e' <- elab Γ x e ;;
          es2 <- elab_args es' exps' ;;
          Ok (e' :: es2)
      end in
    (* Arguments of a generic call, threading the partial instantiation [s].
       Pass 1 elaborates left to right, but postpones lambdas that have
       unannotated parameters and no known expected type; pass 2 elaborates
       those with what the other arguments taught us (possibly only their
       parameter types).  [gargs1] returns [None] for postponed arguments. *)
    let fix gargs1 (p : pos) (es : list sexpr) (ps : list ty) (s : list (option ty)) :
        result (list (option expr) * list (option ty)) elab_error :=
      match es with
      | [] => Ok ([], s)
      | e :: es' =>
          let (pt, ps') := match ps with
                           | [] => (None, [])
                           | t :: ts => (Some t, ts)
                           end in
          let ex := match pt with Some t => resolve s t | None => None end in
          if andb (needs_context e) (match ex with None => true | Some _ => false end) then
            '(r, s2) <- gargs1 p es' ps' s ;;
            Ok (None :: r, s2)
          else
            e' <- elab Γ ex e ;;
            s' <- match pt with
                  | Some t => τ <- type_of p Γ e' ;; Ok (tmatch t τ s)
                  | None => Ok s
                  end ;;
            '(r, s2) <- gargs1 p es' ps' s' ;;
            Ok (Some e' :: r, s2)
      end in
    let fix gargs2 (p : pos) (es : list sexpr) (pre : list (option expr)) (ps : list ty)
        (s : list (option ty)) : result (list expr * list (option ty)) elab_error :=
      match es with
      | [] => Ok ([], s)
      | e :: es' =>
          let (d, pre') := match pre with
                           | [] => (None, [])
                           | d :: ds => (d, ds)
                           end in
          let (pt, ps') := match ps with
                           | [] => (None, [])
                           | t :: ts => (Some t, ts)
                           end in
          e' <- match d with
                | Some e' => Ok e'
                | None =>
                    match e, pt with
                    | SLam q lps ret body, Some (TArrow pps pr) =>
                        let pexps := if Nat.eqb (List.length pps) (List.length lps)
                                     then map (resolve s) pps
                                     else repeat None (List.length lps) in
                        elab_lam Γ q lps ret pexps (resolve s pr) (fun Γ' t => elab Γ' t body)
                    | _, _ => elab Γ (match pt with Some t => resolve s t | None => None end) e
                    end
                end ;;
          s' <- match d, pt with
                | None, Some t => τ <- type_of p Γ e' ;; Ok (tmatch t τ s)
                | _, _ => Ok s
                end ;;
          '(r, s2) <- gargs2 p es' pre' ps' s' ;;
          Ok (e' :: r, s2)
      end in
    (* Constructor [cd] of [td] applied to [args]. *)
    let ctor_app (p q : pos) (td : tdef) (cd : cdef) (args : list sexpr) :=
      let n := td_tparams td in
      let fs := cd_fields cd in
      if negb (Nat.eqb (List.length fs) (List.length args)) then
        Err (EE_CtorArity q (cd_name cd) (List.length fs) (List.length args))
      else
        '(pre, s1) <- gargs1 p args fs (data_inst (td_name td) n exp) ;;
        '(args', s) <- gargs2 p args pre fs s1 ;;
        match all_some s with
        | Some ts => Ok (EConstr (td_name td) (cd_name cd) ts (ETuple args'))
        | None => Err (EE_CannotInfer q (cd_name cd))
        end in
    (* Record fields in source order, each bound by a [let] (so that they are
       evaluated in source order); returns the field index of each binding,
       innermost (last written) first, and the final instantiation. *)
    let fix rfields (p : pos) (Γ0 : lctx) (names : list ident) (fs : list ty)
        (fes : list (ident * sexpr)) (s : list (option ty)) :
        result (list (expr * nat) * lctx * list (option ty)) elab_error :=
      match fes with
      | [] => Ok ([], Γ0, s)
      | (f, fe) :: fes' =>
          i <- of_opt (index_of f names) (EE_UnknownField p f) ;;
          τf <- of_opt (nth_error fs i) (EE_UnknownField p f) ;;
          e' <- elab Γ0 (resolve s τf) fe ;;
          τ <- type_of p Γ0 e' ;;
          '(rest, Γ1, s1) <- rfields p ((None, τ) :: Γ0) names fs fes' (tmatch τf τ s) ;;
          Ok ((e', i) :: rest, Γ1, s1)
      end in
    match e with
    | SVar p x =>
        match lookup_local x Γ with
        | Some i => Ok (EVar i)
        | None =>
            match lookup_fn hdr x with
            | Some fd => elab_global p x fd exp
            | None => Err (EE_Unbound p x)
            end
        end
    | SLit p l => l' <- elab_lit p exp l ;; Ok (ELit l')
    | SApp p f args =>
        match f with
        | SConstr q tq c =>
            '(td, cd) <- resolve_ctor q tq c exp ;;
            ctor_app p q td cd args
        | SVar q g =>
            match lookup_local g Γ, lookup_fn hdr g with
            | None, Some fd =>
                match fd_tparams fd with
                | 0 =>
                    args' <- elab_args args (map Some (fd_params fd)) ;;
                    Ok (EApp (EGlobal g []) args')
                | n =>
                    let s0 := match exp with
                              | Some t => tmatch (fd_ret fd) t (repeat None n)
                              | None => repeat None n
                              end in
                    '(pre, s1) <- gargs1 p args (fd_params fd) s0 ;;
                    '(args', s) <- gargs2 p args pre (fd_params fd) s1 ;;
                    match all_some s with
                    | Some ts => Ok (EApp (EGlobal g ts) args')
                    | None => Err (EE_CannotInfer q g)
                    end
                end
            | None, None =>
                (* builtins that are not ordinary functions in Core *)
                if eqb g "not" then
                  args' <- elab_args args [Some TBool] ;;
                  Ok (EPrim PBoolNot args')
                else if eqb g "ignore" then
                  match args with
                  | [a] => a' <- elab Γ None a ;; Ok (ELet a' (ELit LUnit))
                  | _ => Err (EE_Unbound q g)
                  end
                else Err (EE_Unbound q g)
            | Some _, _ =>
                f' <- elab Γ None f ;;
                τf <- type_of p Γ f' ;;
                args' <- elab_args args (arrow_params τf (List.length args)) ;;
                Ok (EApp f' args')
            end
        | _ =>
            f' <- elab Γ None f ;;
            τf <- type_of p Γ f' ;;
            args' <- elab_args args (arrow_params τf (List.length args)) ;;
            Ok (EApp f' args')
        end
    | SConstr p tq c =>
        '(td, cd) <- resolve_ctor p tq c exp ;;
        ctor_app p p td cd []
    | SRecord p tq fes =>
        T <- resolve_record p tq (map fst fes) exp ;;
        names <- of_opt (assoc T sinfo) (EE_NotRecord p (TData T [])) ;;
        td <- of_opt (lookup_ty hdr T) (EE_UnknownType p T) ;;
        match td_ctors td with
        | [cd] =>
            let n := td_tparams td in
            '(bound, _, s) <- rfields p Γ names (cd_fields cd) fes (data_inst T n exp) ;;
            ts <- of_opt (all_some s) (EE_CannotInfer p T) ;;
            let m := List.length bound in
            (* the binding of field [j] is the [k]-th written one *)
            let var_of j :=
              match find (fun x => Nat.eqb (snd (fst x)) j) (combine bound (seq 0 m)) with
              | Some (_, k) => Ok (EVar (m - 1 - k))
              | None => Err (EE_MissingField p (nth j names ""))
              end in
            vs <- mapM var_of (seq 0 (List.length names)) ;;
            _ <- if Nat.eqb m (List.length names) then Ok tt
                 else Err (EE_UnknownField p "") ;;
            Ok (fold_right (fun b acc => ELet (fst b) acc)
                           (EConstr T (cd_name cd) ts (ETuple vs)) bound)
        | _ => Err (EE_NotRecord p (TData T []))
        end
    | SField p e0 f =>
        e0' <- elab Γ None e0 ;;
        τ <- type_of p Γ e0' ;;
        match τ with
        | TData T ts =>
            names <- of_opt (assoc T sinfo) (EE_NotRecord p τ) ;;
            i <- of_opt (index_of f names) (EE_UnknownField p f) ;;
            proj_field p T ts i e0'
        | _ => Err (EE_NotRecord p τ)
        end
    | SMatch p e0 cases =>
        e0' <- elab Γ None e0 ;;
        τs <- type_of p Γ e0' ;;
        let fix arms (cs : list (spat * sexpr)) (exp : option ty) :
            result (list (pat * expr) * option ty) elab_error :=
          match cs with
          | [] => Ok ([], exp)
          | (sp, b) :: cs' =>
              '(q, Δ) <- elab_pat τs sp ;;
              let Γ' := List.app Δ Γ in
              b' <- elab Γ' exp b ;;
              τb <- match exp with
                    | Some t => Ok t
                    | None => type_of p Γ' b'
                    end ;;
              '(rest, r) <- arms cs' (Some τb) ;;
              Ok ((q, b') :: rest, r)
          end in
        '(bs, r) <- arms cases exp ;;
        τ <- of_opt r (EE_EmptyMatch p) ;;
        Ok (EMatch e0' τ bs)
    | SInfix p op a b =>
        if eqb op "&&" then
          a' <- elab Γ (Some TBool) a ;;
          b' <- elab Γ (Some TBool) b ;;
          Ok (EIf a' b' e_false)
        else if eqb op "||" then
          a' <- elab Γ (Some TBool) a ;;
          b' <- elab Γ (Some TBool) b ;;
          Ok (EIf a' e_true b')
        else
          (* the expected type only flows into arithmetic operands *)
          let exp' := match assoc op arith_ops with Some _ => exp | None => None end in
          if andb (flexible a) (negb (flexible b)) then
            b' <- elab Γ exp' b ;;
            τ <- type_of p Γ b' ;;
            a' <- elab Γ (Some τ) a ;;
            elab_binop p op τ a' b'
          else
            a' <- elab Γ exp' a ;;
            τ <- type_of p Γ a' ;;
            b' <- elab Γ (Some τ) b ;;
            elab_binop p op τ a' b'
    | SUnary p op a =>
        if eqb op "-" then
          match a with
          | SLit q (SLInt k z) => l' <- elab_lit q exp (SLInt k (Z.opp z)) ;; Ok (ELit l')
          | _ =>
              a' <- elab Γ exp a ;;
              τ <- type_of p Γ a' ;;
              match τ with
              | TBase (BInt k) => Ok (EPrim (PIntNeg k) [a'])
              | _ => Err (EE_NoOperator p op τ)
              end
          end
        else if eqb op "!" then
          a' <- elab Γ (Some TBool) a ;;
          Ok (EPrim PBoolNot [a'])
        else Err (EE_NoOperator p op TUnit)
    | SLet p x ann e1 body =>
        τann <- match ann with
                | Some t => map_result Some (elab_ty tys tps t)
                | None => Ok None
                end ;;
        e1' <- elab Γ τann e1 ;;
        τ1 <- type_of p Γ e1' ;;
        _ <- match τann with
             | Some t => if eqb t τ1 then Ok tt else Err (EE_Annot p t τ1)
             | None => Ok tt
             end ;;
        body' <- elab ((x, τ1) :: Γ) exp body ;;
        Ok (ELet e1' body')
    | SIf p c t oe =>
        c' <- elab Γ (Some TBool) c ;;
        match oe with
        | Some e0 =>
            t' <- elab Γ exp t ;;
            exp' <- match exp with
                    | Some τ => Ok (Some τ)
                    | None => map_result Some (type_of p Γ t')
                    end ;;
            e0' <- elab Γ exp' e0 ;;
            Ok (EIf c' t' e0')
        | None =>
            t' <- elab Γ (Some TUnit) t ;;
            Ok (EIf c' t' (ELit LUnit))
        end
    | STup p es =>
        let exps := match exp with
                    | Some (TTuple ts) =>
                        if Nat.eqb (List.length ts) (List.length es) then map Some ts
                        else repeat None (List.length es)
                    | _ => repeat None (List.length es)
                    end in
        es' <- elab_args es exps ;;
        Ok (ETuple es')
    | SProj p e0 i =>
        e0' <- elab Γ None e0 ;;
        τ <- type_of p Γ e0' ;;
        match τ with
        | TData T ts => proj_field p T ts i e0'      (* tuple struct *)
        | _ => Ok (EProj e0' i)
        end
    | SLam p ps ret body =>
        let pexps := match exp with
                     | Some t => arrow_params t (List.length ps)
                     | None => repeat None (List.length ps)
                     end in
        let rexp := match exp with Some (TArrow _ r) => Some r | _ => None end in
        elab_lam Γ p ps ret pexps rexp (fun Γ' t => elab Γ' t body)
    | SAnnot p e0 t =>
        τ <- elab_ty tys tps t ;;
        e0' <- elab Γ (Some τ) e0 ;;
        τ0 <- type_of p Γ e0' ;;
        if eqb τ τ0 then Ok e0' else Err (EE_Annot p τ τ0)
    end.
End Elab.

(** ** Programs *)

Definition elab_tdef (tys : list (ident * nat)) (st : stype) : result tdef elab_error :=
  let tps := st_tparams st in
  let n := List.length tps in
  match st_body st with
  | SDEnum cs =>
      cds <- mapM (fun c => τs <- mapM (elab_ty tys tps) (snd c) ;; Ok (mk_cdef (fst c) τs)) cs ;;
      Ok (mk_tdef (st_name st) n cds)
  | SDStruct fs =>
      τs <- mapM (fun f => elab_ty tys tps (snd f)) fs ;;
      Ok (mk_tdef (st_name st) n [mk_cdef (st_name st) τs])
  | SDTupleStruct ts =>
      τs <- mapM (elab_ty tys tps) ts ;;
      Ok (mk_tdef (st_name st) n [mk_cdef (st_name st) τs])
  end.

Definition elab_sig (tys : list (ident * nat)) (f : sfun) : result fdef elab_error :=
  τs <- mapM (fun xt => elab_ty tys (sf_tparams f) (snd xt)) (sf_params f) ;;
  τ <- match sf_ret f with
       | Some t => elab_ty tys (sf_tparams f) t
       | None => Ok TUnit
       end ;;
  Ok (mk_fdef (sf_name f) (List.length (sf_tparams f)) τs τ (ELit LUnit)).

Definition elab_fun tys hdr sinfo (f : sfun) (sig : fdef) : result fdef elab_error :=
  let Γ := combine (map (fun xt => Some (fst xt)) (sf_params f)) (fd_params sig) in
  b <- elab tys hdr sinfo (sf_tparams f) Γ (Some (fd_ret sig)) (sf_body f) ;;
  Ok (mk_fdef (fd_name sig) (fd_tparams sig) (fd_params sig) (fd_ret sig) b).

Fixpoint elab_funs tys hdr sinfo (fs : list sfun) (sigs : list fdef) : result (list fdef) elab_error :=
  match fs, sigs with
  | f :: fs', sig :: sigs' =>
      fd <- elab_fun tys hdr sinfo f sig ;;
      fds <- elab_funs tys hdr sinfo fs' sigs' ;;
      Ok (fd :: fds)
  | _, _ => Ok []
  end.

(** The entry expression is the body of [fn main] (checked against [Unit]),
    or [()] when there is none.  [Option] is predeclared. *)
Definition elab_prog (sp : sprog) : result (genv * expr) elab_error :=
  let tys := ("Option", 1) :: map (fun st => (st_name st, List.length (st_tparams st))) (sp_types sp) in
  let sinfo := flat_map (fun st => match st_body st with
                                   | SDStruct fs => [(st_name st, map fst fs)]
                                   | _ => []
                                   end) (sp_types sp) in
  tds <- mapM (elab_tdef tys) (sp_types sp) ;;
  let types := option_tdef :: tds in
  sigs <- mapM (elab_sig tys) (sp_funs sp) ;;
  let hdr := mk_genv types sigs in
  funs <- elab_funs tys hdr sinfo (sp_funs sp) sigs ;;
  main <- match sp_main sp with
          | Some e =>
              elab tys hdr sinfo [] [] (Some TUnit)
                   (SAnnot (sexpr_pos e) e (SName (sexpr_pos e) "Unit" []))
          | None => Ok (ELit LUnit)
          end ;;
  Ok (mk_genv types funs, main).
