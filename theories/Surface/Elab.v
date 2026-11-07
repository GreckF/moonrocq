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
    expected type.

    Milestone M3: a [let mut] variable is a cell ([TRef]) in Core, read and
    written with store operations; a [mut] struct field holds a cell too.
    Loops, labelled blocks and function bodies become Core [ELoop]s; the
    label environment [L] has one entry per enclosing [ELoop] and resolves
    [break]/[continue]/[return] to de Bruijn indices. *)

From Stdlib Require Import List ZArith NArith String Bool Arith.
From MoonRocq.Prelude Require Import Result EqDec Ident ListDec.
From MoonRocq.Core Require Import Syntax Prim Subst Typing Check.
From MoonRocq.Surface Require Import Syntax Resolve Base.
Import ListNotations.

Local Open Scope string_scope.

Section Elab.
  Variable tys : list (ident * nat).               (** data types in scope *)
  Variable hdr : genv.                             (** data types + signatures of functions *)
  Variable sinfo : list (ident * list ident).      (** field names of record structs *)
  Variable tps : list ident.                       (** type parameters in scope *)
  Variable gx : xenv.                              (** traits, instances, bounds, methods *)

  Definition type_of (p : pos) (L : cenv) (Γ : lctx) (e : expr) : result ty elab_error :=
    match infer hdr [] (mk_cctx (core_labels (ce_labs L)) (ce_exn L)) (map snd Γ) e with
    | Ok (exist _ τ _) => Ok τ
    | Err err => Err (EE_Type p err)
    end.

  (** *** Dictionaries *)

  (** The dictionary of [Tr[τ]] in context [Γ]: assumptions are the
      dictionary variables of the current definition. *)
  Definition dict_of (p : pos) (Γ : lctx) (Tr : ident) (τ : ty) : result expr elab_error :=
    let Θ := flat_map (fun a => let '(Tr', τ', x) := a in
                                match lookup_local x Γ with
                                | Some i => [(Tr', τ', EVar i)]
                                | None => []
                                end) (x_asm gx) in
    match entails_dec (x_insts gx) Θ Tr τ with
    | inleft (exist _ d _) => Ok d
    | inright _ => Err (EE_NoInstance p Tr τ)
    end.

  Definition has_meth (T m : ident) : bool :=
    existsb (fun tm => (eqb (fst tm) T && eqb (snd tm) m)%bool) (x_meths gx).

  Definition bounds_of (g : ident) : list (ident * nat) :=
    match assoc g (x_bounds gx) with Some b => b | None => [] end.

  Definition is_obj (t : ty) : option ident :=
    match t with
    | TData On [] => find (fun Tr => eqb (obj_name Tr) On) (x_objs gx)
    | _ => None
    end.

  (** The method [m] of the trait [ti] at [Self = τs], from a dictionary. *)
  Definition trait_method (p : pos) (Γ : lctx) (ti : trinfo) (m : ident) (τs : ty) :
      result (expr * list ty * ty * ty) elab_error :=
    '(i, s) <- of_opt (method_of ti m) (EE_NoMethod p m τs) ;;
    d <- dict_of p Γ (ti_name ti) τs ;;
    let σ := tsubst (inst [τs]) in
    let ps := map σ (ms_params s) in
    Ok (field_of (ti_name ti) (nfields ti) i d (TArrow ps (σ (ms_ret s)) (σ (ms_eff s))),
        ps, σ (ms_ret s), σ (ms_eff s)).

  (** Build the object [&Tr] of a value [e : τ]. *)
  Definition make_obj (p : pos) (Γ : lctx) (Tr : ident) (τ : ty) (e : expr) :
      result expr elab_error :=
    let Γx := (None, τ) :: Γ in
    fs <- mapM (fun sm =>
                  let '(Sn, s) := sm in
                  let ps := map (tsubst (inst [τ])) (tl (ms_params s)) in
                  let Γl := List.app (map (fun t => (None, t)) ps) Γx in
                  ti <- of_opt (find_trait (x_traits gx) Sn) (EE_NotObjectSafe p Tr) ;;
                  '(mv, _, r, ε) <- trait_method p Γl ti (ms_name s) τ ;;
                  let n := List.length ps in
                  Ok (ELam ps r ε (EApp mv (EVar n :: map EVar (seq 0 n)))))
               (obj_fields (x_traits gx) Tr) ;;
    Ok (ELet e (EConstr (obj_name Tr) (obj_name Tr) [] (ETuple fs))).

  (** Promotions where an [Error] or a trait object is expected. *)
  Definition coerce_to (p : pos) (Γ : lctx) (exp : option ty) (τ : ty) (e : expr) :
      result expr elab_error :=
    match exp with
    | Some TError => Ok (up_err τ e)
    | Some t =>
        match is_obj t with
        | Some Tr => if eqb t τ then Ok e else make_obj p Γ Tr τ e
        | None => Ok e
        end
    | None => Ok e
    end.

  (** The constraint [X : Tr] (or a supertrait) of a type parameter, for
      [x.m()] and [X::m()]. *)
  Definition asm_traits (τ : ty) : list ident :=
    map (fun a => fst (fst a)) (filter (fun a => eqb (snd (fst a)) τ) (x_asm gx)).

  (** Traits declaring a method [m] whose constraint holds for [τ]. *)
  Definition traits_for (p : pos) (Γ : lctx) (m : ident) (τ : ty) : list trinfo :=
    filter (fun ti => match method_of ti m, dict_of p Γ (ti_name ti) τ with
                      | Some _, Ok _ => true
                      | _, _ => false
                      end) (x_traits gx).

  (** Dot calls on a trait method are allowed on type parameters and on the
      program's own types (as in MoonBit; not on builtin types). *)
  Definition dot_traits (τ : ty) : bool :=
    match τ with
    | TVar _ => true
    | TData T _ => negb (existsb (eqb T) ["Option"; "Ref"; "Result"; "Failure"])
    | _ => false
    end.

  Definition arrow_params (t : ty) (n : nat) : list (option ty) :=
    match t with
    | TArrow ps _ _ => if Nat.eqb (List.length ps) n then map Some ps else repeat None n
    | _ => repeat None n
    end.

  (** A global function used as a value (not called): its type arguments
      come from the expected type. *)
  Definition elab_global (p : pos) (f : ident) (fd : fdef) (exp : option ty) :
      result expr elab_error :=
    match bounds_of f, fd_tparams fd with
    | _ :: _, _ => Err (EE_Unsupported p "a function with trait bounds used as a value")
    | [], 0 => Ok (EGlobal f [])
    | [], n =>
        let s := match exp with
                 | Some t => tmatch (TArrow (fd_params fd) (fd_ret fd) (fd_eff fd)) t (repeat None n)
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
        (* a [mut] field holds a cell: read its content *)
        let (q, τr) := match τ with TRef t => (PRef PVar, t) | _ => (PVar, τ) end in
        let ps := map (fun j => if Nat.eqb j i then q else PWild) (seq 0 (List.length fs)) in
        Ok (EMatch e τr [(PConstr (cd_name cd) ps, EVar 0)])
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
          '(q, Δ1) <- match τ0 with
                      | TRef t => '(q0, Δ0) <- elab_pat t sp ;; Ok (PRef q0, Δ0)
                      | _ => elab_pat τ0 sp
                      end ;;
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
          (* a [mut] field: match the content of its cell *)
          '(q, Δ) <- match τi with
                     | TRef t => '(q0, Δ0) <- elab_pat t sp ;; Ok (PRef q0, Δ0)
                     | _ => elab_pat τi sp
                     end ;;
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
        (* on [Error], a constructor names its error type *)
        '(T, ts, up) <-
          match τ with
          | TData T ts =>
              _ <- match tq with
                   | Some T' => if eqb T T' then Ok tt else Err (EE_PatType p τ)
                   | None => Ok tt
                   end ;;
              Ok (T, ts, false)
          | TError =>
              match tq with
              | Some T => Ok (T, [], true)
              | None =>
                  match filter (fun td => td_err td && has_ctor c td) (ge_types hdr) with
                  | [td] => Ok (td_name td, [], true)
                  | [] => Err (EE_UnknownCtor p c)
                  | _ => Err (EE_AmbiguousCtor p c)
                  end
              end
          | _ => Err (EE_PatType p τ)
          end ;;
        td <- of_opt (lookup_ty hdr T) (EE_UnknownType p T) ;;
        cd <- of_opt (lookup_ctor td c) (EE_UnknownCtor p c) ;;
        '(qs, Δ) <- go p open sps (map (tsubst (inst ts)) (cd_fields cd)) ;;
        Ok ((if up then PUp T (PConstr c qs) else PConstr c qs), Δ)
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
      the body in the extended context.  Labels do not cross the function
      boundary; when the result type is known the body is wrapped in a
      block that [return] targets. *)
  Definition elab_lam (Γ : lctx) (p : pos) (ps : list (ident * option sty)) (ret : option sty)
      (eff : option (option sty)) (pexps : list (option ty)) (rexp εexp : option ty)
      (elab_body : cenv -> lctx -> option ty -> result expr elab_error) :
      result expr elab_error :=
    τs <- param_tys p ps pexps ;;
    let Γ' := List.app (combine (map (fun x => Some (fst x)) ps) τs) Γ in
    τr <- match ret with
          | Some t => map_result Some (elab_ty tys tps t)
          | None => Ok rexp
          end ;;
    (* the effect: annotation, else expectation, else [noraise] *)
    ε <- match eff, εexp with
         | Some (Some t), _ => elab_ty tys tps t
         | Some None, _ => Ok TNever
         | None, Some ε => Ok ε
         | None, None => Ok TNever
         end ;;
    match τr with
    | Some r =>
        body' <- elab_body (mk_cenv [mk_lab None LKFun [] r] ε) Γ' τr ;;
        Ok (ELam τs r ε (eblock r body'))
    | None =>
        body' <- elab_body (mk_cenv [] ε) Γ' None ;;
        r <- type_of p (mk_cenv [] ε) Γ' body' ;;
        Ok (ELam τs r ε body')
    end.

  (** A lambda whose parameter types must come from the context. *)
  Definition needs_context (e : sexpr) : bool :=
    match e with
    | SLam _ ps _ _ _ => existsb (fun xa => match snd xa with None => true | Some _ => false end) ps
    | _ => false
    end.

  (** Instantiation of a data type from the expected type. *)
  Definition data_inst (T : ident) (n : nat) (exp : option ty) : list (option ty) :=
    match exp with
    | Some t => tmatch (TData T (tvars n)) t (repeat None n)
    | None => repeat None n
    end.

  (** *** Expressions *)

  Fixpoint elab (L : cenv) (Γ : lctx) (exp : option ty) (e : sexpr) {struct e}
      : result expr elab_error :=
    (* elaborate a list against a list of expected types *)
    let fix elab_args (es : list sexpr) (exps : list (option ty)) : result (list expr) elab_error :=
      match es with
      | [] => Ok []
      | e :: es' =>
          let (x, exps') := match exps with
                            | [] => (None, [])
                            | x :: xs => (x, xs)
                            end in
          e' <- elab L Γ x e ;;
          (* an error passed where [Error] is expected is promoted *)
          e'' <- match x with
                 | Some t =>
                     if match t with
                        | TError => true
                        | _ => match is_obj t with Some _ => true | None => false end
                        end
                     then τ <- type_of (sexpr_pos e) L Γ e' ;; coerce_to (sexpr_pos e) Γ x τ e'
                     else Ok e'
                 | None => Ok e'
                 end ;;
          es2 <- elab_args es' exps' ;;
          Ok (e'' :: es2)
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
            e' <- elab L Γ ex e ;;
            s' <- match pt with
                  | Some t => τ <- type_of p L Γ e' ;; Ok (tmatch t τ s)
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
                    | SLam q lps ret leff body, Some (TArrow pps pr pε) =>
                        let pexps := if Nat.eqb (List.length pps) (List.length lps)
                                     then map (resolve s) pps
                                     else repeat None (List.length lps) in
                        elab_lam Γ q lps ret leff pexps (resolve s pr) (resolve s pε)
                                 (fun L' Γ' t => elab L' Γ' t body)
                    | _, _ => elab L Γ (match pt with Some t => resolve s t | None => None end) e
                    end
                end ;;
          s' <- match d, pt with
                | None, Some t => τ <- type_of p L Γ e' ;; Ok (tmatch t τ s)
                | _, _ => Ok s
                end ;;
          '(r, s2) <- gargs2 p es' pre' ps' s' ;;
          Ok (e' :: r, s2)
      end in
    (* A call of the global function or method [g] (signature [fd]), with an
       optional receiver already elaborated: type arguments by matching,
       then the dictionaries of its trait bounds. *)
    let fix gcall (args : list sexpr) (p q : pos) (g : ident) (fd : fdef)
        (rcv : option (expr * ty)) {struct args} : result expr elab_error :=
      let nb := bounds_of g in
      let ups := skipn (List.length nb) (fd_params fd) in
      let ps := match rcv with Some _ => tl ups | None => ups end in
      let n := fd_tparams fd in
      let s0 := match exp with
                | Some t => tmatch (fd_ret fd) t (repeat None n)
                | None => repeat None n
                end in
      let s0' := match rcv, ups with
                 | Some (_, τr), p0 :: _ => tmatch p0 τr s0
                 | _, _ => s0
                 end in
      '(pre, s1) <- gargs1 p args ps s0' ;;
      '(args', s) <- gargs2 p args pre ps s1 ;;
      ts <- of_opt (all_some s) (EE_CannotInfer q g) ;;
      ds <- mapM (fun c => dict_of q Γ (fst c) (nth (snd c) ts TUnit)) nb ;;
      let rargs := match rcv with Some (r, _) => r :: args' | None => args' end in
      Ok (promote L (tsubst (inst ts) (fd_eff fd)) (tsubst (inst ts) (fd_ret fd))
                  (EApp (EGlobal g ts) (List.app ds rargs))) in
    (* A call of the trait method [m] of [ti]: [Self] is [self] if known,
       else the type of the receiver or of the first argument, else the
       expected result. *)
    let fix tcall (args : list sexpr) (q : pos) (ti : trinfo) (m : ident) (self : option ty)
        (rcv : option (expr * ty)) {struct args} : result expr elab_error :=
      '(_, sg) <- of_opt (method_of ti m) (EE_NoMethod q m TUnit) ;;
      let call (τs : ty) (all : list expr) :=
        '(mv, _, r, ε) <- trait_method q Γ ti m τs ;;
        Ok (promote L ε r (EApp mv all)) in
      let exps (τs : ty) (ps : list ty) := map (fun t => Some (tsubst (inst [τs]) t)) ps in
      match rcv, ms_params sg, args with
      | Some (r0, τr), _ :: ps', _ =>
          args' <- elab_args args (exps τr ps') ;;
          call τr (r0 :: args')
      | Some _, [], _ => Err (EE_NoMethod q m TUnit)
      | None, TVar 0 :: ps', a0 :: rest =>
          a0' <- elab L Γ self a0 ;;
          τs <- match self with Some t => Ok t | None => type_of q L Γ a0' end ;;
          rest' <- elab_args rest (exps τs ps') ;;
          call τs (a0' :: rest')
      | None, ps, _ =>
          τs <- match self, ms_ret sg, exp with
                | Some t, _, _ => Ok t
                | None, TVar 0, Some t => Ok t
                | _, _, _ => Err (EE_CannotInfer q m)
                end ;;
          args' <- elab_args args (exps τs ps) ;;
          call τs args'
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
          (* a [mut] field holds a cell, allocated here *)
          let (τc, mut) := match τf with TRef t => (t, true) | _ => (τf, false) end in
          e' <- elab L Γ0 (resolve s τc) fe ;;
          τ <- type_of p L Γ0 e' ;;
          let e'' := if mut then EMem (MRef τ) [e'] else e' in
          let τ' := if mut then TRef τ else τ in
          '(rest, Γ1, s1) <- rfields p ((None, τ') :: Γ0) names fs fes' (tmatch τf τ' s) ;;
          Ok ((e'', i) :: rest, Γ1, s1)
      end in
    (* [x = e] for named bindings, elaborated in order *)
    let fix elab_named (L0 : cenv) (Γ0 : lctx) (tyof : ident -> option ty)
        (bs : list (ident * sexpr)) : result (list (ident * expr)) elab_error :=
      match bs with
      | [] => Ok []
      | (y, b) :: bs' =>
          b' <- elab L0 Γ0 (tyof y) b ;;
          rest <- elab_named L0 Γ0 tyof bs' ;;
          Ok ((y, b') :: rest)
      end in
    (* the type of the first arm of a [match] that does not jump away *)
    let fix first_arm (L0 : cenv) (Γ0 : lctx) (τs : ty) (cs : list (spat * sexpr)) :
        result (option ty) elab_error :=
      match cs with
      | [] => Ok None
      | (sp, b) :: cs' =>
          if diverges b then first_arm L0 Γ0 τs cs'
          else
            '(_, Δ) <- elab_pat τs sp ;;
            b' <- elab L0 (List.app Δ Γ0) None b ;;
            map_result Some (type_of (sexpr_pos b) L0 (List.app Δ Γ0) b')
      end in
    (* the arms of a [match] on [τs], with the expected result type *)
    let fix arms (L0 : cenv) (Γ0 : lctx) (τs : ty) (cs : list (spat * sexpr)) (exp : option ty) :
        result (list (pat * expr) * option ty) elab_error :=
      match cs with
      | [] => Ok ([], exp)
      | (sp, b) :: cs' =>
          '(q, Δ) <- elab_pat τs sp ;;
          let Γ' := List.app Δ Γ0 in
          b' <- elab L0 Γ' exp b ;;
          τb <- match exp with
                | Some t => Ok t
                | None => type_of (sexpr_pos b) L0 Γ' b'
                end ;;
          '(rest, r) <- arms L0 Γ0 τs cs' (Some τb) ;;
          Ok ((q, b') :: rest, r)
      end in
    match e with
    | SVar p x =>
        match lookup_local x Γ with
        | Some i =>
            match nth_error Γ i with
            | Some (_, TRef τ) => Ok (EMem (MGet τ) [EVar i])
            | _ => Ok (EVar i)
            end
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
                match fd_tparams fd, bounds_of g with
                | 0, [] =>
                    args' <- elab_args args (map Some (fd_params fd)) ;;
                    Ok (promote L (fd_eff fd) (fd_ret fd) (EApp (EGlobal g []) args'))
                | _, _ => gcall args p q g fd None
                end
            | None, None =>
                (* builtins that are not ordinary functions in Core *)
                if eqb g "not" then
                  args' <- elab_args args [Some TBool] ;;
                  Ok (EPrim PBoolNot args')
                (* [panic() : T] and [abort(msg) : T] stop the program *)
                else if eqb g "panic" then
                  match args with
                  | [] => Ok (EAbort (jty exp))
                  | _ => Err (EE_Type q (E_ArgArity 0 (List.length args)))
                  end
                else if eqb g "abort" then
                  match args with
                  | [a] =>
                      a' <- elab L Γ (Some TString) a ;;
                      τa <- type_of p L Γ a' ;;
                      if eqb τa TString then Ok (ELet a' (EAbort (jty exp)))
                      else Err (EE_Annot (sexpr_pos a) TString τa)
                  | _ => Err (EE_Type q (E_ArgArity 1 (List.length args)))
                  end
                (* [fail(msg)] raises [Failure(msg)] *)
                else if eqb g "fail" then
                  match args with
                  | [a] =>
                      a' <- elab L Γ (Some TString) a ;;
                      Ok (raise_val L (TData "Failure" [])
                                    (EConstr "Failure" "Failure" [] (ETuple [a'])) (jty exp))
                  | _ => Err (EE_Type q (E_ArgArity 1 (List.length args)))
                  end
                else if eqb g "ignore" then
                  match args with
                  | [a] => a' <- elab L Γ None a ;; Ok (ELet a' (ELit LUnit))
                  | _ => Err (EE_Unbound q g)
                  end
                else Err (EE_Unbound q g)
            | Some _, _ =>
                f' <- elab L Γ None f ;;
                τf <- type_of p L Γ f' ;;
                args' <- elab_args args (arrow_params τf (List.length args)) ;;
                match τf with
                | TArrow _ r ε => Ok (promote L ε r (EApp f' args'))
                | _ => Ok (EApp f' args')
                end
            end
        | SQual q T m =>
            (* [T::m(..)] for a method of [T], [Tr::m(..)] for a trait method,
               [X::m(..)] for a type parameter with a bound *)
            let qcall (_ : unit) :=
              let g := T ++ "::" ++ m in
              if has_meth T m then
                match lookup_fn hdr g with
                | Some fd => gcall args p q g fd None
                | None => Err (EE_Unbound q g)
                end
              else
                let with_m := filter (fun ti => match method_of ti m with
                                                | Some _ => true
                                                | None => false
                                                end) in
                match find_trait (x_traits gx) T, index_of T tps with
                | Some ti, _ => tcall args q ti m None None
                | None, Some i =>
                    match with_m (flat_map (fun Tr => match find_trait (x_traits gx) Tr with
                                                      | Some ti => [ti]
                                                      | None => []
                                                      end) (asm_traits (TVar i))) with
                    | ti :: _ => tcall args q ti m (Some (TVar i)) None
                    | [] => Err (EE_NoMethod q m (TVar i))
                    end
                | None, None =>
                    match with_m (x_traits gx) with
                    | [ti] => tcall args q ti m None None
                    | [] => Err (EE_NoMethod q m TUnit)
                    | _ => Err (EE_AmbiguousMethod q m)
                    end
                end in
            (* [Ref::new(v)], [Array::make(n, v)], [FixedArray::make(n, v)], [Array::new()] *)
            match array_kind_of T, args with
            | None, [v] =>
                if (eqb T "Ref" && eqb m "new")%bool then
                  v' <- elab L Γ (match exp with
                                  | Some (TData R [t]) => if eqb R "Ref" then Some t else None
                                  | _ => None
                                  end) v ;;
                  t <- type_of p L Γ v' ;;
                  Ok (EConstr "Ref" "Ref" [t] (ETuple [EMem (MRef t) [v']]))
                else qcall tt
            | Some k, [n; v] =>
                if eqb m "make" then
                  n' <- elab L Γ (Some TIndex) n ;;
                  v' <- elab L Γ (match exp with Some (TArray _ t) => Some t | _ => None end) v ;;
                  t <- type_of p L Γ v' ;;
                  Ok (EMem (MMake k t) [n'; v'])
                else qcall tt
            | Some k, [] =>
                if eqb m "new" then
                  match exp with
                  | Some (TArray _ t) => Ok (EMem (MArray k t 0) [])
                  | _ => Err (EE_CannotInfer q m)
                  end
                else qcall tt
            | _, _ => qcall tt
            end
        | _ =>
            f' <- elab L Γ None f ;;
            τf <- type_of p L Γ f' ;;
            args' <- elab_args args (arrow_params τf (List.length args)) ;;
            match τf with
            | TArrow _ r ε => Ok (promote L ε r (EApp f' args'))
            | _ => Ok (EApp f' args')
            end
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
        e0' <- elab L Γ None e0 ;;
        τ <- type_of p L Γ e0' ;;
        match τ with
        | TData T ts =>
            names <- of_opt (assoc T sinfo) (EE_NotRecord p τ) ;;
            i <- of_opt (index_of f names) (EE_UnknownField p f) ;;
            proj_field p T ts i e0'
        | _ => Err (EE_NotRecord p τ)
        end
    | SMatch p e0 cases =>
        e0' <- elab L Γ None e0 ;;
        τs <- type_of p L Γ e0' ;;
        exp0 <- match exp with
                | Some _ => Ok exp
                | None => first_arm L Γ τs cases
                end ;;
        '(bs, r) <- arms L Γ τs cases exp0 ;;
        τ <- of_opt r (EE_EmptyMatch p) ;;
        Ok (EMatch e0' τ bs)
    | SInfix p op a b =>
        if eqb op "&&" then
          a' <- elab L Γ (Some TBool) a ;;
          b' <- elab L Γ (Some TBool) b ;;
          Ok (EIf a' b' e_false)
        else if eqb op "||" then
          a' <- elab L Γ (Some TBool) a ;;
          b' <- elab L Γ (Some TBool) b ;;
          Ok (EIf a' e_true b')
        else
          (* the expected type only flows into arithmetic operands *)
          let exp' := match assoc op arith_ops with Some _ => exp | None => None end in
          if andb (flexible a) (negb (flexible b)) then
            b' <- elab L Γ exp' b ;;
            τ <- type_of p L Γ b' ;;
            a' <- elab L Γ (Some τ) a ;;
            elab_binop p op τ a' b'
          else
            a' <- elab L Γ exp' a ;;
            τ <- type_of p L Γ a' ;;
            b' <- elab L Γ (Some τ) b ;;
            elab_binop p op τ a' b'
    | SUnary p op a =>
        if eqb op "-" then
          match a with
          | SLit q (SLInt k z) => l' <- elab_lit q exp (SLInt k (Z.opp z)) ;; Ok (ELit l')
          | _ =>
              a' <- elab L Γ exp a ;;
              τ <- type_of p L Γ a' ;;
              match τ with
              | TBase (BInt k) => Ok (EPrim (PIntNeg k) [a'])
              | _ => Err (EE_NoOperator p op τ)
              end
          end
        else if eqb op "!" then
          a' <- elab L Γ (Some TBool) a ;;
          Ok (EPrim PBoolNot [a'])
        else Err (EE_NoOperator p op TUnit)
    | SLet p x ann e1 body =>
        τann <- match ann with
                | Some t => map_result Some (elab_ty tys tps t)
                | None => Ok None
                end ;;
        e1' <- elab L Γ τann e1 ;;
        τ0 <- type_of p L Γ e1' ;;
        e1'' <- coerce_to p Γ τann τ0 e1' ;;
        τ1 <- type_of p L Γ e1'' ;;
        _ <- match τann with
             | Some t => if eqb t τ1 then Ok tt else Err (EE_Annot p t τ1)
             | None => Ok tt
             end ;;
        body' <- elab L ((x, τ1) :: Γ) exp body ;;
        Ok (ELet e1'' body')
    | SIf p c t oe =>
        c' <- elab L Γ (Some TBool) c ;;
        match oe with
        | Some e0 =>
            if (match exp with None => true | Some _ => false end && diverges t
                && negb (diverges e0))%bool then
              e0' <- elab L Γ None e0 ;;
              τe <- type_of p L Γ e0' ;;
              t' <- elab L Γ (Some τe) t ;;
              Ok (EIf c' t' e0')
            else
            t' <- elab L Γ exp t ;;
            exp' <- match exp with
                    | Some τ => Ok (Some τ)
                    | None => map_result Some (type_of p L Γ t')
                    end ;;
            e0' <- elab L Γ exp' e0 ;;
            Ok (EIf c' t' e0')
        | None =>
            t' <- elab L Γ (Some TUnit) t ;;
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
        e0' <- elab L Γ None e0 ;;
        τ <- type_of p L Γ e0' ;;
        match τ with
        | TData T ts => proj_field p T ts i e0'      (* tuple struct *)
        | _ => Ok (EProj e0' i)
        end
    | SLam p ps ret eff body =>
        let pexps := match exp with
                     | Some t => arrow_params t (List.length ps)
                     | None => repeat None (List.length ps)
                     end in
        let rexp := match exp with Some (TArrow _ r _) => Some r | _ => None end in
        let εexp := match exp with Some (TArrow _ _ ε) => Some ε | _ => None end in
        elab_lam Γ p ps ret eff pexps rexp εexp (fun L' Γ' t => elab L' Γ' t body)
    | SAnnot p e0 t =>
        τ <- elab_ty tys tps t ;;
        e0' <- elab L Γ (Some τ) e0 ;;
        τ1 <- type_of p L Γ e0' ;;
        e0'' <- coerce_to p Γ (Some τ) τ1 e0' ;;
        τ0 <- type_of p L Γ e0'' ;;
        if eqb τ τ0 then Ok e0'' else Err (EE_Annot p τ τ0)
    (* ---- milestone M3 ---- *)
    | SLetMut p x ann e1 body =>
        τann <- match ann with
                | Some t => map_result Some (elab_ty tys tps t)
                | None => Ok None
                end ;;
        e1' <- elab L Γ τann e1 ;;
        τ1 <- type_of p L Γ e1' ;;
        _ <- match τann with
             | Some t => if eqb t τ1 then Ok tt else Err (EE_Annot p t τ1)
             | None => Ok tt
             end ;;
        body' <- elab L ((Some x, TRef τ1) :: Γ) exp body ;;
        Ok (ELet (EMem (MRef τ1) [e1']) body')
    | SAssign p x op e0 =>
        i <- of_opt (lookup_local x Γ) (EE_NotMutable p x) ;;
        match nth_error Γ i with
        | Some (_, TRef τ) =>
            v' <- elab L Γ (Some τ) e0 ;;
            v'' <- match op with
                   | None => Ok v'
                   | Some o => elab_binop p o τ (EMem (MGet τ) [EVar i]) v'
                   end ;;
            Ok (EMem (MSet τ) [EVar i; v''])
        | _ => Err (EE_NotMutable p x)
        end
    | SArray p es =>
        match exp, es with
        | Some (TArray k t), _ =>
            es' <- elab_args es (repeat (Some t) (List.length es)) ;;
            Ok (EMem (MArray k t (List.length es)) es')
        | _, e1 :: es1 =>
            e1' <- elab L Γ None e1 ;;
            t <- type_of p L Γ e1' ;;
            es1' <- elab_args es1 (repeat (Some t) (List.length es1)) ;;
            Ok (EMem (MArray AGrow t (List.length es)) (e1' :: es1'))
        | _, [] => Err (EE_CannotInfer p "[]")
        end
    | SIndex p a i =>
        a' <- elab L Γ None a ;;
        τa <- type_of p L Γ a' ;;
        match τa with
        | TArray k t =>
            i' <- elab L Γ (Some TIndex) i ;;
            Ok (EMem (MIndex k t) [a'; i'])
        | _ => Err (EE_NoMethod p "[]" τa)
        end
    | SIndexSet p a i op v =>
        a' <- elab L Γ None a ;;
        τa <- type_of p L Γ a' ;;
        match τa with
        | TArray k t =>
            match op with
            | None =>
                i' <- elab L Γ (Some TIndex) i ;;
                v' <- elab L Γ (Some t) v ;;
                Ok (EMem (MSetIndex k t) [a'; i'; v'])
            | Some o =>
                (* [a] and [i] are evaluated once *)
                let Γ1 := (None, τa) :: Γ in
                i' <- elab L Γ1 (Some TIndex) i ;;
                let Γ2 := (None, TIndex) :: Γ1 in
                v' <- elab L Γ2 (Some t) v ;;
                rhs <- elab_binop p o t (EMem (MIndex k t) [EVar 1; EVar 0]) v' ;;
                Ok (ELet a' (ELet i' (EMem (MSetIndex k t) [EVar 1; EVar 0; rhs])))
            end
        | _ => Err (EE_NoMethod p "[]=" τa)
        end
    | SFieldSet p e0 f op v =>
        e0' <- elab L Γ None e0 ;;
        τ <- type_of p L Γ e0' ;;
        match τ with
        | TData T ts =>
            names <- of_opt (assoc T sinfo) (EE_NotRecord p τ) ;;
            i <- of_opt (index_of f names) (EE_UnknownField p f) ;;
            td <- of_opt (lookup_ty hdr T) (EE_UnknownType p T) ;;
            match td_ctors td with
            | [cd] =>
                let fs := map (tsubst (inst ts)) (cd_fields cd) in
                match nth_error fs i with
                | Some (TRef t) =>
                    (* bind the field's cell, then write it *)
                    let Γ1 := (None, TRef t) :: Γ in
                    v' <- elab L Γ1 (Some t) v ;;
                    rhs <- match op with
                           | None => Ok v'
                           | Some o => elab_binop p o t (EMem (MGet t) [EVar 0]) v'
                           end ;;
                    let ps := map (fun j => if Nat.eqb j i then PVar else PWild)
                                  (seq 0 (List.length fs)) in
                    Ok (EMatch e0' TUnit [(PConstr (cd_name cd) ps, EMem (MSet t) [EVar 0; rhs])])
                | _ => Err (EE_NotMutable p f)
                end
            | _ => Err (EE_NotRecord p τ)
            end
        | _ => Err (EE_NotRecord p τ)
        end
    | SMethod p e0 m args =>
        e0' <- elab L Γ None e0 ;;
        τ <- type_of p L Γ e0' ;;
        (* 2. a trait object: call its closure; 3. a trait method, on a type
           parameter or on one of the program's own types *)
        let via_trait (_ : unit) :=
          match is_obj τ with
          | Some Tr =>
              let fs := obj_fields (x_traits gx) Tr in
              match find (fun js => eqb (ms_name (snd (snd js))) m)
                         (combine (seq 0 (List.length fs)) fs) with
              | Some (j, (_, sg)) =>
                  args' <- elab_args args (map Some (tl (ms_params sg))) ;;
                  Ok (promote L (ms_eff sg) (ms_ret sg)
                        (EApp (field_of (obj_name Tr) (List.length fs) j e0' (obj_field_ty sg)) args'))
              | None => Err (EE_NoMethod p m τ)
              end
          | None =>
              if dot_traits τ then
                match traits_for p Γ m τ with
                | [ti] => tcall args p ti m None (Some (e0', τ))
                | [] => Err (EE_NoMethod p m τ)
                | _ => Err (EE_AmbiguousMethod p m)
                end
              else Err (EE_NoMethod p m τ)
          end in
        (* 1. a method [fn T::m] of the type *)
        let general (_ : unit) :=
          match head_name τ with
          | Some H =>
              if has_meth H m then
                match lookup_fn hdr (H ++ "::" ++ m) with
                | Some fd => gcall args p p (H ++ "::" ++ m) fd (Some (e0', τ))
                | None => Err (EE_Unbound p m)
                end
              else via_trait tt
          | None => via_trait tt
          end in
        match τ, args with
        | TArray k t, [] =>
            if eqb m "length" then Ok (EMem (MLength k t) [e0']) else general tt
        | TArray AGrow t, [a] =>
            if eqb m "push" then
              a' <- elab L Γ (Some t) a ;;
              Ok (EMem (MPush t) [e0'; a'])
            else general tt
        | _, _ => general tt
        end
    | SQual p T m => Err (EE_NoMethod p m TUnit)
    | SWhile p x c body nb =>
        (* the loop's condition and [nobreak] see it as a transparent entry *)
        let hd τ := push_lab (mk_lab None LKHead [] τ) L in
        τ <- match nb with
             | None => Ok TUnit
             | Some e0 =>
                 match exp with
                 | Some t => Ok t
                 | None => e0' <- elab (hd TUnit) Γ None e0 ;; type_of p (hd TUnit) Γ e0'
                 end
             end ;;
        c' <- elab (hd τ) Γ (Some TBool) c ;;
        body' <- elab (push_lab (mk_lab x LKWhile [] τ) L) Γ (Some TUnit) body ;;
        nb' <- match nb with
               | Some e0 => elab (hd τ) Γ (Some τ) e0
               | None => Ok (ELit LUnit)
               end ;;
        Ok (ELoop (ETuple []) [] τ
                  (EIf c' (ELet body' (EJump CCont 0 (ETuple []) τ)) nb'))
    | SFor p x inits c upds body nb =>
        inits' <- elab_named L Γ (fun _ => None) inits ;;
        τs <- mapM (fun b => type_of p L Γ (snd b)) inits' ;;
        let names := map fst inits in
        let Γ' := List.app (combine (map Some names) τs) Γ in
        let hd τ := push_lab (mk_lab None LKHead τs τ) L in
        τ <- match nb, c with
             | None, Some _ => Ok TUnit
             | None, None => Ok (jty exp)
             | Some e0, _ =>
                 match exp with
                 | Some t => Ok t
                 | None => e0' <- elab (hd TUnit) Γ' None e0 ;; type_of p (hd TUnit) Γ' e0'
                 end
             end ;;
        c' <- match c with
              | Some c0 => map_result Some (elab (hd τ) Γ' (Some TBool) c0)
              | None => Ok None
              end ;;
        (* the body is a block: [continue] without arguments leaves it *)
        body' <- elab (push_lab (mk_lab x LKForBody [] TUnit) (hd τ)) Γ' (Some TUnit) body ;;
        (* the next values of the loop variables, after the body's binder *)
        let Γ'' := (None, TUnit) :: Γ' in
        upds' <- elab_named (hd τ) Γ'' (fun y => assoc y (combine names τs)) upds ;;
        let next := map (fun i => match assoc (nth i names "") upds' with
                                  | Some u => u
                                  | None => EVar (S i)
                                  end) (seq 0 (List.length names)) in
        let step := ELet (eblock TUnit body') (EJump CCont 0 (ETuple next) τ) in
        nb' <- match nb with
               | Some e0 => elab (hd τ) Γ' (Some τ) e0
               | None => Ok (ELit LUnit)
               end ;;
        Ok (ELoop (ETuple (map snd inits')) τs τ
                  (match c' with Some c0 => EIf c0 step nb' | None => step end))
    | SBlock p x body =>
        let τ := jty exp in
        body' <- elab (push_lab (mk_lab (Some x) LKBlock [] τ) L) Γ (Some τ) body ;;
        Ok (eblock τ body')
    | SBreak p x arg =>
        '(k, τt) <- of_opt (break_target x (ce_labs L) 0) (EE_NoTarget p) ;;
        a' <- match arg with
              | Some a => elab L Γ (Some τt) a
              | None => Ok (ELit LUnit)
              end ;;
        Ok (EJump CBreak k a' (jty exp))
    | SContinue p x args =>
        tgt <- of_opt (cont_target_of x (ce_labs L) 0) (EE_NoTarget p) ;;
        match tgt, args with
        | CTWhile k, [] => Ok (EJump CCont k (ETuple []) (jty exp))
        | CTWhile _, _ => Err (EE_BadContinue p 0 (List.length args))
        | CTFor k _, [] => Ok (EJump CBreak k (ELit LUnit) (jty exp))
        | CTFor k ps, _ =>
            if Nat.eqb (List.length ps) (List.length args) then
              args' <- elab_args args (map Some ps) ;;
              Ok (EJump CCont (S k) (ETuple args') (jty exp))
            else Err (EE_BadContinue p (List.length ps) (List.length args))
        (* [for .. in]: leave the body (the state block then applies the
           update clauses), or give the next state directly *)
        | CTForIn k _, [] => Ok (EJump CBreak k (ELit LUnit) (jty exp))
        | CTForIn k ss, _ =>
            if Nat.eqb (List.length ss) (List.length args) then
              args' <- elab_args args (map Some ss) ;;
              Ok (EJump CBreak (S k) (ETuple args') (jty exp))
            else Err (EE_BadContinue p (List.length ss) (List.length args))
        end
    | SReturn p arg =>
        '(k, r) <- of_opt (return_target (ce_labs L) 0) (EE_NoTarget p) ;;
        a' <- match arg with
              | Some a =>
                  a' <- elab L Γ (Some r) a ;;
                  τa <- type_of p L Γ a' ;;
                  coerce_to p Γ (Some r) τa a'
              | None => Ok (ELit LUnit)
              end ;;
        Ok (EJump CBreak k a' (jty exp))
    | SForIn p x pats src inits upds body nb =>
        (* the source, bound to two hidden variables: [e1] in [Γ], [e2] under [e1] *)
        let array_src :=
          a' <- elab L Γ None src ;;
          τa <- type_of p L Γ a' ;;
          match τa with
          | TArray k t => Ok (a', EMem (MLength k t) [EVar 0], IArray k t)
          | _ => Err (EE_NoMethod p "iter" τa)
          end in
        '(e1, e2, it) <-
          match src with
          | SInfix q op lo hi =>
              match range_op op with
              | Some rk =>
                  (* the start fixes the integer type, as in MoonBit *)
                  lo' <- elab L Γ None lo ;;
                  τk <- type_of q L Γ lo' ;;
                  hi' <- elab L ((None, τk) :: Γ) (Some τk) hi ;;
                  match τk with
                  | TBase (BInt kk) => Ok (lo', hi', IRange rk kk)
                  | _ => Err (EE_NoOperator q op τk)
                  end
              | None => array_src
              end
          | _ => array_src
          end ;;
        let '(τ1, τ2, ivs, start, incl) :=
          match it with
          | IRange rk kk =>
              let incl := match rk with RUpIncl | RDownIncl => true | _ => false end in
              (TInt kk, TInt kk,
               (if incl then [TInt kk; TBool] else [TInt kk]), EVar 1, incl)
          | IArray k t => (TArray k t, TIndex, [TIndex], ELit (LInt I32 0), false)
          end in
        let Γo := (None, τ2) :: (None, τ1) :: Γ in
        (* the state variables *)
        inits' <- elab_named L Γo (fun _ => None) inits ;;
        τs <- mapM (fun b => type_of p L Γo (snd b)) inits' ;;
        let names := map fst inits in
        let ps := List.app ivs τs in
        let n := List.length ps in
        let Γl := List.app (List.app (map (fun t => (None, t)) ivs)
                                     (combine (map Some names) τs)) Γo in
        let hd τ := push_lab (mk_lab None LKHead ps τ) L in
        τ <- match nb with
             | None => Ok TUnit
             | Some e0 =>
                 match exp with
                 | Some t => Ok t
                 | None => e0' <- elab (hd TUnit) Γl None e0 ;; type_of p (hd TUnit) Γl e0'
                 end
             end ;;
        (* condition and element, in [Γl]: the position is [EVar 0], the
           [done] flag of an inclusive range [EVar 1], the bound [EVar n] *)
        let v := EVar 0 in
        let bound := EVar n in
        let '(cond, elem, τe) :=
          match it with
          | IRange RUpExcl kk => (icmp CLt kk v bound, v, TInt kk)
          | IRange RUpIncl kk => (EIf (EVar 1) e_false (icmp CLe kk v bound), v, TInt kk)
          | IRange RDownExcl kk => (icmp CGt kk v bound, iarith ASub kk v (int1 kk), TInt kk)
          | IRange RDownIncl kk => (EIf (EVar 1) e_false (icmp CGe kk v bound), v, TInt kk)
          | IArray k t => (icmp CLt I32 v bound, EMem (MIndex k t) [EVar (S n); v], t)
          end in
        '(q, Δ, scrut) <-
          match pats, it with
          | [sp], _ => '(q, Δ) <- elab_pat τe sp ;; Ok (q, Δ, elem)
          | [sp1; sp2], IArray _ _ =>
              '(q1, Δ1) <- elab_pat TIndex sp1 ;;
              '(q2, Δ2) <- elab_pat τe sp2 ;;
              Ok (PTuple [q1; q2], List.app Δ1 Δ2, ETuple [v; elem])
          | _, _ => Err (EE_PatType p τe)
          end ;;
        let d := List.length Δ in
        let Γb := List.app Δ Γl in
        (* the body is a block inside the block that computes the next state *)
        let st := push_lab (mk_lab None LKHead [] (TTuple τs)) (hd τ) in
        body' <- elab (push_lab (mk_lab x LKForInBody [] TUnit) st) Γb (Some TUnit) body ;;
        let Γu := (None, TUnit) :: Γb in
        upds' <- elab_named st Γu (fun y => assoc y (combine names τs)) upds ;;
        let state := map (fun j => match assoc (nth j names "") upds' with
                                   | Some u => u
                                   | None => EVar (1 + d + List.length ivs + j)
                                   end) (seq 0 (List.length names)) in
        let blk := eblock (TTuple τs) (ELet (eblock TUnit body') (ETuple state)) in
        (* after the state block: the position is [EVar (1 + d)], the bound
           [EVar (1 + d + n)]; inclusive ranges stop at the bound without
           stepping past it *)
        let vv := EVar (1 + d) in
        let bb := EVar (1 + d + n) in
        let next_iv :=
          match it with
          | IRange RUpExcl kk => [iarith AAdd kk vv (int1 kk)]
          | IRange RDownExcl kk => [iarith ASub kk vv (int1 kk)]
          | IRange RUpIncl kk =>
              [EIf (icmp CEq kk vv bb) vv (iarith AAdd kk vv (int1 kk)); icmp CEq kk vv bb]
          | IRange RDownIncl kk =>
              [EIf (icmp CEq kk vv bb) vv (iarith ASub kk vv (int1 kk)); icmp CEq kk vv bb]
          | IArray _ _ => [iarith AAdd I32 vv (int1 I32)]
          end in
        let next := List.app next_iv (map (fun j => EProj (EVar 0) j) (seq 0 (List.length names))) in
        let step := ELet blk (EJump CCont 0 (ETuple next) τ) in
        nb' <- match nb with
               | Some e0 => elab (hd τ) Γl (Some τ) e0
               | None => Ok (ELit LUnit)
               end ;;
        let init := List.app (if incl then [start; e_false] else [start]) (map snd inits') in
        Ok (ELet e1 (ELet e2
              (ELoop (ETuple init) ps τ (EIf cond (EMatch scrut τ [(q, step)]) nb'))))
    (* ---- milestone M4: errors ---- *)
    | SRaise p e0 =>
        e0' <- elab L Γ (match ce_exn L with TError => None | ρ => Some ρ end) e0 ;;
        τ <- type_of p L Γ e0' ;;
        Ok (raise_val L τ e0' (jty exp))
    | STryBang p body =>
        let L' := set_exn TError L in
        body' <- elab L' Γ exp body ;;
        τ0 <- type_of p L' Γ body' ;;
        Ok (ETry body' TError (EAbort τ0) (EVar 0))
    | STry p body cases nr =>
        let bexp := match nr with None => exp | Some _ => None end in
        (* the error type of the body: named by the patterns, or the only
           error type the body type-checks with, else [Error] *)
        let info :=
          fold_left
            (fun acc (c : spat * sexpr) =>
               let one T := match acc with
                            | CINone => CIOne T
                            | CIOne T' => if eqb T T' then acc else CIMany
                            | CIMany => CIMany
                            end in
               match fst c with
               | SPConstr _ (Some T) _ _ _ => one T
               | SPConstr _ None cn _ _ =>
                   match filter (fun td => td_err td && has_ctor cn td) (ge_types hdr) with
                   | [td] => one (td_name td)
                   | _ => acc
                   end
               | _ => acc
               end) cases CINone in
        let errs := filter td_err (ge_types hdr) in
        τe <- match info with
              | CIOne T => Ok (TData T [])
              | CIMany => Ok TError
              | CINone =>
                  let ok td :=
                    let Lt := set_exn (TData (td_name td) []) L in
                    match elab Lt Γ bexp body with
                    | Ok b' => match type_of p Lt Γ b' with Ok _ => true | Err _ => false end
                    | Err _ => false
                    end in
                  match filter ok errs with
                  | [td] => Ok (TData (td_name td) [])
                  | _ => Ok TError
                  end
              end ;;
        let Lb := set_exn τe L in
        body' <- elab Lb Γ bexp body ;;
        τ0 <- type_of p Lb Γ body' ;;
        (* the handler and the [noraise] arms *)
        let Γh := (None, τe) :: Γ in
        hexp <- match exp, nr with
                | Some t, _ => Ok (Some t)
                | None, None => Ok (Some τ0)
                | None, Some _ => first_arm L Γh τe cases
                end ;;
        '(hbs, r) <- arms L Γh τe cases hexp ;;
        τ <- of_opt r (EE_EmptyMatch p) ;;
        k <- match nr with
             | None => Ok (EVar 0)
             | Some ncs =>
                 '(kbs, _) <- arms L ((None, τ0) :: Γ) τ0 ncs (Some τ) ;;
                 Ok (EMatch (EVar 0) τ kbs)
             end ;;
        Ok (ETry body' τe (EMatch (EVar 0) τ hbs) k)
    | SAs p e0 Tr =>
        e0' <- elab L Γ None e0 ;;
        τ <- type_of p L Γ e0' ;;
        if existsb (eqb Tr) (x_objs gx) then make_obj p Γ Tr τ e0'
        else Err (EE_NotObjectSafe p Tr)
    | SDefer p onerr c body =>
        (* the cleanup may raise but not jump *)
        let Lc := mk_cenv [] (ce_exn L) in
        c' <- elab Lc Γ (Some TUnit) c ;;
        τc <- type_of p Lc Γ c' ;;
        _ <- if eqb τc TUnit then Ok tt else Err (EE_Annot (sexpr_pos c) TUnit τc) ;;
        body' <- elab L Γ exp body ;;
        Ok (EDefer onerr c' body')
    end.
End Elab.

(** ** Programs *)

Definition elab_tdef (tys : list (ident * nat)) (st : stype) : result tdef elab_error :=
  let tps := st_tparams st in
  let n := List.length tps in
  match st_body st with
  | SDEnum cs =>
      cds <- mapM (fun c => τs <- mapM (elab_ty tys tps) (snd c) ;; Ok (mk_cdef (fst c) τs)) cs ;;
      Ok (mk_tdef (st_name st) n cds false)
  | SDError cs =>
      cds <- mapM (fun c => τs <- mapM (elab_ty tys tps) (snd c) ;; Ok (mk_cdef (fst c) τs)) cs ;;
      Ok (mk_tdef (st_name st) n cds true)
  | SDStruct fs =>
      (* a [mut] field holds a cell *)
      τs <- mapM (fun (f : ident * bool * sty) => τ <- elab_ty tys tps (snd f) ;;
                           Ok (if snd (fst f) then TRef τ else τ)) fs ;;
      Ok (mk_tdef (st_name st) n [mk_cdef (st_name st) τs] false)
  | SDTupleStruct ts =>
      τs <- mapM (elab_ty tys tps) ts ;;
      Ok (mk_tdef (st_name st) n [mk_cdef (st_name st) τs] false)
  end.

(** Does the type mention the name [x] (used for [raise?])? *)
Fixpoint sty_mentions (x : ident) (t : sty) {struct t} : bool :=
  let fix go (ts : list sty) : bool :=
    match ts with
    | [] => false
    | t :: ts' => (sty_mentions x t || go ts')%bool
    end in
  match t with
  | SName _ n args => (eqb n x || go args)%bool
  | STuple _ ts => go ts
  | SArrow _ ps r eff =>
      (go ps || sty_mentions x r || match eff with Some t => sty_mentions x t | None => false end)%bool
  | SObj _ _ => false
  end.

(** The type parameters of a signature: a [raise?] signature has a hidden
    last one, the error type it raises ([?]). *)
Definition sig_tparams (f : sfun) : list ident :=
  let poly := (existsb (fun xt => sty_mentions "?" (snd xt)) (sf_params f)
               || match sf_eff f with Some t => sty_mentions "?" t | None => false end)%bool in
  if poly then List.app (sf_tparams f) ["?"] else sf_tparams f.

(** The global name of a function or method. *)
Definition fun_name (f : sfun) : ident :=
  match sf_self f with
  | Some T => T ++ "::" ++ sf_name f
  | None => sf_name f
  end.

(** Trait bounds [(X, Tr)] as constraints [(Tr, index of X)]. *)
Definition bound_ctx (p : pos) (tps : list ident) (bs : list (ident * ident)) :
    result (list (ident * nat)) elab_error :=
  mapM (fun b => i <- of_opt (index_of (fst b) tps) (EE_UnknownType p (fst b)) ;; Ok (snd b, i)) bs.

Definition dict_ty (c : ident * nat) : ty := TData (fst c) [TVar (snd c)].

Definition elab_sig (tys : list (ident * nat)) (f : sfun) : result fdef elab_error :=
  let tps := sig_tparams f in
  ctx <- bound_ctx (sf_pos f) tps (sf_bounds f) ;;
  τs <- mapM (fun xt => elab_ty tys tps (snd xt)) (sf_params f) ;;
  τ <- match sf_ret f with
       | Some t => elab_ty tys tps t
       | None => Ok TUnit
       end ;;
  ε <- match sf_eff f with
       | Some t => elab_ty tys tps t
       | None => Ok TNever
       end ;;
  Ok (mk_fdef (fun_name f) (List.length tps) (List.app (map dict_ty ctx) τs) τ ε (ELit LUnit)).

(** The body of a definition with trait bounds [ctx] on the type
    parameters [tps]: the dictionary parameters are named, their
    supertrait dictionaries are bound by [let]s around the body (which is
    wrapped in the block that [return] targets). *)
Definition elab_body tys hdr sinfo tps (gx : xenv) (ctx : list (ident * nat)) (Γp : lctx)
    (r ε : ty) (body : sexpr) : result expr elab_error :=
  let named := map (fun c => (fst c, nth (snd c) tps "", snd c)) ctx in
  let lets := super_lets (x_traits gx) (List.length (x_traits gx) * S (List.length ctx)) []
                         named in
  let Γd := map (fun c => (Some (dict_var (fst c) (nth (snd c) tps "")), dict_ty c)) ctx in
  let Γ0 := List.app Γd Γp in
  (* the supertrait dictionaries, outermost first *)
  let fix bind (ls : list (ident * ident * nat * ident * nat)) (Γ : lctx) :
      result (list expr * lctx) elab_error :=
    match ls with
    | [] => Ok ([], Γ)
    | (Sn, X, i, T, j) :: ls' =>
        k <- of_opt (lookup_local (dict_var T X) Γ) (EE_Unbound (mk_pos 0%N 0%N) (dict_var T X)) ;;
        ti <- of_opt (find_trait (x_traits gx) T) (EE_UnknownType (mk_pos 0%N 0%N) T) ;;
        let e := field_of T (nfields ti) j (EVar k) (TData Sn [TVar i]) in
        '(es, Γ') <- bind ls' ((Some (dict_var Sn X), TData Sn [TVar i]) :: Γ) ;;
        Ok (e :: es, Γ')
    end in
  '(es, Γ) <- bind lets Γ0 ;;
  let asm := List.app (map (fun c => (fst c, TVar (snd c), dict_var (fst c) (nth (snd c) tps ""))) ctx)
                      (map (fun l => let '(Sn, X, i, _, _) := l in (Sn, TVar i, dict_var Sn X)) lets) in
  let gx' := mk_xenv (x_traits gx) (x_insts gx) (x_bounds gx) (x_meths gx) (x_objs gx) asm in
  b <- elab tys hdr sinfo tps gx' (mk_cenv [mk_lab None LKFun [] r] ε) Γ (Some r) body ;;
  Ok (fold_right ELet (eblock r b) es).

Definition elab_fun tys hdr sinfo gx (f : sfun) (sig : fdef) : result fdef elab_error :=
  let tps := sig_tparams f in
  ctx <- bound_ctx (sf_pos f) tps (sf_bounds f) ;;
  let Γp := combine (map (fun xt => Some (fst xt)) (sf_params f))
                    (skipn (List.length ctx) (fd_params sig)) in
  b <- elab_body tys hdr sinfo tps gx ctx Γp (fd_ret sig) (fd_eff sig) (sf_body f) ;;
  Ok (mk_fdef (fd_name sig) (fd_tparams sig) (fd_params sig) (fd_ret sig) (fd_eff sig) b).

Fixpoint elab_funs tys hdr sinfo gx (fs : list sfun) (sigs : list fdef) : result (list fdef) elab_error :=
  match fs, sigs with
  | f :: fs', sig :: sigs' =>
      fd <- elab_fun tys hdr sinfo gx f sig ;;
      fds <- elab_funs tys hdr sinfo gx fs' sigs' ;;
      Ok (fd :: fds)
  | _, _ => Ok []
  end.

(** ** Traits and impls *)

Definition elab_trait (tys : list (ident * nat)) (t : strait) : result trinfo elab_error :=
  ms <- mapM (fun m =>
                ps <- mapM (elab_ty tys ["Self"]) (sm_params m) ;;
                r <- elab_ty tys ["Self"] (sm_ret m) ;;
                ε <- match sm_eff m with
                     | Some t => elab_ty tys ["Self"] t
                     | None => Ok TNever
                     end ;;
                Ok (mk_msig (sm_name m) ps r ε)) (str_methods t) ;;
  Ok (mk_trinfo (str_name t) (str_supers t) ms (map sm_name (filter sm_default (str_methods t)))).

(** The [impl]s of one trait for one type, grouped. *)
Record igroup : Type := mk_igroup {
  ig_pos     : pos;
  ig_trait   : ident;
  ig_head    : ty;
  ig_tparams : list ident;
  ig_bounds  : list (ident * ident);
  ig_methods : list simethod
}.

Fixpoint add_impl (gs : list igroup) (p : pos) (Tr : ident) (τ : ty) (tps : list ident)
    (bs : list (ident * ident)) (m : option simethod) : list igroup :=
  match gs with
  | [] => [mk_igroup p Tr τ tps bs (match m with Some m => [m] | None => [] end)]
  | g :: gs' =>
      if (eqb (ig_trait g) Tr && eqb (ig_head g) τ)%bool
      then mk_igroup (ig_pos g) Tr τ (ig_tparams g) (ig_bounds g)
                     (List.app (ig_methods g) (match m with Some m => [m] | None => [] end)) :: gs'
      else g :: add_impl gs' p Tr τ tps bs m
  end.

Definition inst_name (Tr H : ident) : ident := "inst$" ++ Tr ++ "$" ++ H.
Definition impl_name (Tr H m : ident) : ident := "impl$" ++ Tr ++ "$" ++ H ++ "$" ++ m.
Definition default_name (Tr m : ident) : ident := "default$" ++ Tr ++ "$" ++ m.

(** An instance group, checked: its head, constraints and signatures. *)
Record iinfo : Type := mk_iinfo {
  ii_group : igroup;
  ii_ti    : trinfo;
  ii_name  : ident;                (** the head's type name *)
  ii_ctx   : list (ident * nat);
  ii_idef  : idef
}.

Definition check_group (trs : list trinfo) (g : igroup) : result iinfo elab_error :=
  let p := ig_pos g in
  let n := List.length (ig_tparams g) in
  ti <- of_opt (find_trait trs (ig_trait g)) (EE_UnknownType p (ig_trait g)) ;;
  '(h, args) <- of_opt (head_args (ig_head g)) (EE_Unsupported p "impl for this type") ;;
  _ <- if eqb args (map TVar (seq 0 n)) then Ok tt
       else Err (EE_Unsupported p "impl head (type parameters in order)") ;;
  H <- of_opt (head_name (ig_head g)) (EE_Unsupported p "impl for this type") ;;
  ctx <- bound_ctx p (ig_tparams g) (ig_bounds g) ;;
  (* every method must be implemented, or have a default *)
  _ <- mapM (fun s =>
               if existsb (fun im => eqb (sim_name im) (ms_name s)) (ig_methods g)
                  || existsb (eqb (ms_name s)) (ti_defaults ti)
               then Ok tt else Err (EE_MissingMethod p (ig_trait g) (ms_name s)))
            (ti_methods ti) ;;
  _ <- if NoDup_dec (map sim_name (ig_methods g)) then Ok tt else Err (EE_Overlap p) ;;
  _ <- mapM (fun im => match method_of ti (sim_name im) with
                       | Some _ => Ok tt
                       | None => Err (EE_NoMethod p (sim_name im) (ig_head g))
                       end) (ig_methods g) ;;
  Ok (mk_iinfo g ti H ctx (mk_idef (ig_trait g) h n ctx (inst_name (ig_trait g) H))).

(** The signatures generated for an instance: its methods and its
    dictionary function. *)
Definition group_sigs (ii : iinfo) : list fdef :=
  let g := ii_group ii in
  let σ := tsubst (inst [ig_head g]) in
  let n := List.length (ig_tparams g) in
  let dicts := map dict_ty (ii_ctx ii) in
  mk_fdef (inst_name (ig_trait g) (ii_name ii)) n dicts (TData (ig_trait g) [ig_head g]) TNever (ELit LUnit)
  :: flat_map (fun im => match method_of (ii_ti ii) (sim_name im) with
                         | Some (_, s) =>
                             [mk_fdef (impl_name (ig_trait g) (ii_name ii) (sim_name im)) n
                                      (List.app dicts (map σ (ms_params s))) (σ (ms_ret s))
                                      (σ (ms_eff s)) (ELit LUnit)]
                         | None => []
                         end) (ig_methods g).

(** The dictionary function of an instance. *)
Definition inst_body (insts : list idef) (trs : list trinfo) (defaults : list (ident * ident))
    (ii : iinfo) : result expr elab_error :=
  let g := ii_group ii in
  let ti := ii_ti ii in
  let p := ig_pos g in
  let n := List.length (ig_tparams g) in
  let nc := List.length (ii_ctx ii) in
  let tvars := map TVar (seq 0 n) in
  let τh := ig_head g in
  let σ := tsubst (inst [τh]) in
  let Θ := map (fun jc => (fst (snd jc), TVar (snd (snd jc)), EVar (fst jc)))
               (combine (seq 0 nc) (ii_ctx ii)) in
  sups <- mapM (fun S => match entails_dec insts Θ S τh with
                         | inleft (exist _ d _) => Ok d
                         | inright _ => Err (EE_NoInstance p S τh)
                         end) (ti_supers ti) ;;
  ms <- mapM (fun s =>
                let ps := map σ (ms_params s) in
                let k := List.length ps in
                let lvars := map EVar (seq 0 k) in
                let dvars := map (fun j => EVar (k + j)) (seq 0 nc) in
                if existsb (fun im => eqb (sim_name im) (ms_name s)) (ig_methods g) then
                  Ok (ELam ps (σ (ms_ret s)) (σ (ms_eff s))
                        (EApp (EGlobal (impl_name (ig_trait g) (ii_name ii) (ms_name s)) tvars)
                              (List.app dvars lvars)))
                else
                  let self := EApp (EGlobal (inst_name (ig_trait g) (ii_name ii)) tvars) dvars in
                  Ok (ELam ps (σ (ms_ret s)) (σ (ms_eff s))
                        (EApp (EGlobal (default_name (ig_trait g) (ms_name s)) [τh]) (self :: lvars))))
             (ti_methods ti) ;;
  Ok (EConstr (ig_trait g) (ig_trait g) [τh] (ETuple (List.app sups ms))).

(** The automatic instance of each trait [S] of an object type [&Tr]. *)
Definition obj_insts (trs : list trinfo) (Tr : ident) : list (idef * fdef) :=
  let On := obj_name Tr in
  map (fun Sn => (mk_idef Sn (HData On) 0 [] (inst_name Sn On),
                  mk_fdef (inst_name Sn On) 0 [] (TData Sn [TData On []]) TNever (ELit LUnit)))
      (closure trs Tr).

Definition obj_inst_body (insts : list idef) (trs : list trinfo) (Tr Sn : ident) :
    result expr elab_error :=
  let On := obj_name Tr in
  let τo := TData On [] in
  let fs := obj_fields trs Tr in
  ti <- of_opt (find_trait trs Sn) (EE_UnknownType (mk_pos 0%N 0%N) Sn) ;;
  sups <- mapM (fun S' => match entails_dec insts [] S' τo with
                          | inleft (exist _ d _) => Ok d
                          | inright _ => Err (EE_NoInstance (mk_pos 0%N 0%N) S' τo)
                          end) (ti_supers ti) ;;
  ms <- mapM (fun s =>
                j <- of_opt (index_of (ms_name s) (map (fun sm => ms_name (snd sm)) fs))
                            (EE_NotObjectSafe (mk_pos 0%N 0%N) Tr) ;;
                let ps := tl (ms_params s) in
                let k := List.length ps in
                Ok (ELam (τo :: ps) (ms_ret s) (ms_eff s)
                      (EApp (field_of On (List.length fs) j (EVar 0) (obj_field_ty s))
                            (map EVar (seq 1 k)))))
             (ti_methods ti) ;;
  Ok (EConstr Sn Sn [τo] (ETuple (List.app sups ms))).

(** ** Programs *)

(** The entry expression is the body of [fn main] (checked against [Unit]),
    or [()] when there is none.  [Option], [Ref], [Result] and [Failure]
    are predeclared. *)
Definition elab_prog (sp : sprog) : result (genv * expr) elab_error :=
  let trnames := map str_name (sp_traits sp) in
  let tys := List.app [("Option", 1); ("Ref", 1); ("Result", 2); ("Failure", 0)]
               (List.app (map (fun st => (st_name st, List.length (st_tparams st))) (sp_types sp))
                  (List.app (map (fun n => (n, 1)) trnames)
                            (map (fun n => (obj_name n, 0)) trnames))) in
  let sinfo := ("Ref", ["val"]) :: flat_map (fun st => match st_body st with
                                   | SDStruct fs => [(st_name st, map (fun f => fst (fst f)) fs)]
                                   | _ => []
                                   end) (sp_types sp) in
  trs <- mapM (elab_trait tys) (sp_traits sp) ;;
  let objs := filter (obj_safe trs) trnames in
  tds <- mapM (elab_tdef tys) (sp_types sp) ;;
  let types := List.app [option_tdef; ref_tdef; result_tdef; failure_tdef]
                 (List.app tds (List.app (map dict_tdef trs) (map (obj_tdef trs) objs))) in
  (* impls: grouped by trait and type; default implementations apart *)
  groups <- fold_left
              (fun acc i =>
                 gs <- acc ;;
                 match si_self i with
                 | Some t => τ <- elab_ty tys (si_tparams i) t ;;
                             Ok (add_impl gs (si_pos i) (si_trait i) τ (si_tparams i) (si_bounds i)
                                          (si_method i))
                 | None => Ok gs
                 end) (sp_impls sp) (Ok []) ;;
  iis <- mapM (check_group trs) groups ;;
  let defaults := flat_map (fun i => match si_self i, si_method i with
                                     | None, Some m => [(si_trait i, m)]
                                     | _, _ => []
                                     end) (sp_impls sp) in
  dsigs <- mapM (fun tm =>
                   let '(Tr, im) := tm in
                   ti <- of_opt (find_trait trs Tr) (EE_UnknownType (mk_pos 0%N 0%N) Tr) ;;
                   '(_, s) <- of_opt (method_of ti (sim_name im)) (EE_NoMethod (mk_pos 0%N 0%N) (sim_name im) TUnit) ;;
                   Ok (mk_fdef (default_name Tr (sim_name im)) 1
                               (TData Tr [TVar 0] :: ms_params s) (ms_ret s) (ms_eff s) (ELit LUnit)))
                defaults ;;
  let oinsts := flat_map (obj_insts trs) objs in
  let insts := List.app (map ii_idef iis) (map fst oinsts) in
  _ <- if coherent_dec insts then Ok tt else Err (EE_Overlap (mk_pos 0%N 0%N)) ;;
  (* signatures *)
  sigs <- mapM (elab_sig tys) (sp_funs sp) ;;
  let gsigs := flat_map group_sigs iis in
  let hdr := mk_genv types (List.app sigs (List.app gsigs (List.app dsigs (map snd oinsts)))) in
  let bounds := List.app
    (flat_map (fun f => match bound_ctx (sf_pos f) (sig_tparams f) (sf_bounds f) with
                        | Ok ctx => [(fun_name f, ctx)]
                        | Err _ => []
                        end) (sp_funs sp))
    (List.app
       (flat_map (fun ii => map (fun im => (impl_name (ig_trait (ii_group ii)) (ii_name ii) (sim_name im),
                                            ii_ctx ii))
                                (ig_methods (ii_group ii))) iis)
       (flat_map (fun ii => [(inst_name (ig_trait (ii_group ii)) (ii_name ii), ii_ctx ii)]) iis)) in
  let meths := flat_map (fun f => match sf_self f with Some T => [(T, sf_name f)] | None => [] end)
                        (sp_funs sp) in
  let gx := mk_xenv trs insts bounds meths objs [] in
  (* bodies *)
  funs <- elab_funs tys hdr sinfo gx (sp_funs sp) sigs ;;
  imfs <- mapM (fun ii =>
                  let g := ii_group ii in
                  let σ := tsubst (inst [ig_head g]) in
                  mapM (fun im =>
                          '(_, s) <- of_opt (method_of (ii_ti ii) (sim_name im))
                                            (EE_NoMethod (ig_pos g) (sim_name im) TUnit) ;;
                          let ps := map σ (ms_params s) in
                          _ <- if Nat.eqb (List.length (sim_params im)) (List.length ps) then Ok tt
                               else Err (EE_Type (ig_pos g) (E_ArgArity (List.length ps)
                                                                        (List.length (sim_params im)))) ;;
                          let Γp := combine (map (fun x => Some (fst x)) (sim_params im)) ps in
                          b <- elab_body tys hdr sinfo (ig_tparams g) gx (ii_ctx ii) Γp
                                         (σ (ms_ret s)) (σ (ms_eff s)) (sim_body im) ;;
                          Ok (mk_fdef (impl_name (ig_trait g) (ii_name ii) (sim_name im))
                                      (List.length (ig_tparams g))
                                      (List.app (map dict_ty (ii_ctx ii)) ps)
                                      (σ (ms_ret s)) (σ (ms_eff s)) b))
                       (ig_methods g)) iis ;;
  ifs <- mapM (fun ii =>
                 let g := ii_group ii in
                 b <- inst_body insts trs [] ii ;;
                 Ok (mk_fdef (inst_name (ig_trait g) (ii_name ii)) (List.length (ig_tparams g))
                             (map dict_ty (ii_ctx ii)) (TData (ig_trait g) [ig_head g]) TNever b)) iis ;;
  dfs <- mapM (fun tm =>
                 let '(Tr, im) := tm in
                 ti <- of_opt (find_trait trs Tr) (EE_UnknownType (mk_pos 0%N 0%N) Tr) ;;
                 '(_, s) <- of_opt (method_of ti (sim_name im)) (EE_NoMethod (mk_pos 0%N 0%N) (sim_name im) TUnit) ;;
                 let Γp := combine (map (fun x => Some (fst x)) (sim_params im)) (ms_params s) in
                 b <- elab_body tys hdr sinfo ["Self"] gx [(Tr, 0)] Γp (ms_ret s) (ms_eff s) (sim_body im) ;;
                 Ok (mk_fdef (default_name Tr (sim_name im)) 1 (TData Tr [TVar 0] :: ms_params s)
                             (ms_ret s) (ms_eff s) b)) defaults ;;
  ofs <- mapM (fun Tr =>
                 mapM (fun Sn =>
                         b <- obj_inst_body insts trs Tr Sn ;;
                         Ok (mk_fdef (inst_name Sn (obj_name Tr)) 0 [] (TData Sn [TData (obj_name Tr) []])
                                     TNever b)) (closure trs Tr)) objs ;;
  main <- match sp_main sp with
          | Some e =>
              elab_body tys hdr sinfo [] gx [] [] TUnit TNever
                        (SAnnot (sexpr_pos e) e (SName (sexpr_pos e) "Unit" []))
          | None => Ok (ELit LUnit)
          end ;;
  Ok (mk_genv types (List.app funs (List.app (List.concat imfs) (List.app ifs (List.app dfs (List.concat ofs))))),
      main).
