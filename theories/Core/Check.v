(** * Core IR: type checker, correct by construction

    [infer ge Σ Λ Γ e : result {τ | Γ ⊢[ge;Σ;Λ] e : τ} type_error]

    Every successful answer carries a typing derivation, so soundness of the
    checker holds by construction.  The derivations live in [Prop] and are
    erased by extraction: the extracted checker just returns the type.
    Completeness and decidability are proved in [CheckComplete.v].

    Recursion is structural on the expression; lists of sub-expressions are
    handled by [infer_list]/[check_list], which take the element checker as
    an argument and are unfolded by the guard checker (nested recursion). *)

From Stdlib Require Import List Arith PeanoNat.
From MoonRocq.Prelude Require Import Result EqDec Ident ListDec.
From MoonRocq.Core Require Import Syntax Prim Subst Typing.
Import ListNotations.

Inductive type_error : Type :=
| E_UnboundVar      (x : nat)
| E_UnknownGlobal   (f : ident)
| E_TypeArgArity    (f : ident) (expected got : nat)
| E_Mismatch        (expected got : ty)
| E_NotFunction     (t : ty)
| E_ArgArity        (expected got : nat)
| E_NotTuple        (t : ty)
| E_TupleIndex      (i : nat) (t : ty)
| E_DuplicateGlobal
| E_InGlobal        (f : ident) (e : type_error)
| E_UnknownType     (T : ident)
| E_UnknownCtor     (T c : ident)
| E_NotData         (t : ty)
| E_PatArity        (expected got : nat)
| E_DuplicateType
| E_DuplicateCtor
| E_IllFormed       (t : ty)
| E_InType          (T : ident) (e : type_error)
| E_NotRef          (t : ty)
| E_UnboundLoc      (l : nat)
| E_UnknownLabel    (k : nat)
| E_Effect          (ε ρ : ty)        (** raising [ε] where only [ρ] may escape *)
| E_NotError        (T : ident).

(** ** Certified building blocks *)

Definition of_option {A E} (o : option A) (err : E) : result {a | o = Some a} E :=
  match o as o' return result {a | o' = Some a} E with
  | Some a => Ok (exist _ a eq_refl)
  | None => Err err
  end.

Definition expect_ty (expected got : ty) : result (expected = got) type_error :=
  match ty_eq_dec expected got with
  | left H => Ok H
  | right _ => Err (E_Mismatch expected got)
  end.

Definition expect_nat (expected got : nat) (err : type_error) : result (got = expected) type_error :=
  match Nat.eq_dec got expected with
  | left H => Ok H
  | right _ => Err err
  end.

Definition as_arrow (t : ty) :
    result {ps : list ty & {r : ty & {ε : ty | t = TArrow ps r ε}}} type_error :=
  match t as t' return result {ps : list ty & {r : ty & {ε : ty | t' = TArrow ps r ε}}} type_error with
  | TArrow ps r ε => Ok (existT _ ps (existT _ r (exist _ ε eq_refl)))
  | t' => Err (E_NotFunction t')
  end.

Definition expect_eff (ε ρ : ty) : result (eff_le ε ρ) type_error :=
  match ty_eq_dec ε TNever with
  | left H => Ok (or_introl H)
  | right _ =>
      match ty_eq_dec ε ρ with
      | left H => Ok (or_intror H)
      | right _ => Err (E_Effect ε ρ)
      end
  end.

Definition check_bool (b : bool) (err : type_error) : result (b = true) type_error :=
  match b as b' return result (b' = true) type_error with
  | true => Ok eq_refl
  | false => Err err
  end.

Definition as_tuple (t : ty) : result {ts : list ty | t = TTuple ts} type_error :=
  match t as t' return result {ts : list ty | t' = TTuple ts} type_error with
  | TTuple ts => Ok (exist _ ts eq_refl)
  | t' => Err (E_NotTuple t')
  end.

Definition as_ref (t : ty) : result {u : ty | t = TRef u} type_error :=
  match t as t' return result {u : ty | t' = TRef u} type_error with
  | TRef u => Ok (exist _ u eq_refl)
  | t' => Err (E_NotRef t')
  end.

Definition as_data (t : ty) : result {T : ident & {ts : list ty | t = TData T ts}} type_error :=
  match t as t' return result {T : ident & {ts : list ty | t' = TData T ts}} type_error with
  | TData T ts => Ok (existT _ T (exist _ ts eq_refl))
  | t' => Err (E_NotData t')
  end.

Lemma ctor_fields_intro ge T c ts td cd :
  lookup_ty ge T = Some td -> lookup_ctor td c = Some cd ->
  ctor_fields ge T c ts = Some (map (tsubst (inst ts)) (cd_fields cd)).
Proof. intros H1 H2; unfold ctor_fields; now rewrite H1, H2. Qed.

Lemma cast_pat {ge p τ τ' Δ} : ⊢ᵖ[ge] p : τ ⇝ Δ -> τ = τ' -> ⊢ᵖ[ge] p : τ' ⇝ Δ.
Proof. intros H ->; exact H. Defined.

Lemma cast_ty {ge Σ Λ Γ e τ τ'} : Γ ⊢[ge;Σ;Λ] e : τ -> τ = τ' -> Γ ⊢[ge;Σ;Λ] e : τ'.
Proof. intros H ->; exact H. Defined.

Section Check.
  Variables (ge : genv) (Σ : styping).

  (** Synthesise the types of a list of expressions. *)
  Definition infer_list (Λ : cctx) (Γ : ctx)
      (inf : forall e, result {τ | Γ ⊢[ge;Σ;Λ] e : τ} type_error) :
      forall es, result {τs | Γ ⊢*[ge;Σ;Λ] es : τs} type_error :=
    fix go es :=
      match es as es' return result {τs | Γ ⊢*[ge;Σ;Λ] es' : τs} type_error with
      | [] => Ok (exist _ [] (Ts_nil ge Σ Λ Γ))
      | e :: es' =>
          '(exist _ τ H) <- inf e ;;
          '(exist _ τs Hs) <- go es' ;;
          Ok (exist _ (τ :: τs) (Ts_cons ge Σ Λ Γ e es' τ τs H Hs))
      end.

  (** Check a list of expressions against a list of expected types.  Callers
      compare the lengths first, so that an arity error reports the totals. *)
  Definition check_list (Λ : cctx) (Γ : ctx)
      (inf : forall e, result {τ | Γ ⊢[ge;Σ;Λ] e : τ} type_error) :
      forall es τs, result (Γ ⊢*[ge;Σ;Λ] es : τs) type_error :=
    fix go es τs :=
      match es as es', τs as τs' return result (Γ ⊢*[ge;Σ;Λ] es' : τs') type_error with
      | [], [] => Ok (Ts_nil ge Σ Λ Γ)
      | e :: es', τ :: τs' =>
          '(exist _ τe He) <- inf e ;;
          Heq <- expect_ty τ τe ;;
          Hs <- go es' τs' ;;
          Ok (Ts_cons ge Σ Λ Γ e es' τ τs' (cast_ty He (eq_sym Heq)) Hs)
      | es', τs' => Err (E_ArgArity (length τs') (length es'))
      end.

  (** ** Patterns *)

  Definition check_pats (cp : forall p τ, result {Δ | ⊢ᵖ[ge] p : τ ⇝ Δ} type_error) :
      forall ps τs, result {Δ | ⊢ᵖ*[ge] ps : τs ⇝ Δ} type_error :=
    fix go ps τs :=
      match ps as ps', τs as τs' return result {Δ | ⊢ᵖ*[ge] ps' : τs' ⇝ Δ} type_error with
      | [], [] => Ok (exist _ [] (Ps_nil ge))
      | p :: ps', τ :: τs' =>
          '(exist _ Δ1 H1) <- cp p τ ;;
          '(exist _ Δ2 H2) <- go ps' τs' ;;
          Ok (exist _ (Δ1 ++ Δ2) (Ps_cons ge p ps' τ τs' Δ1 Δ2 H1 H2))
      | ps', τs' => Err (E_PatArity (length τs') (length ps'))
      end.

  Fixpoint check_pat (p : pat) (τ : ty) {struct p} : result {Δ | ⊢ᵖ[ge] p : τ ⇝ Δ} type_error :=
    match p as p' return result {Δ | ⊢ᵖ[ge] p' : τ ⇝ Δ} type_error with
    | PWild => Ok (exist _ [] (P_Wild ge τ))
    | PVar => Ok (exist _ [τ] (P_Var ge τ))
    | PLit l =>
        Heq <- expect_ty τ (TBase (lit_ty l)) ;;
        Ok (exist _ [] (cast_pat (P_Lit ge l) (eq_sym Heq)))
    | PTuple ps =>
        '(exist _ τs Et) <- as_tuple τ ;;
        _ <- expect_nat (length τs) (length ps) (E_PatArity (length τs) (length ps)) ;;
        '(exist _ Δ H) <- check_pats check_pat ps τs ;;
        Ok (exist _ Δ (cast_pat (P_Tuple ge ps τs Δ H) (eq_sym Et)))
    | PConstr c ps =>
        '(existT _ T (exist _ ts Ed)) <- as_data τ ;;
        '(exist _ td Htd) <- of_option (lookup_ty ge T) (E_UnknownType T) ;;
        '(exist _ cd Hcd) <- of_option (lookup_ctor td c) (E_UnknownCtor T c) ;;
        _ <- expect_nat (length (cd_fields cd)) (length ps)
               (E_PatArity (length (cd_fields cd)) (length ps)) ;;
        '(exist _ Δ H) <- check_pats check_pat ps (map (tsubst (inst ts)) (cd_fields cd)) ;;
        Ok (exist _ Δ (cast_pat (P_Constr ge c ps T ts _ Δ
                                   (ctor_fields_intro ge T c ts td cd Htd Hcd) H)
                                (eq_sym Ed)))
    | PRef p0 =>
        '(exist _ τ0 Et) <- as_ref τ ;;
        '(exist _ Δ H) <- check_pat p0 τ0 ;;
        Ok (exist _ Δ (cast_pat (P_Ref ge p0 τ0 Δ H) (eq_sym Et)))
    | PUp T p0 =>
        Heq <- expect_ty TError τ ;;
        '(exist _ Δ H) <- check_pat p0 (TData T []) ;;
        Ok (exist _ Δ (cast_pat (P_Up ge T p0 Δ H) Heq))
    end.

  (** ** Branches of a [match] *)

  Definition check_branches (Λ : cctx)
      (inf : forall Γ e, result {τ | Γ ⊢[ge;Σ;Λ] e : τ} type_error)
      (Γ : ctx) (τs τ : ty) : forall bs, result (Γ ⊢ᵇ[ge;Σ;Λ] bs : τs ⇒ τ) type_error :=
    fix go bs :=
      match bs as bs' return result (Γ ⊢ᵇ[ge;Σ;Λ] bs' : τs ⇒ τ) type_error with
      | [] => Ok (Bs_nil ge Σ Λ Γ τs τ)
      | (p, b) :: bs' =>
          '(exist _ Δ Hp) <- check_pat p τs ;;
          '(exist _ τb Hb) <- inf (Δ ++ Γ) b ;;
          Heq <- expect_ty τ τb ;;
          Hbs <- go bs' ;;
          Ok (Bs_cons ge Σ Λ Γ p b bs' τs τ Δ Hp (cast_ty Hb (eq_sym Heq)) Hbs)
      end.

  (** ** Expressions *)

  Fixpoint infer (Λ : cctx) (Γ : ctx) (e : expr) {struct e}
      : result {τ | Γ ⊢[ge;Σ;Λ] e : τ} type_error :=
    match e as e' return result {τ | Γ ⊢[ge;Σ;Λ] e' : τ} type_error with
    | EVar x =>
        '(exist _ τ H) <- of_option (nth_error Γ x) (E_UnboundVar x) ;;
        Ok (exist _ τ (T_Var ge Σ Λ Γ x τ H))
    | EGlobal f ts =>
        '(exist _ fd Hf) <- of_option (lookup_fn ge f) (E_UnknownGlobal f) ;;
        Hlen <- expect_nat (fd_tparams fd) (length ts)
                  (E_TypeArgArity f (fd_tparams fd) (length ts)) ;;
        Ok (exist _ _ (T_Global ge Σ Λ Γ f ts fd Hf Hlen))
    | ELit l =>
        Ok (exist _ _ (T_Lit ge Σ Λ Γ l))
    | ELam ps r ε b =>
        '(exist _ τb Hb) <- infer (mk_cctx [] ε) (ps ++ Γ) b ;;
        Heq <- expect_ty r τb ;;
        Ok (exist _ _ (T_Lam ge Σ Λ Γ ps r ε b (cast_ty Hb (eq_sym Heq))))
    | EApp f args =>
        '(exist _ τf Hf) <- infer Λ Γ f ;;
        '(existT _ ps (existT _ r (exist _ ε Ef))) <- as_arrow τf ;;
        _ <- expect_nat (length ps) (length args) (E_ArgArity (length ps) (length args)) ;;
        Hargs <- check_list Λ Γ (infer Λ Γ) args ps ;;
        Heff <- expect_eff ε (cc_exn Λ) ;;
        Ok (exist _ r (T_App ge Σ Λ Γ f args ps r ε (cast_ty Hf Ef) Hargs Heff))
    | ELet e1 e2 =>
        '(exist _ τ1 H1) <- infer Λ Γ e1 ;;
        '(exist _ τ2 H2) <- infer Λ (τ1 :: Γ) e2 ;;
        Ok (exist _ τ2 (T_Let ge Σ Λ Γ e1 e2 τ1 τ2 H1 H2))
    | EIf c t e0 =>
        '(exist _ τc Hc) <- infer Λ Γ c ;;
        Hb <- expect_ty TBool τc ;;
        '(exist _ τt Ht) <- infer Λ Γ t ;;
        '(exist _ τe He) <- infer Λ Γ e0 ;;
        Heq <- expect_ty τt τe ;;
        Ok (exist _ τt (T_If ge Σ Λ Γ c t e0 τt (cast_ty Hc (eq_sym Hb)) Ht
                              (cast_ty He (eq_sym Heq))))
    | ETuple es =>
        '(exist _ τs Hs) <- infer_list Λ Γ (infer Λ Γ) es ;;
        Ok (exist _ _ (T_Tuple ge Σ Λ Γ es τs Hs))
    | EProj e0 i =>
        '(exist _ τ0 H0) <- infer Λ Γ e0 ;;
        '(exist _ τs Et) <- as_tuple τ0 ;;
        '(exist _ τ Hi) <- of_option (nth_error τs i) (E_TupleIndex i τ0) ;;
        Ok (exist _ τ (T_Proj ge Σ Λ Γ e0 i τs τ (cast_ty H0 Et) Hi))
    | EConstr T c ts e0 =>
        '(exist _ td Htd) <- of_option (lookup_ty ge T) (E_UnknownType T) ;;
        Hlen <- expect_nat (td_tparams td) (length ts)
                  (E_TypeArgArity T (td_tparams td) (length ts)) ;;
        '(exist _ cd Hcd) <- of_option (lookup_ctor td c) (E_UnknownCtor T c) ;;
        '(exist _ τe He) <- infer Λ Γ e0 ;;
        Heq <- expect_ty (TTuple (map (tsubst (inst ts)) (cd_fields cd))) τe ;;
        Ok (exist _ (TData T ts)
                  (T_Constr ge Σ Λ Γ T c ts e0 td cd Htd Hlen Hcd (cast_ty He (eq_sym Heq))))
    | EMatch e0 τ bs =>
        '(exist _ τs H0) <- infer Λ Γ e0 ;;
        Hbs <- check_branches Λ (fun Γ' e' => infer Λ Γ' e') Γ τs τ bs ;;
        Ok (exist _ τ (T_Match ge Σ Λ Γ e0 τs τ bs H0 Hbs))
    | EPrim op args =>
        _ <- expect_nat (length (fst (prim_sig op))) (length args)
               (E_ArgArity (length (fst (prim_sig op))) (length args)) ;;
        Hargs <- check_list Λ Γ (infer Λ Γ) args (fst (prim_sig op)) ;;
        Ok (exist _ _ (T_Prim ge Σ Λ Γ op args Hargs))
    | ELoc l =>
        '(exist _ s H) <- of_option (nth_error Σ l) (E_UnboundLoc l) ;;
        Ok (exist _ _ (T_Loc ge Σ Λ Γ l s H))
    | EMem op args =>
        _ <- expect_nat (length (fst (mem_sig op))) (length args)
               (E_ArgArity (length (fst (mem_sig op))) (length args)) ;;
        Hargs <- check_list Λ Γ (infer Λ Γ) args (fst (mem_sig op)) ;;
        Ok (exist _ _ (T_Mem ge Σ Λ Γ op args Hargs))
    | ELoop e0 ps τ b =>
        '(exist _ τ0 H0) <- infer Λ Γ e0 ;;
        Heq0 <- expect_ty (TTuple ps) τ0 ;;
        '(exist _ τb Hb) <- infer (push_lbl (ps, τ) Λ) (ps ++ Γ) b ;;
        Heq <- expect_ty τ τb ;;
        Ok (exist _ τ (T_Loop ge Σ Λ Γ e0 ps τ b (cast_ty H0 (eq_sym Heq0))
                              (cast_ty Hb (eq_sym Heq))))
    | EJump c k e0 τ =>
        '(exist _ lbl Hk) <- of_option (nth_error (cc_lbls Λ) k) (E_UnknownLabel k) ;;
        '(exist _ τ0 H0) <- infer Λ Γ e0 ;;
        Heq <- expect_ty (ctl_ty c lbl) τ0 ;;
        Ok (exist _ τ (T_Jump ge Σ Λ Γ c k e0 τ lbl Hk (cast_ty H0 (eq_sym Heq))))
    | EAbort τ =>
        Ok (exist _ τ (T_Abort ge Σ Λ Γ τ))
    | EUp T e0 =>
        '(exist _ td Htd) <- of_option (lookup_ty ge T) (E_UnknownType T) ;;
        Herr <- check_bool (td_err td) (E_NotError T) ;;
        '(exist _ τ0 H0) <- infer Λ Γ e0 ;;
        Heq <- expect_ty (TData T []) τ0 ;;
        Ok (exist _ TError (T_Up ge Σ Λ Γ T e0 td Htd Herr (cast_ty H0 (eq_sym Heq))))
    | ERaise e0 τ =>
        '(exist _ τe H0) <- infer Λ Γ e0 ;;
        Heff <- expect_eff τe (cc_exn Λ) ;;
        Ok (exist _ τ (T_Raise ge Σ Λ Γ e0 τe τ H0 Heff))
    | ETry e0 τe h k =>
        '(exist _ τ0 H0) <- infer (with_exn τe Λ) Γ e0 ;;
        '(exist _ τ Hh) <- infer Λ (τe :: Γ) h ;;
        '(exist _ τk Hk) <- infer Λ (τ0 :: Γ) k ;;
        Heq <- expect_ty τ τk ;;
        Ok (exist _ τ (T_Try ge Σ Λ Γ e0 τe h k τ0 τ H0 Hh (cast_ty Hk (eq_sym Heq))))
    | EDefer b c e0 =>
        '(exist _ τc Hc) <- infer (mk_cctx [] (cc_exn Λ)) Γ c ;;
        '(exist _ τ H0) <- infer Λ Γ e0 ;;
        Ok (exist _ τ (T_Defer ge Σ Λ Γ b c e0 τc τ Hc H0))
    end.
End Check.

(** ** Global environment *)

(** Function bodies are checked with no store locations and no enclosing
    loops ([fdef_ok]). *)
Definition check_fdef (ge : genv) (fd : fdef) : result (fdef_ok ge fd) type_error :=
  map_err (E_InGlobal (fd_name fd))
    ('(exist _ τ H) <- infer ge [] (mk_cctx [] (fd_eff fd)) (fd_params fd) (fd_body fd) ;;
     Heq <- expect_ty (fd_ret fd) τ ;;
     Ok (cast_ty H (eq_sym Heq))).

Fixpoint check_fdefs (ge : genv) (fds : list fdef) : result (Forall (fdef_ok ge) fds) type_error :=
  match fds as fds' return result (Forall (fdef_ok ge) fds') type_error with
  | [] => Ok (Forall_nil _)
  | fd :: fds' =>
      H <- check_fdef ge fd ;;
      Hs <- check_fdefs ge fds' ;;
      Ok (Forall_cons fd H Hs)
  end.

Definition check_all {A} (P : A -> Prop) (f : forall a, result (P a) type_error) :
    forall l, result (Forall P l) type_error :=
  fix go l :=
    match l as l' return result (Forall P l') type_error with
    | [] => Ok (Forall_nil _)
    | a :: l' =>
        H <- f a ;;
        Hs <- go l' ;;
        Ok (Forall_cons a H Hs)
    end.

Definition check_nodup (l : list ident) (err : type_error) : result (NoDup l) type_error :=
  match NoDup_dec l with
  | left H => Ok H
  | right _ => Err err
  end.

Definition check_wf (ge : genv) (n : nat) (t : ty) : result (ty_wf ge n t) type_error :=
  check_bool (ty_wfb ge n t) (E_IllFormed t).

Definition check_tdef (ge : genv) (td : tdef) : result (tdef_ok ge td) type_error :=
  map_err (E_InType (td_name td))
    (Hn <- check_nodup (map cd_name (td_ctors td)) E_DuplicateCtor ;;
     Hf <- check_all (fun cd => Forall (ty_wf ge (td_tparams td)) (cd_fields cd))
             (fun cd => check_all (ty_wf ge (td_tparams td)) (check_wf ge (td_tparams td))
                          (cd_fields cd))
             (td_ctors td) ;;
     Ok (conj Hn Hf)).

Definition check_fsig (ge : genv) (fd : fdef) : result (fsig_ok ge fd) type_error :=
  map_err (E_InGlobal (fd_name fd))
    (Hp <- check_all (ty_wf ge (fd_tparams fd)) (check_wf ge (fd_tparams fd)) (fd_params fd) ;;
     Hr <- check_wf ge (fd_tparams fd) (fd_ret fd) ;;
     He <- check_bool (err_wfb ge (fd_tparams fd) (fd_eff fd)) (E_IllFormed (fd_eff fd)) ;;
     Ok (conj Hp (conj Hr He))).

Definition check_genv (ge : genv) : result (genv_ok ge) type_error :=
  Ht <- check_nodup (map td_name (ge_types ge)) E_DuplicateType ;;
  Htd <- check_all (tdef_ok ge) (check_tdef ge) (ge_types ge) ;;
  Hn <- check_nodup (map fd_name (ge_funs ge)) E_DuplicateGlobal ;;
  Hs <- check_all (fsig_ok ge) (check_fsig ge) (ge_funs ge) ;;
  Hf <- check_fdefs ge (ge_funs ge) ;;
  Ok (conj Ht (conj Htd (conj Hn (conj Hs Hf)))).
