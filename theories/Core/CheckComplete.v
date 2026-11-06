(** * Completeness of the Core checker, and decidability of typing

    Soundness of [infer] holds by construction (it returns derivations).
    Here we prove the converse: whenever [has_type ge Γ e τ] is derivable,
    [infer] succeeds with exactly [τ].  Together they give decidability of
    [has_type] and [genv_ok], and uniqueness of types. *)

From Stdlib Require Import List.
From MoonRocq.Prelude Require Import Result EqDec Ident ListDec.
From MoonRocq.Core Require Import Syntax Prim Subst Typing Check.
Import ListNotations.

(** ** Building blocks succeed on good inputs *)

Lemma of_option_some {A E} (o : option A) a (err : E) :
  o = Some a -> exists H, of_option o err = Ok (exist _ a H).
Proof. intros ->; simpl; eauto. Qed.

Lemma expect_ty_ok τ τ' : τ = τ' -> exists H, expect_ty τ τ' = Ok H.
Proof.
  intros <-; unfold expect_ty. destruct (ty_eq_dec τ τ) as [H|H]; eauto. now contradiction H.
Qed.

Lemma expect_nat_ok n m err : m = n -> exists H, expect_nat n m err = Ok H.
Proof.
  intros <-; unfold expect_nat. destruct (PeanoNat.Nat.eq_dec m m) as [H|H]; eauto.
  now contradiction H.
Qed.

(* Rewrite a sub-computation with a known successful result. *)
Local Ltac step_ok H :=
  let p := fresh "p" in let E := fresh "E" in
  destruct H as [p E]; rewrite E; cbn [bind as_arrow as_tuple].

Section Complete.
  Variable ge : genv.

  Theorem infer_complete_mut :
    (forall Γ e τ, Γ ⊢[ge] e : τ ->
       exists H, infer ge Γ e = Ok (exist _ τ H)) /\
    (forall Γ es τs, Γ ⊢*[ge] es : τs ->
       (exists H, infer_list ge Γ (infer ge Γ) es = Ok (exist _ τs H)) /\
       (exists H, check_list ge Γ (infer ge Γ) es τs = Ok H)).
  Proof.
    apply has_type_mutind; intros; cbn [infer].
    - (* T_Var *)
      step_ok (of_option_some _ _ (E_UnboundVar x) H). eauto.
    - (* T_Global *)
      step_ok (of_option_some _ _ (E_UnknownGlobal f) H).
      step_ok (expect_nat_ok (fd_tparams fd) (length ts)
                 (E_TypeArgArity f (fd_tparams fd) (length ts)) H0).
      eauto.
    - (* T_Lit *)
      eauto.
    - (* T_Lam *)
      step_ok H0. step_ok (expect_ty_ok r r eq_refl). eauto.
    - (* T_App *)
      step_ok H0.
      step_ok (expect_nat_ok (length ps) (length args) (E_ArgArity (length ps) (length args))
                 (has_types_length _ _ _ _ H1)).
      destruct H2 as [_ H2]. step_ok H2. eauto.
    - (* T_Let *)
      step_ok H0. step_ok H2. eauto.
    - (* T_If *)
      step_ok H0. step_ok (expect_ty_ok TBool TBool eq_refl).
      step_ok H2. step_ok H4. step_ok (expect_ty_ok τ τ eq_refl). eauto.
    - (* T_Tuple *)
      destruct H0 as [H0 _]. step_ok H0. eauto.
    - (* T_Proj *)
      step_ok H0. step_ok (of_option_some _ _ (E_TupleIndex i (TTuple τs)) H1). eauto.
    - (* T_Prim *)
      step_ok (expect_nat_ok _ _ (E_ArgArity (length (fst (prim_sig op))) (length args))
                 (has_types_length _ _ _ _ H)).
      destruct H0 as [_ H0]. step_ok H0. eauto.
    - (* Ts_nil *)
      split; eexists; reflexivity.
    - (* Ts_cons *)
      destruct H2 as [Hl Hc]. split.
      + cbn [infer_list]. step_ok H0. fold (infer_list ge Γ (infer ge Γ) es).
        step_ok Hl. eauto.
      + cbn [check_list]. step_ok H0. step_ok (expect_ty_ok τ τ eq_refl).
        fold (check_list ge Γ (infer ge Γ) es τs).
        step_ok Hc. eauto.
  Qed.

  Theorem infer_complete Γ e τ :
    Γ ⊢[ge] e : τ -> exists H, infer ge Γ e = Ok (exist _ τ H).
  Proof. apply (proj1 infer_complete_mut). Qed.

  (** Types are unique (the checker is a function). *)
  Corollary has_type_unique Γ e τ1 τ2 :
    Γ ⊢[ge] e : τ1 -> Γ ⊢[ge] e : τ2 -> τ1 = τ2.
  Proof.
    intros H1 H2.
    destruct (infer_complete _ _ _ H1) as [p1 E1].
    destruct (infer_complete _ _ _ H2) as [p2 E2].
    rewrite E1 in E2. now inversion E2.
  Qed.

  (** ** Decidability *)

  Definition has_type_dec Γ e τ : {Γ ⊢[ge] e : τ} + {~ Γ ⊢[ge] e : τ}.
  Proof.
    destruct (infer ge Γ e) as [[τ' H]|err] eqn:E.
    - destruct (ty_eq_dec τ' τ) as [<-|Hne]; [left; exact H | right].
      intros Ht. destruct (infer_complete _ _ _ Ht) as [p E'].
      rewrite E in E'. inversion E'. contradiction.
    - right. intros Ht. destruct (infer_complete _ _ _ Ht) as [p E'].
      rewrite E in E'. discriminate.
  Defined.

  (** Whether an expression is typable at all. *)
  Definition typable_dec Γ e :
    {τ | Γ ⊢[ge] e : τ} + {forall τ, ~ Γ ⊢[ge] e : τ}.
  Proof.
    destruct (infer ge Γ e) as [p|err] eqn:E; [left; exact p | right].
    intros τ Ht. destruct (infer_complete _ _ _ Ht) as [p E'].
    rewrite E in E'. discriminate.
  Defined.

  (** ** Global environments *)

  Lemma check_fdef_complete fd : fdef_ok ge fd -> exists H, check_fdef ge fd = Ok H.
  Proof.
    intros Hfd; unfold check_fdef.
    step_ok (infer_complete _ _ _ Hfd).
    step_ok (expect_ty_ok (fd_ret fd) (fd_ret fd) eq_refl).
    simpl; eauto.
  Qed.

  Lemma check_fdefs_complete fds :
    Forall (fdef_ok ge) fds -> exists H, check_fdefs ge fds = Ok H.
  Proof.
    induction 1 as [|fd fds Hfd _ IH]; [eexists; reflexivity|].
    cbn [check_fdefs]. step_ok (check_fdef_complete fd Hfd). step_ok IH. eauto.
  Qed.
End Complete.

Lemma check_names_complete ge : NoDup (map fd_name ge) -> exists H, check_names ge = Ok H.
Proof.
  intros Hn; unfold check_names.
  destruct (NoDup_dec (map fd_name ge)) as [H|H]; eauto. contradiction.
Qed.

Theorem check_genv_complete ge : genv_ok ge -> exists H, check_genv ge = Ok H.
Proof.
  intros [Hn Hf]; unfold check_genv.
  step_ok (check_names_complete ge Hn).
  step_ok (check_fdefs_complete ge ge Hf). eauto.
Qed.

Definition genv_ok_dec ge : {genv_ok ge} + {~ genv_ok ge}.
Proof.
  destruct (check_genv ge) as [H|err] eqn:E; [left; exact H | right].
  intros Hok. destruct (check_genv_complete ge Hok) as [p E'].
  rewrite E in E'. discriminate.
Defined.
