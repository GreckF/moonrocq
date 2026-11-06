(** * Completeness of the Core checker, and decidability of typing

    Soundness of [infer] holds by construction (it returns derivations).
    Here we prove the converse: whenever [Γ ⊢[ge;Σ;Λ] e : τ] is derivable,
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

Lemma expect_eff_ok ε ρ : eff_le ε ρ -> exists H, expect_eff ε ρ = Ok H.
Proof.
  intros Hle; unfold expect_eff.
  destruct (ty_eq_dec ε TNever) as [H|Hn]; [eauto|].
  destruct (ty_eq_dec ε ρ) as [H|Hn']; [eauto|].
  destruct Hle; contradiction.
Qed.

Lemma check_bool_ok b err : b = true -> exists H, check_bool b err = Ok H.
Proof. intros ->; simpl; eauto. Qed.

Lemma expect_nat_ok n m err : m = n -> exists H, expect_nat n m err = Ok H.
Proof.
  intros <-; unfold expect_nat. destruct (PeanoNat.Nat.eq_dec m m) as [H|H]; eauto.
  now contradiction H.
Qed.

(* Rewrite a sub-computation with a known successful result. *)
Local Ltac step_ok H :=
  let p := fresh "p" in let E := fresh "E" in
  destruct H as [p E]; rewrite E; cbn [bind as_arrow as_tuple as_data as_ref].

Lemma pats_typed_length ge ps τs Δ : ⊢ᵖ*[ge] ps : τs ⇝ Δ -> length ps = length τs.
Proof. induction 1; simpl; auto. Qed.

Lemma ctor_fields_inv ge T c ts fs :
  ctor_fields ge T c ts = Some fs ->
  exists td cd, lookup_ty ge T = Some td /\ lookup_ctor td c = Some cd /\
                fs = map (tsubst (inst ts)) (cd_fields cd).
Proof.
  unfold ctor_fields. destruct (lookup_ty ge T) as [td|] eqn:E1; [|discriminate].
  destruct (lookup_ctor td c) as [cd|] eqn:E2; [|discriminate].
  intros E; inversion E; subst. exists td, cd; auto.
Qed.

Section Complete.
  Variables (ge : genv) (Σ : styping).

  (** ** Patterns *)

  Lemma check_pat_complete :
    (forall p τ Δ, ⊢ᵖ[ge] p : τ ⇝ Δ ->
       exists H, check_pat ge p τ = Ok (exist _ Δ H)) /\
    (forall ps τs Δ, ⊢ᵖ*[ge] ps : τs ⇝ Δ ->
       exists H, check_pats ge (check_pat ge) ps τs = Ok (exist _ Δ H)).
  Proof.
    apply pat_typed_mutind; intros; cbn [check_pat bind as_tuple as_data as_ref].
    - eauto.
    - eauto.
    - step_ok (expect_ty_ok (TBase (lit_ty l)) (TBase (lit_ty l)) eq_refl). eauto.
    - step_ok (expect_nat_ok (length τs) (length ps) (E_PatArity (length τs) (length ps))
                 (pats_typed_length _ _ _ _ H)).
      step_ok H0. eauto.
    - destruct (ctor_fields_inv _ _ _ _ _ H) as (td & cd & Etd & Ecd & ->).
      step_ok (of_option_some _ _ (E_UnknownType T) Etd).
      step_ok (of_option_some _ _ (E_UnknownCtor T c) Ecd).
      assert (Hl := pats_typed_length _ _ _ _ H0). rewrite length_map in Hl.
      step_ok (expect_nat_ok (length (cd_fields cd)) (length ps)
                 (E_PatArity (length (cd_fields cd)) (length ps)) Hl).
      step_ok H1. eauto.
    - step_ok H0. eauto.
    - step_ok (expect_ty_ok TError TError eq_refl). step_ok H0. eauto.
    - eexists; reflexivity.
    - cbn [check_pats]. step_ok H0.
      fold (check_pats ge (check_pat ge) ps τs).
      step_ok H2. eauto.
  Qed.

  Theorem infer_complete_mut :
    (forall Λ Γ e τ, Γ ⊢[ge;Σ;Λ] e : τ ->
       exists H, infer ge Σ Λ Γ e = Ok (exist _ τ H)) /\
    (forall Λ Γ es τs, Γ ⊢*[ge;Σ;Λ] es : τs ->
       (exists H, infer_list ge Σ Λ Γ (infer ge Σ Λ Γ) es = Ok (exist _ τs H)) /\
       (exists H, check_list ge Σ Λ Γ (infer ge Σ Λ Γ) es τs = Ok H)) /\
    (forall Λ Γ bs τs τ, Γ ⊢ᵇ[ge;Σ;Λ] bs : τs ⇒ τ ->
       exists H, check_branches ge Σ Λ (fun Γ' e' => infer ge Σ Λ Γ' e') Γ τs τ bs = Ok H).
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
                 (has_types_length _ _ _ _ _ _ H1)).
      destruct H2 as [_ H2]. step_ok H2. step_ok (expect_eff_ok _ _ H3). eauto.
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
                 (has_types_length _ _ _ _ _ _ H)).
      destruct H0 as [_ H0]. step_ok H0. eauto.
    - (* T_Constr *)
      step_ok (of_option_some _ _ (E_UnknownType T) H).
      step_ok (expect_nat_ok (td_tparams td) (length ts)
                 (E_TypeArgArity T (td_tparams td) (length ts)) H0).
      step_ok (of_option_some _ _ (E_UnknownCtor T c) H1).
      step_ok H3.
      step_ok (expect_ty_ok (TTuple (map (tsubst (inst ts)) (cd_fields cd))) _ eq_refl). eauto.
    - (* T_Match *)
      step_ok H0. step_ok H2. eauto.
    - (* T_Loc *)
      step_ok (of_option_some _ _ (E_UnboundLoc l) H). eauto.
    - (* T_Mem *)
      step_ok (expect_nat_ok _ _ (E_ArgArity (length (fst (mem_sig op))) (length args))
                 (has_types_length _ _ _ _ _ _ H)).
      destruct H0 as [_ H0]. step_ok H0. eauto.
    - (* T_Loop *)
      step_ok H0. step_ok (expect_ty_ok (TTuple ps) (TTuple ps) eq_refl).
      step_ok H2. step_ok (expect_ty_ok τ τ eq_refl). eauto.
    - (* T_Jump *)
      step_ok (of_option_some _ _ (E_UnknownLabel k) H).
      step_ok H1. step_ok (expect_ty_ok (ctl_ty c lbl) (ctl_ty c lbl) eq_refl). eauto.
    - (* T_Abort *)
      eauto.
    - (* T_Up *)
      step_ok (of_option_some _ _ (E_UnknownType T) H).
      step_ok (check_bool_ok _ (E_NotError T) H0).
      step_ok H2. step_ok (expect_ty_ok (TData T []) _ eq_refl). eauto.
    - (* T_Raise *)
      step_ok H0. step_ok (expect_eff_ok _ _ H1). eauto.
    - (* T_Try *)
      step_ok H0. step_ok H2. step_ok H4. step_ok (expect_ty_ok τ τ eq_refl). eauto.
    - (* T_Defer *)
      step_ok H0. step_ok H2. eauto.
    - (* Ts_nil *)
      split; eexists; reflexivity.
    - (* Ts_cons *)
      destruct H2 as [Hl Hc]. split.
      + cbn [infer_list]. step_ok H0. fold (infer_list ge Σ Λ Γ (infer ge Σ Λ Γ) es).
        step_ok Hl. eauto.
      + cbn [check_list]. step_ok H0. step_ok (expect_ty_ok τ τ eq_refl).
        fold (check_list ge Σ Λ Γ (infer ge Σ Λ Γ) es τs).
        step_ok Hc. eauto.
    - (* Bs_nil *)
      eexists; reflexivity.
    - (* Bs_cons *)
      cbn [check_branches].
      step_ok (proj1 check_pat_complete _ _ _ H).
      step_ok H1. step_ok (expect_ty_ok τ τ eq_refl).
      fold (check_branches ge Σ Λ (fun Γ' e' => infer ge Σ Λ Γ' e') Γ τs τ bs).
      step_ok H3. eauto.
  Qed.

  Theorem infer_complete Λ Γ e τ :
    Γ ⊢[ge;Σ;Λ] e : τ -> exists H, infer ge Σ Λ Γ e = Ok (exist _ τ H).
  Proof. apply (proj1 infer_complete_mut). Qed.

  (** Types are unique (the checker is a function). *)
  Corollary has_type_unique Λ Γ e τ1 τ2 :
    Γ ⊢[ge;Σ;Λ] e : τ1 -> Γ ⊢[ge;Σ;Λ] e : τ2 -> τ1 = τ2.
  Proof.
    intros H1 H2.
    destruct (infer_complete _ _ _ _ H1) as [p1 E1].
    destruct (infer_complete _ _ _ _ H2) as [p2 E2].
    rewrite E1 in E2. now inversion E2.
  Qed.

  (** ** Decidability *)

  Definition has_type_dec Λ Γ e τ : {Γ ⊢[ge;Σ;Λ] e : τ} + {~ Γ ⊢[ge;Σ;Λ] e : τ}.
  Proof.
    destruct (infer ge Σ Λ Γ e) as [[τ' H]|err] eqn:E.
    - destruct (ty_eq_dec τ' τ) as [<-|Hne]; [left; exact H | right].
      intros Ht. destruct (infer_complete _ _ _ _ Ht) as [p E'].
      rewrite E in E'. inversion E'. contradiction.
    - right. intros Ht. destruct (infer_complete _ _ _ _ Ht) as [p E'].
      rewrite E in E'. discriminate.
  Defined.

  (** Whether an expression is typable at all. *)
  Definition typable_dec Λ Γ e :
    {τ | Γ ⊢[ge;Σ;Λ] e : τ} + {forall τ, ~ Γ ⊢[ge;Σ;Λ] e : τ}.
  Proof.
    destruct (infer ge Σ Λ Γ e) as [p|err] eqn:E; [left; exact p | right].
    intros τ Ht. destruct (infer_complete _ _ _ _ Ht) as [p E'].
    rewrite E in E'. discriminate.
  Defined.
End Complete.

(** ** Global environments *)

Section GlobalComplete.
  Variable ge : genv.

  Lemma check_fdef_complete fd : fdef_ok ge fd -> exists H, check_fdef ge fd = Ok H.
  Proof.
    intros Hfd; unfold check_fdef.
    step_ok (infer_complete ge [] _ _ _ _ Hfd).
    step_ok (expect_ty_ok (fd_ret fd) (fd_ret fd) eq_refl).
    simpl; eauto.
  Qed.

  Lemma check_fdefs_complete fds :
    Forall (fdef_ok ge) fds -> exists H, check_fdefs ge fds = Ok H.
  Proof.
    induction 1 as [|fd fds Hfd _ IH]; [eexists; reflexivity|].
    cbn [check_fdefs]. step_ok (check_fdef_complete fd Hfd). step_ok IH. eauto.
  Qed.
End GlobalComplete.

Lemma check_all_complete {A} (P : A -> Prop) f l :
  (forall a, P a -> exists H, f a = Ok H) -> Forall P l ->
  exists H, check_all P f l = Ok H.
Proof.
  intros Hf; induction 1 as [|a l Ha _ IH]; [eexists; reflexivity|].
  cbn [check_all]. step_ok (Hf a Ha). fold (check_all P f l). step_ok IH. eauto.
Qed.

Lemma check_nodup_complete l err : NoDup l -> exists H, check_nodup l err = Ok H.
Proof.
  intros Hn; unfold check_nodup. destruct (NoDup_dec l) as [H|H]; eauto. contradiction.
Qed.

Lemma check_wf_complete ge n t : ty_wf ge n t -> exists H, check_wf ge n t = Ok H.
Proof. apply check_bool_ok. Qed.

Lemma check_tdef_complete ge td : tdef_ok ge td -> exists H, check_tdef ge td = Ok H.
Proof.
  intros [Hn Hf]; unfold check_tdef.
  step_ok (check_nodup_complete _ E_DuplicateCtor Hn).
  step_ok (check_all_complete _ _ _ (fun cd Hcd =>
             check_all_complete _ _ _ (check_wf_complete ge (td_tparams td)) Hcd) Hf).
  simpl; eauto.
Qed.

Lemma check_fsig_complete ge fd : fsig_ok ge fd -> exists H, check_fsig ge fd = Ok H.
Proof.
  intros [Hp [Hr He]]; unfold check_fsig.
  step_ok (check_all_complete _ _ _ (check_wf_complete ge (fd_tparams fd)) Hp).
  step_ok (check_wf_complete _ _ _ Hr).
  step_ok (check_bool_ok _ (E_IllFormed (fd_eff fd)) He).
  simpl; eauto.
Qed.

Theorem check_genv_complete ge : genv_ok ge -> exists H, check_genv ge = Ok H.
Proof.
  intros (Ht & Htd & Hn & Hs & Hf); unfold check_genv.
  step_ok (check_nodup_complete _ E_DuplicateType Ht).
  step_ok (check_all_complete _ _ _ (check_tdef_complete ge) Htd).
  step_ok (check_nodup_complete _ E_DuplicateGlobal Hn).
  step_ok (check_all_complete _ _ _ (check_fsig_complete ge) Hs).
  step_ok (check_fdefs_complete ge _ Hf). eauto.
Qed.

Definition genv_ok_dec ge : {genv_ok ge} + {~ genv_ok ge}.
Proof.
  destruct (check_genv ge) as [H|err] eqn:E; [left; exact H | right].
  intros Hok. destruct (check_genv_complete ge Hok) as [p E'].
  rewrite E in E'. discriminate.
Defined.
