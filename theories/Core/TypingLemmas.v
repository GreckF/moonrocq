(** * Structural properties of the Core typing relation

    Renaming, term substitution, type substitution and weakening (of the
    store typing and of the label context) preserve typing.  These are the
    workhorses of the preservation proof (β-reduction, [let], loops,
    instantiation of generic top-level functions, allocation). *)

From Stdlib Require Import List Arith Lia.
From MoonRocq.Core Require Import Syntax Prim Subst Typing.
Import ListNotations.

Lemma nth_error_app_some {A} (l l' : list A) k x :
  nth_error l k = Some x -> nth_error (l ++ l') k = Some x.
Proof.
  intros H. rewrite nth_error_app1; [exact H|]. apply nth_error_Some. congruence.
Qed.

Section Lemmas.
  Variable ge : genv.

  (** ** Weakening of the store typing and of the label context *)

  Lemma weaken_typing Σ :
    (forall Λ Γ e τ, Γ ⊢[ge;Σ;Λ] e : τ ->
       forall Σ' Λ', Γ ⊢[ge;Σ ++ Σ';Λ ++ Λ'] e : τ) /\
    (forall Λ Γ es τs, Γ ⊢*[ge;Σ;Λ] es : τs ->
       forall Σ' Λ', Γ ⊢*[ge;Σ ++ Σ';Λ ++ Λ'] es : τs) /\
    (forall Λ Γ bs τs τ, Γ ⊢ᵇ[ge;Σ;Λ] bs : τs ⇒ τ ->
       forall Σ' Λ', Γ ⊢ᵇ[ge;Σ ++ Σ';Λ ++ Λ'] bs : τs ⇒ τ).
  Proof.
    apply has_type_mutind; intros; econstructor; eauto using nth_error_app_some.
  Qed.

  Lemma weaken_store Σ Σ' Λ Γ e τ :
    Γ ⊢[ge;Σ;Λ] e : τ -> Γ ⊢[ge;Σ ++ Σ';Λ] e : τ.
  Proof.
    intros H. rewrite <- (app_nil_r Λ). apply (proj1 (weaken_typing Σ)), H.
  Qed.

  Lemma weaken_store_types Σ Σ' Λ Γ es τs :
    Γ ⊢*[ge;Σ;Λ] es : τs -> Γ ⊢*[ge;Σ ++ Σ';Λ] es : τs.
  Proof.
    intros H. rewrite <- (app_nil_r Λ). apply (proj1 (proj2 (weaken_typing Σ))), H.
  Qed.

  Lemma weaken_store_branches Σ Σ' Λ Γ bs τs τ :
    Γ ⊢ᵇ[ge;Σ;Λ] bs : τs ⇒ τ -> Γ ⊢ᵇ[ge;Σ ++ Σ';Λ] bs : τs ⇒ τ.
  Proof.
    intros H. rewrite <- (app_nil_r Λ). apply (proj2 (proj2 (weaken_typing Σ))), H.
  Qed.

  Variable Σ : styping.

  (** ** Renaming *)

  Definition ren_ok (Γ Δ : ctx) (ξ : nat -> nat) : Prop :=
    forall x τ, nth_error Γ x = Some τ -> nth_error Δ (ξ x) = Some τ.

  Lemma ren_ok_up Γ Δ ξ ps :
    ren_ok Γ Δ ξ -> ren_ok (ps ++ Γ) (ps ++ Δ) (upren (length ps) ξ).
  Proof.
    intros H x τ Hx; unfold upren.
    destruct (Nat.ltb_spec x (length ps)).
    - rewrite nth_error_app1 in * by lia; auto.
    - rewrite nth_error_app2 in Hx by lia. rewrite nth_error_app2 by lia.
      replace (length ps + ξ (x - length ps) - length ps) with (ξ (x - length ps)) by lia.
      auto.
  Qed.

  Lemma rename_typing :
    (forall Λ Γ e τ, Γ ⊢[ge;Σ;Λ] e : τ ->
       forall Δ ξ, ren_ok Γ Δ ξ -> Δ ⊢[ge;Σ;Λ] rename ξ e : τ) /\
    (forall Λ Γ es τs, Γ ⊢*[ge;Σ;Λ] es : τs ->
       forall Δ ξ, ren_ok Γ Δ ξ -> Δ ⊢*[ge;Σ;Λ] map (rename ξ) es : τs) /\
    (forall Λ Γ bs τs τ, Γ ⊢ᵇ[ge;Σ;Λ] bs : τs ⇒ τ ->
       forall Δ ξ, ren_ok Γ Δ ξ ->
       Δ ⊢ᵇ[ge;Σ;Λ] map (fun '(p, b) => (p, rename (upren (pat_arity p) ξ) b)) bs : τs ⇒ τ).
  Proof.
    apply has_type_mutind; intros; simpl; try (econstructor; eauto using ren_ok_up; fail).
    - (* T_Let *)
      econstructor; [eauto|]. apply (H2 _ _ (ren_ok_up _ _ _ [τ1] H3)).
    - (* Bs_cons *)
      eapply Bs_cons; [eassumption | | auto].
      rewrite <- (proj1 (pat_typed_arity ge) _ _ _ H). auto using ren_ok_up.
  Qed.

  Lemma shift_typing Λ Γ e τ ps :
    Γ ⊢[ge;Σ;Λ] e : τ -> ps ++ Γ ⊢[ge;Σ;Λ] rename (Nat.add (length ps)) e : τ.
  Proof.
    intros H; apply (proj1 rename_typing _ _ _ _ H).
    intros x τ' Hx. rewrite nth_error_app2 by lia.
    now replace (length ps + x - length ps) with x by lia.
  Qed.

  (** ** Substitution

      Substituted terms must be typable under every label context: they
      may end up under a λ (no labels) or inside a loop body (one more
      label).  Closed values are (see [value_any_labels] in
      [Soundness.v]). *)

  Definition sub_ok (Γ Δ : ctx) (σ : nat -> expr) : Prop :=
    forall x τ, nth_error Γ x = Some τ -> forall Λ, Δ ⊢[ge;Σ;Λ] σ x : τ.

  Lemma sub_ok_up Γ Δ σ ps :
    sub_ok Γ Δ σ -> sub_ok (ps ++ Γ) (ps ++ Δ) (upsub (length ps) σ).
  Proof.
    intros H x τ Hx Λ; unfold upsub.
    destruct (Nat.ltb_spec x (length ps)).
    - constructor. rewrite nth_error_app1 in * by lia; auto.
    - rewrite nth_error_app2 in Hx by lia. apply shift_typing; auto.
  Qed.

  Lemma subst_typing :
    (forall Λ Γ e τ, Γ ⊢[ge;Σ;Λ] e : τ ->
       forall Δ σ, sub_ok Γ Δ σ -> Δ ⊢[ge;Σ;Λ] subst σ e : τ) /\
    (forall Λ Γ es τs, Γ ⊢*[ge;Σ;Λ] es : τs ->
       forall Δ σ, sub_ok Γ Δ σ -> Δ ⊢*[ge;Σ;Λ] map (subst σ) es : τs) /\
    (forall Λ Γ bs τs τ, Γ ⊢ᵇ[ge;Σ;Λ] bs : τs ⇒ τ ->
       forall Δ σ, sub_ok Γ Δ σ ->
       Δ ⊢ᵇ[ge;Σ;Λ] map (fun '(p, b) => (p, subst (upsub (pat_arity p) σ) b)) bs : τs ⇒ τ).
  Proof.
    apply has_type_mutind; intros; simpl; try (econstructor; eauto using sub_ok_up; fail).
    - (* T_Var *) eauto.
    - (* T_Let *)
      econstructor; [eauto|]. apply (H2 _ _ (sub_ok_up _ _ _ [τ1] H3)).
    - (* Bs_cons *)
      eapply Bs_cons; [eassumption | | auto].
      rewrite <- (proj1 (pat_typed_arity ge) _ _ _ H). auto using sub_ok_up.
  Qed.

  (** β-reduction, [let], [match] and loops: substituting closed arguments
      for the innermost variables. *)
  Lemma subst_args_typing Λ ps b r vs :
    ps ++ [] ⊢[ge;Σ;Λ] b : r -> (forall Λ', [] ⊢*[ge;Σ;Λ'] vs : ps) ->
    [] ⊢[ge;Σ;Λ] subst (args_sub vs) b : r.
  Proof.
    intros Hb Hvs. apply (proj1 subst_typing _ _ _ _ Hb).
    intros x τ Hx Λ'. rewrite app_nil_r in Hx. unfold args_sub.
    eapply has_types_nth; eauto.
  Qed.
End Lemmas.

(** ** Type substitution *)

Section TSubst.
  Variable ge : genv.

  Lemma tsubst_pat_typing σ :
    (forall p τ Δ, ⊢ᵖ[ge] p : τ ⇝ Δ -> ⊢ᵖ[ge] p : tsubst σ τ ⇝ map (tsubst σ) Δ) /\
    (forall ps τs Δ, ⊢ᵖ*[ge] ps : τs ⇝ Δ ->
       ⊢ᵖ*[ge] ps : map (tsubst σ) τs ⇝ map (tsubst σ) Δ).
  Proof.
    apply pat_typed_mutind; intros; simpl.
    - constructor.
    - constructor.
    - constructor.
    - constructor; auto.
    - econstructor; [apply ctor_fields_tsubst; eassumption | auto].
    - constructor; auto.
    - constructor.
    - rewrite map_app. constructor; auto.
  Qed.

  Lemma tsubst_typing σ Σ :
    (forall Λ Γ e τ, Γ ⊢[ge;Σ;Λ] e : τ ->
       map (tsubst σ) Γ ⊢[ge;map (ltsubst σ) Σ;map (lsubst σ) Λ]
         esubst_ty σ e : tsubst σ τ) /\
    (forall Λ Γ es τs, Γ ⊢*[ge;Σ;Λ] es : τs ->
       map (tsubst σ) Γ ⊢*[ge;map (ltsubst σ) Σ;map (lsubst σ) Λ]
         map (esubst_ty σ) es : map (tsubst σ) τs) /\
    (forall Λ Γ bs τs τ, Γ ⊢ᵇ[ge;Σ;Λ] bs : τs ⇒ τ ->
       map (tsubst σ) Γ ⊢ᵇ[ge;map (ltsubst σ) Σ;map (lsubst σ) Λ]
         map (fun '(p, b) => (p, esubst_ty σ b)) bs : tsubst σ τs ⇒ tsubst σ τ).
  Proof.
    apply has_type_mutind; intros; simpl.
    - constructor. rewrite nth_error_map, H; reflexivity.
    - replace (map (tsubst σ) (map (tsubst (inst ts)) (fd_params fd)))
        with (map (tsubst (inst (map (tsubst σ) ts))) (fd_params fd)).
      + rewrite tsubst_inst. constructor; auto. now rewrite length_map.
      + rewrite map_map. apply map_ext. intros; symmetry; apply tsubst_inst.
    - constructor.
    - constructor. now rewrite <- map_app.
    - econstructor; eauto.
    - econstructor; eauto.
    - constructor; auto.
    - constructor; auto.
    - econstructor; eauto. rewrite nth_error_map, H1; reflexivity.
    - destruct (prim_sig_closed σ op) as [E1 E2].
      rewrite E2. constructor. now rewrite <- E1.
    - econstructor; eauto.
      + now rewrite length_map.
      + replace (map (tsubst (inst (map (tsubst σ) ts))) (cd_fields cd))
          with (map (tsubst σ) (map (tsubst (inst ts)) (cd_fields cd))); [exact H3|].
        rewrite map_map. apply map_ext. intros; apply tsubst_inst.
    - econstructor; eauto.
    - (* T_Loc *)
      rewrite <- lty_ty_ltsubst. constructor. rewrite nth_error_map, H; reflexivity.
    - (* T_Mem *)
      destruct (mem_sig_msubst σ op) as [E1 E2].
      rewrite <- E2. constructor. now rewrite E1.
    - (* T_Loop *)
      constructor; [exact H0|]. rewrite <- map_app. exact H2.
    - (* T_Jump *)
      econstructor.
      + rewrite nth_error_map, H; reflexivity.
      + rewrite ctl_ty_lsubst. exact H1.
    - (* T_Abort *) constructor.
    - constructor.
    - constructor; auto.
    - constructor.
    - eapply Bs_cons; [ | | auto].
      + apply (proj1 (tsubst_pat_typing σ)); eassumption.
      + rewrite <- map_app. assumption.
  Qed.

  (** Instantiating a well-typed generic top-level function yields a
      closed, well-typed λ-abstraction (under any store typing and label
      context). *)
  Lemma global_inst_typing Σ Λ f fd ts :
    genv_ok ge -> lookup_fn ge f = Some fd ->
    [] ⊢[ge;Σ;Λ] ELam (map (tsubst (inst ts)) (fd_params fd)) (tsubst (inst ts) (fd_ret fd))
                       (esubst_ty (inst ts) (fd_body fd))
       : TArrow (map (tsubst (inst ts)) (fd_params fd)) (tsubst (inst ts) (fd_ret fd)).
  Proof.
    intros (_ & _ & _ & _ & Hall) Hl. constructor. rewrite app_nil_r.
    apply lookup_fn_in in Hl. rewrite Forall_forall in Hall.
    apply (weaken_store ge [] Σ []).
    exact (proj1 (tsubst_typing (inst ts) []) [] _ _ _ (Hall _ Hl)).
  Qed.
End TSubst.
