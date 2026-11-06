(** * Structural properties of the Core typing relation

    Renaming, term substitution and type substitution preserve typing.
    These are the workhorses of the preservation proof (β-reduction, [let],
    and instantiation of generic top-level functions). *)

From Stdlib Require Import List Arith Lia.
From MoonRocq.Core Require Import Syntax Prim Subst Typing.
Import ListNotations.

Section Lemmas.
  Variable ge : genv.

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
    (forall Γ e τ, Γ ⊢[ge] e : τ ->
       forall Δ ξ, ren_ok Γ Δ ξ -> Δ ⊢[ge] rename ξ e : τ) /\
    (forall Γ es τs, Γ ⊢*[ge] es : τs ->
       forall Δ ξ, ren_ok Γ Δ ξ -> Δ ⊢*[ge] map (rename ξ) es : τs).
  Proof.
    apply has_type_mutind; intros; simpl.
    - constructor; auto.
    - econstructor; eauto.
    - constructor.
    - constructor; auto using ren_ok_up.
    - econstructor; eauto.
    - econstructor; eauto. apply (H2 _ _ (ren_ok_up _ _ _ [τ1] H3)).
    - constructor; auto.
    - constructor; auto.
    - econstructor; eauto.
    - constructor; auto.
    - constructor.
    - constructor; auto.
  Qed.

  Lemma shift_typing Γ e τ ps :
    Γ ⊢[ge] e : τ -> ps ++ Γ ⊢[ge] rename (Nat.add (length ps)) e : τ.
  Proof.
    intros H; apply (proj1 rename_typing _ _ _ H).
    intros x τ' Hx. rewrite nth_error_app2 by lia.
    now replace (length ps + x - length ps) with x by lia.
  Qed.

  (** ** Substitution *)

  Definition sub_ok (Γ Δ : ctx) (σ : nat -> expr) : Prop :=
    forall x τ, nth_error Γ x = Some τ -> Δ ⊢[ge] σ x : τ.

  Lemma sub_ok_up Γ Δ σ ps :
    sub_ok Γ Δ σ -> sub_ok (ps ++ Γ) (ps ++ Δ) (upsub (length ps) σ).
  Proof.
    intros H x τ Hx; unfold upsub.
    destruct (Nat.ltb_spec x (length ps)).
    - constructor. rewrite nth_error_app1 in * by lia; auto.
    - rewrite nth_error_app2 in Hx by lia. apply shift_typing; auto.
  Qed.

  Lemma subst_typing :
    (forall Γ e τ, Γ ⊢[ge] e : τ ->
       forall Δ σ, sub_ok Γ Δ σ -> Δ ⊢[ge] subst σ e : τ) /\
    (forall Γ es τs, Γ ⊢*[ge] es : τs ->
       forall Δ σ, sub_ok Γ Δ σ -> Δ ⊢*[ge] map (subst σ) es : τs).
  Proof.
    apply has_type_mutind; intros; simpl.
    - auto.
    - econstructor; eauto.
    - constructor.
    - constructor; auto using sub_ok_up.
    - econstructor; eauto.
    - econstructor; eauto. apply (H2 _ _ (sub_ok_up _ _ _ [τ1] H3)).
    - constructor; auto.
    - constructor; auto.
    - econstructor; eauto.
    - constructor; auto.
    - constructor.
    - constructor; auto.
  Qed.

  (** β-reduction: substituting typed closed arguments for the parameters. *)
  Lemma subst_args_typing ps b r vs :
    ps ++ [] ⊢[ge] b : r -> [] ⊢*[ge] vs : ps ->
    [] ⊢[ge] subst (args_sub vs) b : r.
  Proof.
    intros Hb Hvs. apply (proj1 subst_typing _ _ _ Hb).
    intros x τ Hx. rewrite app_nil_r in Hx. unfold args_sub.
    eapply has_types_nth; eauto.
  Qed.

  (** ** Type substitution *)

  Lemma tsubst_typing σ :
    (forall Γ e τ, Γ ⊢[ge] e : τ ->
       map (tsubst σ) Γ ⊢[ge] esubst_ty σ e : tsubst σ τ) /\
    (forall Γ es τs, Γ ⊢*[ge] es : τs ->
       map (tsubst σ) Γ ⊢*[ge] map (esubst_ty σ) es : map (tsubst σ) τs).
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
    - constructor.
    - constructor; auto.
  Qed.

  (** Instantiating a well-typed generic top-level function yields a
      closed, well-typed λ-abstraction. *)
  Lemma global_inst_typing f fd ts :
    genv_ok ge -> lookup_fn ge f = Some fd ->
    [] ⊢[ge] ELam (map (tsubst (inst ts)) (fd_params fd)) (tsubst (inst ts) (fd_ret fd))
                  (esubst_ty (inst ts) (fd_body fd))
       : TArrow (map (tsubst (inst ts)) (fd_params fd)) (tsubst (inst ts) (fd_ret fd)).
  Proof.
    intros [_ Hall] Hl. constructor. rewrite app_nil_r.
    apply lookup_fn_in in Hl. rewrite Forall_forall in Hall.
    apply (proj1 (tsubst_typing (inst ts))), Hall, Hl.
  Qed.
End Lemmas.
