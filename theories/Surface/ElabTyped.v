(** * Surface: elaboration produces well-typed Core

    [elab_typed]: whatever the rules of [ElabSpec.v] relate a surface
    expression to is well typed in Core, at the synthesized or expected
    type, in the Core view of the environments ([ctx_of Γ], [cc_of L]).
    Source programs mention no store locations: [Σ = []]. *)

From Stdlib Require Import List ZArith String Bool Arith Lia.
From MoonRocq.Prelude Require Import Result EqDec Ident.
From MoonRocq.Core Require Import Syntax Prim Subst Typing Check.
From MoonRocq.Surface Require Import Syntax Base ElabSpec.
Import ListNotations.

Section Typed.
  Variable E : senv.
  Abbreviation ge := (se_hdr E).

  Lemma binop_typed Γ Λ p op τ a b e :
    elab_binop p op τ a b = Ok e ->
    Γ ⊢[ge;[];Λ] a : τ -> Γ ⊢[ge;[];Λ] b : τ ->
    Γ ⊢[ge;[];Λ] e : binop_res op τ.
  Proof.
    unfold elab_binop, binop_res; intros H Ha Hb.
    destruct (assoc op arith_ops) as [o|], (assoc op cmp_ops) as [c|], τ;
      try discriminate H;
      repeat match goal with
             | b0 : base_ty |- _ => destruct b0; try discriminate H
             | o0 : arith_op |- _ => destruct o0; try discriminate H
             | c0 : cmp_op |- _ => destruct c0; try discriminate H
             end;
      injection H as <-;
      repeat (econstructor; eauto).
  Qed.

  Lemma lam_ctx_ctx ps τs Γ :
    List.length ps = List.length τs ->
    ctx_of (List.app (lam_ctx ps τs) Γ) = List.app τs (ctx_of Γ).
  Proof.
    unfold ctx_of, lam_ctx; rewrite map_app; intros Hl; f_equal.
    revert τs Hl; induction ps as [|xa ps IH]; intros [|τ τs] Hl; simpl in *;
      try discriminate; auto.
    rewrite IH; auto.
  Qed.

  Lemma proj_list_typed Λ Γ pre ps :
    TTuple (List.app pre ps) :: Γ ⊢*[ge;[];Λ]
      map (fun i => EProj (EVar 0) i) (seq (List.length pre) (List.length ps)) : ps.
  Proof.
    revert pre; induction ps as [|τ ps IH]; intros pre; simpl; constructor.
    - eapply T_Proj; [constructor; reflexivity|].
      rewrite nth_error_app2 by lia; rewrite Nat.sub_diag; reflexivity.
    - specialize (IH (List.app pre [τ])).
      rewrite <- app_assoc in IH; simpl in IH.
      rewrite length_app in IH; simpl in IH; rewrite Nat.add_1_r in IH; exact IH.
  Qed.

  Lemma wrap_call_typed L Γ f es ps r ε :
    Γ ⊢[ge;[];cc_of L] f : TArrow ps r ε ->
    Γ ⊢*[ge;[];cc_of L] es : ps ->
    call_ok E L ε ->
    Γ ⊢[ge;[];cc_of L] wrap_call L ε r f es : r.
  Proof.
    intros Hf Hes Hok.
    assert (Hplain : eff_le ε (ce_exn L) -> Γ ⊢[ge;[];cc_of L] EApp f es : r)
      by (intros; eapply T_App; eauto).
    unfold wrap_call, call_ok, call_allowed in *.
    destruct ε as [| | | | T [|? ?] | | |]; auto.
    destruct (ce_exn L) eqn:Ex; auto.
    destruct Hok as (td & Htd & Herr).
    unfold promote_call.
    eapply T_Let; [constructor; constructor; eauto|].
    eapply T_Try with (τ0 := r).
    - eapply T_App with (ps := ps) (ε := TData T []).
      + eapply T_Proj; [constructor; reflexivity|reflexivity].
      + rewrite (has_types_length _ _ _ _ _ _ Hes).
        exact (proj_list_typed _ _ [TArrow ps r (TData T [])] ps).
      + right; reflexivity.
    - eapply T_Raise.
      + eapply T_Up; eauto. constructor; reflexivity.
      + right; simpl; rewrite Ex; reflexivity.
    - constructor; reflexivity.
  Qed.

  Lemma coerce_typed Λ Γ e τ τ' e' :
    ⊩ᶜ[E] e : τ ≼ τ' ⇝ e' ->
    Γ ⊢[ge;[];Λ] e : τ -> Γ ⊢[ge;[];Λ] e' : τ'.
  Proof.
    destruct 1 as [|e0 T (td & Htd & Herr)]; intros He; auto.
    eapply T_Up; eauto.
  Qed.

  Lemma eblock_typed Γ r ε b :
    Γ ⊢[ge;[];cc_of (fun_env r ε)] b : r ->
    Γ ⊢[ge;[];mk_cctx [] ε] eblock r b : r.
  Proof.
    intros Hb; unfold eblock; eapply T_Loop; [constructor; constructor|exact Hb].
  Qed.

  Lemma params_len {A B} (P : A -> B -> Prop) xs ys :
    Forall2 P xs ys -> List.length xs = List.length ys.
  Proof. induction 1; simpl; auto. Qed.

  (** Core typing rules whose result type is computed ([prim_sig],
      [mem_sig]) are applied at the given operator. *)
  Ltac prim :=
    match goal with
    | |- has_type _ _ _ _ (EPrim ?op ?args) _ => apply (T_Prim _ _ _ _ op args); simpl
    | |- has_type _ _ _ _ (EMem ?op ?args) _ => apply (T_Mem _ _ _ _ op args); simpl
    end.
  Ltac tc := repeat (first [prim | econstructor]; eauto).

  Lemma ctx_of_app (Δ Γ : lctx) : ctx_of (List.app Δ Γ) = List.app (ctx_of Δ) (ctx_of Γ).
  Proof. apply map_app. Qed.

  (** *** Patterns *)

  Lemma pats_app qs1 qs2 τs1 τs2 Δ1 Δ2 :
    ⊢ᵖ*[ge] qs1 : τs1 ⇝ Δ1 -> ⊢ᵖ*[ge] qs2 : τs2 ⇝ Δ2 ->
    ⊢ᵖ*[ge] List.app qs1 qs2 : List.app τs1 τs2 ⇝ List.app Δ1 Δ2.
  Proof.
    induction 1; simpl; auto.
    intros H2; rewrite <- app_assoc; constructor; auto.
  Qed.

  Lemma wilds_typed (τs : list ty) : ⊢ᵖ*[ge] map (fun _ => PWild) τs : τs ⇝ [].
  Proof.
    induction τs; simpl; [constructor|].
    change (@nil ty) with (List.app (@nil ty) []); constructor; auto; constructor.
  Qed.

  Lemma lookup_ctor_single td cd :
    td_ctors td = [cd] -> lookup_ctor td (cd_name cd) = Some cd.
  Proof. unfold lookup_ctor; intros ->; cbn [find]; rewrite eqb_refl; reflexivity. Qed.

  Lemma assemble_typed op given FS :
    Forall (fun x => exists τ, nth_error FS (fst (fst x)) = Some τ /\
                               ⊢ᵖ[ge] snd (fst x) : τ ⇝ ctx_of (snd x)) given ->
    forall fs j qs Δ, (forall k, nth_error fs k = nth_error FS (j + k)) ->
    assemble op given j fs = Some (qs, Δ) -> ⊢ᵖ*[ge] qs : fs ⇝ ctx_of Δ.
  Proof.
    intros Hg fs; induction fs as [|τ fs IH]; intros j qs Δ Hfs H; simpl in H.
    - injection H as <- <-; constructor.
    - destruct (find (fun x => Nat.eqb (fst (fst x)) j) given) as [[[i q] Δ0]|] eqn:Hf.
      + destruct (assemble op given (S j) fs) as [[qs' Δs]|] eqn:Ha; [|discriminate].
        injection H as <- <-.
        apply find_some in Hf as [Hin Hi]; apply Nat.eqb_eq in Hi; simpl in Hi; subst i.
        rewrite Forall_forall in Hg; destruct (Hg _ Hin) as (τ' & Hτ' & Hq); simpl in *.
        specialize (Hfs 0) as H0; simpl in H0; rewrite Nat.add_0_r, Hτ' in H0.
        injection H0 as <-.
        unfold ctx_of; rewrite map_app; constructor; auto.
        eapply IH; eauto. intros k; specialize (Hfs (S k)); simpl in Hfs; rewrite Hfs; f_equal; lia.
      + destruct op; [|discriminate].
        destruct (assemble true given (S j) fs) as [[qs' Δs]|] eqn:Ha; [|discriminate].
        injection H as <- <-.
        change (ctx_of Δs) with (List.app [] (ctx_of Δs)).
        constructor; [constructor|].
        eapply IH; eauto. intros k; specialize (Hfs (S k)); simpl in Hfs; rewrite Hfs; f_equal; lia.
  Qed.

  Theorem pat_typed_el :
    (forall sp τ q Δ, ⊩ᵖ[E] sp : τ ⇝ q ⊣ Δ -> ⊢ᵖ[ge] q : τ ⇝ ctx_of Δ) /\
    (forall sp τ q Δ, ⊩ᶠ[E] sp : τ ⇝ q ⊣ Δ -> ⊢ᵖ[ge] q : τ ⇝ ctx_of Δ) /\
    (forall sps τs qs Δ, ⊩ᶠ*[E] sps : τs ⇝ qs ⊣ Δ -> ⊢ᵖ*[ge] qs : τs ⇝ ctx_of Δ) /\
    (forall fps names fs given, ⊩ⁿ[E] fps : names ; fs ⇝ given ->
       Forall (fun x => exists τ, nth_error fs (fst (fst x)) = Some τ /\
                                  ⊢ᵖ[ge] snd (fst x) : τ ⇝ ctx_of (snd x)) given).
  Proof.
    apply spat_mutind; intros; simpl in *.
    - constructor.
    - constructor.
    - subst τ; constructor.
    - constructor; auto.
    - (* constructor *)
      rewrite <- (app_nil_r (ctx_of Δ)).
      eapply P_Constr; [eapply ctor_fields_intro; eauto|].
      rewrite H2; apply pats_app; auto; apply wilds_typed.
    - rewrite <- (app_nil_r (ctx_of Δ)).
      apply P_Up; eapply P_Constr; [eapply ctor_fields_intro; eauto|].
      rewrite H2; apply pats_app; auto; apply wilds_typed.
    - (* record *)
      eapply P_Constr; [eapply ctor_fields_intro; eauto using lookup_ctor_single|].
      eapply assemble_typed; eauto. intros k; reflexivity.
    - auto.
    - constructor; auto.
    - auto.
    - constructor.
    - unfold ctx_of; rewrite map_app; constructor; auto.
    - constructor.
    - constructor; eauto.
  Qed.

  Lemma proj_pats_after i q : forall fs k, i < k ->
    ⊢ᵖ*[ge] proj_pats i q k (List.length fs) : fs ⇝ [].
  Proof.
    induction fs as [|τ fs IH]; intros k Hk; simpl; [constructor|].
    unfold proj_pats in *; simpl.
    destruct (Nat.eqb_spec k i); [lia|].
    change (@nil ty) with (List.app (@nil ty) []); constructor; [constructor|].
    apply IH; lia.
  Qed.

  Lemma proj_pats_typed i q τ Δ : ⊢ᵖ[ge] q : τ ⇝ Δ ->
    forall fs k, k <= i -> nth_error fs (i - k) = Some τ ->
    ⊢ᵖ*[ge] proj_pats i q k (List.length fs) : fs ⇝ Δ.
  Proof.
    intros Hq fs; induction fs as [|τ0 fs IH]; intros k Hk Hn.
    - destruct (i - k); discriminate.
    - unfold proj_pats in *; simpl.
      destruct (Nat.eqb_spec k i).
      + subst k; rewrite Nat.sub_diag in Hn; injection Hn as ->.
        rewrite <- (app_nil_r Δ); constructor; auto.
        apply proj_pats_after; lia.
      + change Δ with (List.app [] Δ); constructor; [constructor|].
        apply IH; [lia|].
        replace (i - k) with (S (i - S k)) in Hn by lia; exact Hn.
  Qed.

  Lemma field_proj_typed Λ Γ T ts i e e' τ :
    Γ ⊢[ge;[];Λ] e : TData T ts -> field_proj E T ts i e = Some (e', τ) ->
    Γ ⊢[ge;[];Λ] e' : τ.
  Proof.
    unfold field_proj; intros He H.
    destruct (lookup_ty ge T) as [td|] eqn:Htd; [|discriminate].
    destruct (td_ctors td) as [|cd [|]] eqn:Hc; try discriminate.
    destruct (nth_error (map (tsubst (inst ts)) (cd_fields cd)) i) as [τ0|] eqn:Hn; [|discriminate].
    assert (Hpat : forall q τr, ⊢ᵖ[ge] q : τ0 ⇝ [τr] ->
              Γ ⊢[ge;[];Λ] EMatch e τr [(PConstr (cd_name cd)
                 (proj_pats i q 0 (List.length (map (tsubst (inst ts)) (cd_fields cd)))), EVar 0)] : τr).
    { intros q τr Hq. eapply T_Match; [exact He|].
      apply Bs_cons with (Δ := [τr]); [|constructor; reflexivity|constructor].
      eapply P_Constr; [eapply ctor_fields_intro; eauto using lookup_ctor_single|].
      eapply proj_pats_typed; eauto; [lia|]. rewrite Nat.sub_0_r; exact Hn. }
    destruct τ0; injection H as <- <-; apply Hpat; repeat constructor.
  Qed.

  Theorem elab_typed :
    (forall L Γ s τ e, Γ ⊩[E;L] s ⇒ τ ⇝ e -> ctx_of Γ ⊢[ge;[];cc_of L] e : τ) /\
    (forall L Γ s τ e, Γ ⊩[E;L] s ⇐ τ ⇝ e -> ctx_of Γ ⊢[ge;[];cc_of L] e : τ) /\
    (forall L Γ s a τ e, Γ ⊩[E;L] s ⦂ a ⇒ τ ⇝ e -> ctx_of Γ ⊢[ge;[];cc_of L] e : τ) /\
    (forall L Γ cs τs τ bs, Γ ⊩ᵇ[E;L] cs : τs ⇐ τ ⇝ bs -> ctx_of Γ ⊢ᵇ[ge;[];cc_of L] bs : τs ⇒ τ) /\
    (forall L Γ ss τs es, Γ ⊩*[E;L] ss ⇒ τs ⇝ es -> ctx_of Γ ⊢*[ge;[];cc_of L] es : τs) /\
    (forall L Γ ss τs es, Γ ⊩*[E;L] ss ⇐ τs ⇝ es -> ctx_of Γ ⊢*[ge;[];cc_of L] es : τs).
  Proof.
    apply elab_mutind; intros; simpl in *.
    all: repeat match goal with
                | H : params_syn _ _ _ |- _ => pose proof (params_len _ _ _ H); clear H
                | H : params_ann _ _ _ |- _ => pose proof (params_len _ _ _ H); clear H
                | H : context [ctx_of (List.app (lam_ctx ?ps ?τs) ?Γ)] |- _ =>
                    rewrite lam_ctx_ctx in H by assumption
                | H : context [ctx_of (List.app ?Δ ?Γ)] |- _ => rewrite ctx_of_app in H
                | H : ⊩ᵖ[E] _ : _ ⇝ _ ⊣ _ |- _ => apply (proj1 pat_typed_el) in H
                end.
    all: try assumption.
    all: try solve [tc].
    (* operators *)
    all: try solve [eapply binop_typed; eauto].
    all: try solve [match goal with H : binop_res _ _ = _ |- _ => rewrite <- H end;
                    eapply binop_typed; eauto].
    (* lambdas *)
    all: try solve [constructor; apply eblock_typed; assumption].
    all: try solve [apply T_Lam; assumption].
    (* data types *)
    all: try solve [eapply field_proj_typed; eauto].
    all: try solve [eapply T_Constr; eauto;
                    match goal with H : cd_fields _ = [] |- _ => rewrite H end; repeat constructor].
    (* conversions and calls *)
    all: try solve [eapply coerce_typed; eauto].
    all: eapply wrap_call_typed; eauto; eapply T_Global; eauto.
  Qed.
End Typed.
