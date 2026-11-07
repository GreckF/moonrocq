(** * Surface: elaboration produces well-typed Core

    [elab_typed]: whatever the rules of [ElabSpec.v] relate a surface
    expression to is well typed in Core, at the synthesized or expected
    type, in the Core view of the environments ([ctx_of Γ], [cc_of L]).
    Source programs mention no store locations: [Σ = []]. *)

From Stdlib Require Import List ZArith String Bool Arith Lia.
From MoonRocq.Prelude Require Import Result EqDec Ident.
From MoonRocq.Core Require Import Syntax Prim Subst Typing Check.
From MoonRocq.Surface Require Import Syntax Resolve Base ElabSpec.
Import ListNotations.

Local Open Scope string_scope.

Section Typed.
  Variable E : senv.
  Abbreviation ge := (se_hdr E).

  (** The instance functions have the signatures resolution assumes. *)
  Hypothesis HI : Forall (inst_ok ge) (x_insts (se_x E)).

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

  (** *** Records *)

  Lemma Forall2_nth {A B} (R : A -> B -> Prop) l1 l2 k x :
    Forall2 R l1 l2 -> nth_error l1 k = Some x -> exists y, nth_error l2 k = Some y /\ R x y.
  Proof.
    intros H; revert k; induction H as [|a b l1 l2 Hab H IH]; intros [|k] Hk; simpl in *;
      try discriminate.
    - injection Hk as <-; eauto.
    - eauto.
  Qed.

  Lemma pos_of_spec j ixs k : pos_of j ixs = Some k -> nth_error ixs k = Some j.
  Proof.
    revert k; induction ixs as [|i ixs IH]; intros k H; simpl in *; [discriminate|].
    destruct (Nat.eqb_spec i j).
    - injection H as <-; subst; reflexivity.
    - destruct (pos_of j ixs) as [k'|]; simpl in H; [|discriminate].
      injection H as <-; simpl; auto.
  Qed.

  Lemma rec_vars_typed Λ Γ ixs taus fs vs :
    Forall2 (fun i τ => nth_error fs i = Some τ) ixs taus ->
    rec_vars ixs (List.length fs) = Some vs ->
    TTuple taus :: Γ ⊢*[ge;[];Λ] vs : fs.
  Proof.
    unfold rec_vars; intros Hf H.
    destruct (Nat.eqb (List.length ixs) (List.length fs)); [|discriminate].
    assert (Hgen : forall fsl a vs,
               (forall d, nth_error fsl d = nth_error fs (a + d)) ->
               all_some (map (fun j => option_map (fun k => EProj (EVar 0) k) (pos_of j ixs))
                             (seq a (List.length fsl))) = Some vs ->
               TTuple taus :: Γ ⊢*[ge;[];Λ] vs : fsl).
    { induction fsl as [|τ fsl IH]; intros a vs0 Hd Ha; simpl in Ha.
      - injection Ha as <-; constructor.
      - destruct (pos_of a ixs) as [k|] eqn:Hp; simpl in Ha; [|discriminate].
        destruct (all_some (map _ (seq (S a) (Datatypes.length fsl)))) as [vs'|] eqn:Hr;
          simpl in Ha; [|discriminate].
        injection Ha as <-.
        apply pos_of_spec in Hp.
        destruct (Forall2_nth _ _ _ _ _ Hf Hp) as (τk & Hτk & Hfa).
        specialize (Hd 0) as H0; simpl in H0; rewrite Nat.add_0_r, Hfa in H0.
        injection H0 as ->.
        constructor.
        + eapply T_Proj; [constructor; reflexivity|exact Hτk].
        + eapply IH; [|exact Hr]. intros d; specialize (Hd (S d)); simpl in Hd; rewrite Hd; f_equal; lia. }
    eapply Hgen; [|exact H]. intros d; reflexivity.
  Qed.

  Lemma record_typed Λ Γ T ts td cd (names : list ident) es ixs vs taus :
    lookup_ty ge T = Some td -> td_ctors td = [cd] ->
    List.length (cd_fields cd) = List.length names ->
    Γ ⊢*[ge;[];Λ] es : taus ->
    Forall2 (fun i τ => nth_error (map (tsubst (inst ts)) (cd_fields cd)) i = Some τ) ixs taus ->
    rec_vars ixs (List.length names) = Some vs ->
    List.length ts = td_tparams td ->
    Γ ⊢[ge;[];Λ] ELet (ETuple es) (EConstr T (cd_name cd) ts (ETuple vs)) : TData T ts.
  Proof.
    intros Htd Hc Hlen Hes Hf Hv Hts.
    eapply T_Let; [constructor; exact Hes|].
    eapply T_Constr; eauto using lookup_ctor_single.
    constructor. eapply rec_vars_typed; eauto.
    rewrite length_map, Hlen; exact Hv.
  Qed.

  (** *** State and loops *)

  Lemma names_ctx_ctx xs τs Γ :
    List.length xs = List.length τs ->
    ctx_of (List.app (names_ctx xs τs) Γ) = List.app τs (ctx_of Γ).
  Proof.
    unfold ctx_of, names_ctx; rewrite map_app; intros Hl; f_equal.
    revert τs Hl; induction xs as [|x xs IH]; intros [|τ τs] Hl; simpl in *;
      try discriminate; auto.
    rewrite IH; auto.
  Qed.

  Lemma eblock_typed' Λ Γ r b :
    Γ ⊢[ge;[];push_lbl ([], r) Λ] b : r -> Γ ⊢[ge;[];Λ] eblock r b : r.
  Proof. intros Hb; eapply T_Loop; [constructor; constructor|exact Hb]. Qed.

  Lemma upd_rhs_typed Λ Γ p op τ cur v e :
    upd_rhs p op τ cur v e ->
    Γ ⊢[ge;[];Λ] cur : τ -> Γ ⊢[ge;[];Λ] v : τ -> Γ ⊢[ge;[];Λ] e : τ.
  Proof.
    destruct op as [o|]; simpl; intros H Hc Hv.
    - destruct H as [Hr He]; pose proof (binop_typed _ _ _ _ _ _ _ _ He Hc Hv) as H'; rewrite Hr in H'; exact H'.
    - subst; exact Hv.
  Qed.

  Lemma has_types_seq Λ Γ (f : nat -> expr) : forall τs k,
    (forall i τ, nth_error τs i = Some τ -> Γ ⊢[ge;[];Λ] f (k + i) : τ) ->
    Γ ⊢*[ge;[];Λ] map f (seq k (List.length τs)) : τs.
  Proof.
    induction τs as [|τ τs IH]; intros k H; simpl; constructor.
    - rewrite <- (Nat.add_0_r k); apply (H 0); reflexivity.
    - apply IH; intros i τ' Hi. replace (S k + i) with (k + S i) by lia; apply (H (S i)); exact Hi.
  Qed.

  Lemma upd_next_typed Λ G off names τs us :
    List.length names = List.length τs ->
    (forall i τ, nth_error τs i = Some τ -> nth_error G (off + i) = Some τ) ->
    Forall (fun yu => exists j τ, index_of (fst yu) names = Some j /\ nth_error τs j = Some τ /\
                                  G ⊢[ge;[];Λ] snd yu : τ) us ->
    G ⊢*[ge;[];Λ] upd_next off names us : τs.
  Proof.
    intros Hl Hoff Hus; unfold upd_next; rewrite Hl.
    apply has_types_seq; intros i τ Hi; simpl.
    destruct (find _ us) as [[y u]|] eqn:Hf.
    - apply find_some in Hf as [Hin Hj].
      rewrite Forall_forall in Hus; destruct (Hus _ Hin) as (j & τ' & Hy & Hτ' & Hu); simpl in *.
      rewrite Hy in Hj; apply Nat.eqb_eq in Hj; subst j.
      rewrite Hi in Hτ'; injection Hτ' as <-; exact Hu.
    - constructor; apply Hoff; exact Hi.
  Qed.

  Lemma for_next_typed Λ G names τs us :
    List.length names = List.length τs ->
    Forall (fun yu => exists j τ, index_of (fst yu) names = Some j /\ nth_error τs j = Some τ /\
                                  TUnit :: List.app τs G ⊢[ge;[];Λ] snd yu : τ) us ->
    TUnit :: List.app τs G ⊢*[ge;[];Λ] for_next names us : τs.
  Proof.
    intros Hl Hus; apply upd_next_typed; auto.
    intros i τ Hi; simpl. rewrite nth_error_app1; auto.
    apply nth_error_Some; congruence.
  Qed.

  Lemma while_loop_typed Λ Γ τ c b nb :
    Γ ⊢[ge;[];push_lbl ([], τ) Λ] c : TBool ->
    Γ ⊢[ge;[];push_lbl ([], τ) Λ] b : TUnit ->
    Γ ⊢[ge;[];push_lbl ([], τ) Λ] nb : τ ->
    Γ ⊢[ge;[];Λ] while_loop τ c b nb : τ.
  Proof.
    intros Hc Hb Hnb; unfold while_loop.
    eapply T_Loop; [constructor; constructor|]; simpl.
    constructor; auto.
    eapply T_Let; [exact Hb|].
    eapply T_Jump; [reflexivity|]; simpl; constructor; constructor.
  Qed.

  Lemma for_loop_typed Λ Γ es τs τ c b names us nb :
    Γ ⊢*[ge;[];Λ] es : τs ->
    match c with
    | Some c0 => List.app τs Γ ⊢[ge;[];push_lbl (τs, τ) Λ] c0 : TBool /\
                 List.app τs Γ ⊢[ge;[];push_lbl (τs, τ) Λ] nb : τ
    | None => True
    end ->
    List.app τs Γ ⊢[ge;[];push_lbl ([], TUnit) (push_lbl (τs, τ) Λ)] b : TUnit ->
    List.length names = List.length τs ->
    Forall (fun yu => exists j τ', index_of (fst yu) names = Some j /\ nth_error τs j = Some τ' /\
                                   TUnit :: List.app τs Γ ⊢[ge;[];push_lbl (τs, τ) Λ] snd yu : τ') us ->
    Γ ⊢[ge;[];Λ] for_loop es τs τ c b names us nb : τ.
  Proof.
    intros Hes Hc Hb Hl Hus; unfold for_loop.
    assert (Hstep : List.app τs Γ ⊢[ge;[];push_lbl (τs, τ) Λ]
                      ELet (eblock TUnit b) (EJump CCont 0 (ETuple (for_next names us)) τ) : τ).
    { eapply T_Let; [apply eblock_typed'; exact Hb|].
      eapply T_Jump; [reflexivity|]; simpl; constructor.
      apply for_next_typed; auto. }
    eapply T_Loop; [constructor; exact Hes|].
    destruct c as [c0|]; [destruct Hc; constructor; auto|exact Hstep].
  Qed.

  Lemma field_cell_typed Λ Γ T ts i c n t e b :
    field_cell E T ts i = Some (c, n, t) ->
    Γ ⊢[ge;[];Λ] e : TData T ts ->
    TRef t :: Γ ⊢[ge;[];Λ] b : TUnit ->
    Γ ⊢[ge;[];Λ] EMatch e TUnit [(PConstr c (proj_pats i PVar 0 n), b)] : TUnit.
  Proof.
    unfold field_cell; intros H He Hb.
    destruct (lookup_ty ge T) as [td|] eqn:Htd; [|discriminate].
    destruct (td_ctors td) as [|cd [|]] eqn:Hc; try discriminate.
    destruct (nth_error (map (tsubst (inst ts)) (cd_fields cd)) i) as [τ0|] eqn:Hn; [|discriminate].
    destruct τ0; try discriminate.
    injection H as H1 H2 H3; subst.
    eapply T_Match; [exact He|].
    apply Bs_cons with (Δ := [TRef t]); [|exact Hb|constructor].
    eapply P_Constr; [eapply ctor_fields_intro; eauto using lookup_ctor_single|].
    eapply proj_pats_typed; [constructor| |]; [lia|]. rewrite Nat.sub_0_r; exact Hn.
  Qed.

  Lemma ref_new_typed Λ Γ t v :
    ref_ok E -> Γ ⊢[ge;[];Λ] v : t ->
    Γ ⊢[ge;[];Λ] EConstr "Ref" "Ref" [t] (ETuple [EMem (MRef t) [v]]) : TData "Ref" [t].
  Proof.
    unfold ref_ok; intros (td & cd & Htd & Hn & Hc & Hf) Hv.
    eapply T_Constr; [exact Htd|rewrite Hn; reflexivity|exact Hc|]; rewrite Hf; simpl.
    constructor; constructor; [|constructor].
    apply (T_Mem _ _ _ _ (MRef t) [v]); simpl; constructor; auto; constructor.
  Qed.

  Lemma index_upd_typed Λ Γ p o k t a i v rhs :
    Γ ⊢[ge;[];Λ] a : TArray k t ->
    TArray k t :: Γ ⊢[ge;[];Λ] i : TIndex ->
    TIndex :: TArray k t :: Γ ⊢[ge;[];Λ] v : t ->
    binop_res o t = t ->
    elab_binop p o t (EMem (MIndex k t) [EVar 1; EVar 0]) v = Ok rhs ->
    Γ ⊢[ge;[];Λ] ELet a (ELet i (EMem (MSetIndex k t) [EVar 1; EVar 0; rhs])) : TUnit.
  Proof.
    intros Ha Hi Hv Hr Hb.
    eapply T_Let; [exact Ha|]; eapply T_Let; [exact Hi|].
    apply (T_Mem _ _ _ _ (MSetIndex k t) [_; _; _]); simpl.
    constructor; [constructor; reflexivity|].
    constructor; [constructor; reflexivity|].
    constructor; [|constructor].
    assert (Hc : TIndex :: TArray k t :: Γ ⊢[ge;[];Λ] EMem (MIndex k t) [EVar 1; EVar 0] : t).
    { apply (T_Mem _ _ _ _ (MIndex k t) [_; _]); simpl.
      constructor; [constructor; reflexivity|constructor; [constructor; reflexivity|constructor]]. }
    pose proof (binop_typed _ _ _ _ _ _ _ _ Hb Hc Hv) as He; rewrite Hr in He; exact He.
  Qed.

  (** *** [for .. in] *)

  Lemma nth_skip (A R : list ty) i : nth_error (List.app A R) (List.length A + i) = nth_error R i.
  Proof. rewrite nth_error_app2 by lia; f_equal; lia. Qed.

  Lemma nth_at_len (A R : list ty) x : nth_error (List.app A (x :: R)) (List.length A) = Some x.
  Proof. rewrite <- (Nat.add_0_r (List.length A)), nth_skip; reflexivity. Qed.

  Lemma nth_at_len1 (A R : list ty) x y : nth_error (List.app A (x :: y :: R)) (S (List.length A)) = Some y.
  Proof. rewrite <- Nat.add_1_r, nth_skip; reflexivity. Qed.

  Definition fi_inner (it : iter_src) (τs : list ty) (G : ctx) : ctx :=
    List.app (fi_ivs it) (List.app τs (fi_t2 it :: fi_t1 it :: G)).

  Lemma fl_ctx_ctx it names τs Γ :
    List.length names = List.length τs ->
    ctx_of (fl_ctx it names τs Γ) = fi_inner it τs (ctx_of Γ).
  Proof.
    intros Hl; unfold fl_ctx, fi_inner; rewrite ctx_of_app, names_ctx_ctx by exact Hl.
    f_equal. unfold ctx_of; rewrite map_map; simpl; apply map_id.
  Qed.

  Lemma inner_bound it τs G : nth_error (fi_inner it τs G) (fi_n it τs) = Some (fi_t2 it).
  Proof.
    unfold fi_inner, fi_n. rewrite nth_skip. apply nth_at_len.
  Qed.

  Lemma inner_src it τs G : nth_error (fi_inner it τs G) (S (fi_n it τs)) = Some (fi_t1 it).
  Proof.
    unfold fi_inner, fi_n. rewrite <- Nat.add_succ_r, nth_skip. apply nth_at_len1.
  Qed.

  Ltac var_tac :=
    match goal with
    | |- _ ⊢[_;_;_] EVar ?n : _ => constructor; first [reflexivity | apply inner_bound | apply inner_src | eassumption]
    end.

  Ltac fi_tac := repeat (first [var_tac | prim | econstructor]; simpl).

  Lemma fi_cond_typed Λ it τs G : fi_inner it τs G ⊢[ge;[];Λ] fi_cond it (fi_n it τs) : TBool.
  Proof.
    destruct it as [rk kk|k t]; [destruct rk|]; cbn [fi_cond].
    all: try (apply (T_Prim _ _ _ _ (PIntCmp _ _) [_; _]); cbn [prim_sig fst snd];
              constructor; [constructor; reflexivity|constructor; [constructor; apply inner_bound|constructor]]).
    all: constructor; [constructor; reflexivity|constructor; reflexivity|].
    all: apply (T_Prim _ _ _ _ (PIntCmp _ _) [_; _]); cbn [prim_sig fst snd];
         constructor; [constructor; reflexivity|constructor; [constructor; apply inner_bound|constructor]].
  Qed.

  Lemma fi_elem_typed Λ it τs G : fi_inner it τs G ⊢[ge;[];Λ] fi_elem it (fi_n it τs) : fi_elem_ty it.
  Proof.
    destruct it as [rk kk|k t]; [destruct rk|]; cbn [fi_elem fi_elem_ty].
    all: try (constructor; reflexivity).
    - apply (T_Prim _ _ _ _ (PIntArith _ _) [_; _]); cbn [prim_sig fst snd].
      constructor; [constructor; reflexivity|constructor; [constructor|constructor]].
    - apply (T_Mem _ _ _ _ (MIndex _ _) [_; _]); cbn [mem_sig fst snd].
      constructor; [constructor; apply inner_src|constructor; [constructor; reflexivity|constructor]].
  Qed.

  Lemma fi_init_typed Λ it G : fi_t2 it :: fi_t1 it :: G ⊢*[ge;[];Λ] fi_init it : fi_ivs it.
  Proof.
    destruct it as [rk kk|k t]; [destruct rk|]; cbn [fi_init fi_ivs].
    all: repeat constructor.
  Qed.

  Lemma fi_next_typed Λ it τs G D X :
    X :: List.app D (fi_inner it τs G) ⊢*[ge;[];Λ] fi_next it (List.length D) (fi_n it τs) : fi_ivs it.
  Proof.
    assert (Hv : forall τ, nth_error (fi_inner it τs G) 0 = Some τ ->
                 X :: List.app D (fi_inner it τs G) ⊢[ge;[];Λ] EVar (1 + List.length D) : τ).
    { intros τ H; constructor; simpl; rewrite <- (Nat.add_0_r (List.length D)), nth_skip; exact H. }
    assert (Hb : X :: List.app D (fi_inner it τs G) ⊢[ge;[];Λ] EVar (1 + List.length D + fi_n it τs) : fi_t2 it).
    { constructor; simpl; rewrite nth_skip; apply inner_bound. }
    destruct it as [rk kk|k t]; [destruct rk|]; cbn [fi_next fi_ivs fi_t2] in *.
    all: repeat (first [ apply Hv; reflexivity | exact Hb
                       | apply (T_Prim _ _ _ _ (PIntCmp _ _) [_; _]); cbn [prim_sig fst snd]
                       | apply (T_Prim _ _ _ _ (PIntArith _ _) [_; _]); cbn [prim_sig fst snd]
                       | constructor ]).
  Qed.

  Lemma fi_pat_scrut Λ it pats q Δ scrut sty τs G :
    fi_pat E it pats (fi_elem it (fi_n it τs)) q Δ scrut sty ->
    fi_inner it τs G ⊢[ge;[];Λ] scrut : sty.
  Proof.
    intros H; inversion H; subst.
    - apply fi_elem_typed.
    - constructor. constructor; [constructor; reflexivity|].
      constructor; [apply (fi_elem_typed Λ (IArray k t))|constructor].
  Qed.

  Lemma fi_pat_pat it pats elem q Δ scrut sty :
    fi_pat E it pats elem q Δ scrut sty -> ⊢ᵖ[ge] q : sty ⇝ ctx_of Δ.
  Proof.
    destruct 1 as [sp elem q Δ Hp|k t sp1 sp2 elem q1 q2 Δ1 Δ2 Hit Hp1 Hp2].
    - exact (proj1 pat_typed_el _ _ _ _ Hp).
    - constructor. rewrite ctx_of_app, <- (app_nil_r (ctx_of Δ2)).
      constructor; [exact (proj1 pat_typed_el _ _ _ _ Hp1)|].
      constructor; [exact (proj1 pat_typed_el _ _ _ _ Hp2)|constructor].
  Qed.

  Lemma forin_typed Λ G it e1 e2 es τs τ q scrut sty D b names us nb :
    G ⊢[ge;[];Λ] e1 : fi_t1 it ->
    fi_t1 it :: G ⊢[ge;[];Λ] e2 : fi_t2 it ->
    fi_t2 it :: fi_t1 it :: G ⊢*[ge;[];Λ] es : τs ->
    fi_inner it τs G ⊢[ge;[];push_lbl (List.app (fi_ivs it) τs, τ) Λ] scrut : sty ->
    ⊢ᵖ[ge] q : sty ⇝ D ->
    List.app D (fi_inner it τs G)
      ⊢[ge;[];push_lbl ([], TUnit) (push_lbl ([], TTuple τs) (push_lbl (List.app (fi_ivs it) τs, τ) Λ))] b : TUnit ->
    Forall (fun yu => exists j τ', index_of (fst yu) names = Some j /\ nth_error τs j = Some τ' /\
              TUnit :: List.app D (fi_inner it τs G)
                ⊢[ge;[];push_lbl ([], TTuple τs) (push_lbl (List.app (fi_ivs it) τs, τ) Λ)] snd yu : τ') us ->
    fi_inner it τs G ⊢[ge;[];push_lbl (List.app (fi_ivs it) τs, τ) Λ] nb : τ ->
    List.length names = List.length τs ->
    G ⊢[ge;[];Λ] forin_loop it e1 e2 es τs τ q scrut (List.length D) b names us nb : τ.
  Proof.
    intros H1 H2 Hes Hs Hq Hb Hus Hnb Hl; unfold forin_loop.
    eapply T_Let; [exact H1|]; eapply T_Let; [exact H2|].
    eapply T_Loop; [constructor; apply has_types_app; [apply fi_init_typed|exact Hes]|].
    rewrite <- app_assoc; fold (fi_inner it τs G).
    constructor; [apply fi_cond_typed| |exact Hnb].
    eapply T_Match; [exact Hs|].
    apply Bs_cons with (Δ := D); [exact Hq| |constructor].
    eapply T_Let.
    - apply eblock_typed'. eapply T_Let; [apply eblock_typed'; exact Hb|].
      constructor. apply upd_next_typed; auto.
      intros i τ' Hi. simpl. unfold fi_inner.
      rewrite <- Nat.add_assoc, nth_skip, nth_skip.
      rewrite nth_error_app1; [exact Hi|apply nth_error_Some; congruence].
    - eapply T_Jump; [reflexivity|]; simpl.
      constructor; apply has_types_app; [apply fi_next_typed|].
      rewrite Hl. apply has_types_seq; intros i τ' Hi; simpl.
      eapply T_Proj; [constructor; reflexivity|exact Hi].
  Qed.

  (** *** Errors *)

  Lemma fail_typed Λ Γ a :
    failure_ok E -> Γ ⊢[ge;[];Λ] a : TString ->
    Γ ⊢[ge;[];Λ] fail_val a : TData "Failure" [].
  Proof.
    intros (td & cd & Htd & Hn & Hc & Hf) Ha; unfold fail_val.
    eapply T_Constr; [exact Htd|rewrite Hn; reflexivity|exact Hc|].
    rewrite Hf; simpl; constructor; constructor; [exact Ha|constructor].
  Qed.

  Lemma raise_typed Λ Γ e τ :
    Γ ⊢[ge;[];Λ] e : cc_exn Λ -> Γ ⊢[ge;[];Λ] ERaise e τ : τ.
  Proof. intros He; eapply T_Raise; [exact He|right; reflexivity]. Qed.

  Lemma try_typed Λ Γ b τe τ0 τ hbs k :
    Γ ⊢[ge;[];with_exn τe Λ] b : τ0 ->
    τe :: Γ ⊢ᵇ[ge;[];Λ] hbs : τe ⇒ τ ->
    τ0 :: Γ ⊢[ge;[];Λ] k : τ ->
    Γ ⊢[ge;[];Λ] ETry b τe (EMatch (EVar 0) τ hbs) k : τ.
  Proof.
    intros Hb Hh Hk; eapply T_Try; [exact Hb| |exact Hk].
    eapply T_Match; [constructor; reflexivity|exact Hh].
  Qed.

  Lemma noraise_typed Λ Γ τ0 τ kbs :
    τ0 :: Γ ⊢ᵇ[ge;[];Λ] kbs : τ0 ⇒ τ -> τ0 :: Γ ⊢[ge;[];Λ] EMatch (EVar 0) τ kbs : τ.
  Proof. intros Hk; eapply T_Match; [constructor; reflexivity|exact Hk]. Qed.

  (** *** Traits, methods, objects *)

  Lemma asm_typed Λ Γ Tr τ d :
    In (Tr, τ, d) (asm_of E Γ) -> ctx_of Γ ⊢[ge;[];Λ] d : TData Tr [τ].
  Proof.
    unfold asm_of; rewrite in_flat_map; intros ([[Tr' τ'] x] & _ & Hin); simpl in Hin.
    destruct (lookup_local x Γ) as [i|]; [|contradiction].
    destruct (nth_error (ctx_of Γ) i) as [t|] eqn:Hn; [|contradiction].
    destruct (eq_dec t (TData Tr' [τ'])) as [->|]; [|contradiction].
    destruct Hin as [Hin|[]]; injection Hin as <- <- <-.
    constructor; exact Hn.
  Qed.

  Lemma dict_typed Λ Γ Tr τ d :
    dict E Γ Tr τ d -> ctx_of Γ ⊢[ge;[];Λ] d : TData Tr [τ].
  Proof.
    intros H; eapply entails_typed; [exact HI| |exact H].
    intros; apply asm_typed; assumption.
  Qed.

  Lemma dicts_typed Λ Γ τs ds : dicts E Γ τs ds -> ctx_of Γ ⊢*[ge;[];Λ] ds : τs.
  Proof.
    induction 1 as [|t d τs ds (Tr & τ & -> & Hd) _ IH]; constructor; auto.
    apply dict_typed; exact Hd.
  Qed.

  Lemma call_typed L Γ g fd ts n ds es :
    lookup_fn ge g = Some fd -> List.length ts = fd_tparams fd ->
    dicts E Γ (map (tsubst (inst ts)) (firstn n (fd_params fd))) ds ->
    ctx_of Γ ⊢*[ge;[];cc_of L] es : map (tsubst (inst ts)) (skipn n (fd_params fd)) ->
    call_ok E L (tsubst (inst ts) (fd_eff fd)) ->
    ctx_of Γ ⊢[ge;[];cc_of L] wrap_call L (tsubst (inst ts) (fd_eff fd)) (tsubst (inst ts) (fd_ret fd))
                                         (EGlobal g ts) (List.app ds es) : tsubst (inst ts) (fd_ret fd).
  Proof.
    intros Hfd Hts Hds Hes Hok.
    eapply wrap_call_typed; [eapply T_Global; eauto| |exact Hok].
    rewrite <- (firstn_skipn n (fd_params fd)), map_app.
    apply has_types_app; [apply dicts_typed|]; assumption.
  Qed.

  Lemma meth_call_typed L Γ g fd ts n p0 ps ds r' τr es :
    lookup_fn ge g = Some fd -> List.length ts = fd_tparams fd ->
    skipn n (fd_params fd) = p0 :: ps -> tsubst (inst ts) p0 = τr ->
    dicts E Γ (map (tsubst (inst ts)) (firstn n (fd_params fd))) ds ->
    ctx_of Γ ⊢[ge;[];cc_of L] r' : τr ->
    ctx_of Γ ⊢*[ge;[];cc_of L] es : map (tsubst (inst ts)) ps ->
    call_ok E L (tsubst (inst ts) (fd_eff fd)) ->
    ctx_of Γ ⊢[ge;[];cc_of L] wrap_call L (tsubst (inst ts) (fd_eff fd)) (tsubst (inst ts) (fd_ret fd))
                                         (EGlobal g ts) (List.app ds (r' :: es)) : tsubst (inst ts) (fd_ret fd).
  Proof.
    intros Hfd Hts Hs Hp Hds Hr Hes Hok.
    eapply call_typed; eauto.
    rewrite Hs; simpl; rewrite Hp; constructor; assumption.
  Qed.

  Lemma obj_of_ty τ Tr : obj_of E τ = Some Tr -> τ = TData (obj_name Tr) [].
  Proof.
    unfold obj_of; intros H.
    destruct τ; try discriminate.
    match goal with l : list ty |- _ => destruct l; [|discriminate] end.
    apply find_some in H as [_ H]; apply String.eqb_eq in H; subst; reflexivity.
  Qed.

  Lemma ctx_of_nones ps : ctx_of (map (fun t => (None, t)) ps) = ps.
  Proof. unfold ctx_of; rewrite map_map; apply map_id. Qed.

  Lemma obj_meth_typed Λ Γ τ sm fty f :
    obj_meth E ((None, τ) :: Γ) τ sm fty f -> τ :: ctx_of Γ ⊢[ge;[];Λ] f : fty.
  Proof.
    intros (ti & i & sg & ps & r & ε & d & mv & _ & _ & -> & Hd & Hp & ->).
    apply T_Lam. eapply T_App; [| |right; reflexivity].
    - eapply field_proj_typed; [|exact Hp].
      pose proof (dict_typed (mk_cctx [] ε) _ _ _ _ Hd) as Hd'.
      rewrite ctx_of_app, ctx_of_nones in Hd'. exact Hd'.
    - constructor.
      + constructor. rewrite nth_error_app2 by lia. rewrite Nat.sub_diag; reflexivity.
      + apply has_types_seq; intros j t Hj; simpl; constructor.
        rewrite nth_error_app1; [exact Hj|]. apply nth_error_Some; congruence.
  Qed.

  Lemma obj_meths_typed Λ Γ τ : forall sms ftys fs,
    obj_meths E ((None, τ) :: Γ) τ sms ftys fs -> τ :: ctx_of Γ ⊢*[ge;[];Λ] fs : ftys.
  Proof.
    induction sms as [|sm sms IH]; intros [|t ts] [|f fs] H; simpl in H; try contradiction.
    - constructor.
    - destruct H as [H1 H2]; constructor; [eapply obj_meth_typed; exact H1 | apply IH; exact H2].
  Qed.

  Lemma coerce_typed Λ Γ e τ τ' e' :
    ⊩ᶜ[E;Γ] e : τ ≼ τ' ⇝ e' ->
    ctx_of Γ ⊢[ge;[];Λ] e : τ -> ctx_of Γ ⊢[ge;[];Λ] e' : τ'.
  Proof.
    destruct 1 as [|e0 T (td & Htd & Herr)|e0 τ0 τ1 Tr td cd fs Ho Hne Htd Hn Hc Hfs]; intros He; auto.
    - eapply T_Up; eauto.
    - rewrite (obj_of_ty _ _ Ho). eapply T_Let; [exact He|].
      eapply T_Constr; [exact Htd|rewrite Hn; reflexivity|exact Hc|].
      constructor. eapply obj_meths_typed; exact Hfs.
  Qed.

  Lemma tcall_typed L Γ Tr τs i d mv ps r ε es :
    dict E Γ Tr τs d ->
    field_proj E Tr [τs] i d = Some (mv, TArrow ps r ε) ->
    ctx_of Γ ⊢*[ge;[];cc_of L] es : ps ->
    call_ok E L ε ->
    ctx_of Γ ⊢[ge;[];cc_of L] wrap_call L ε r mv es : r.
  Proof.
    intros Hd Hp Hes Hok; eapply wrap_call_typed; [|exact Hes|exact Hok].
    eapply field_proj_typed; [apply dict_typed; exact Hd|exact Hp].
  Qed.

  Theorem elab_typed :
    (forall L Γ s τ e, Γ ⊩[E;L] s ⇒ τ ⇝ e -> ctx_of Γ ⊢[ge;[];cc_of L] e : τ) /\
    (forall L Γ s τ e, Γ ⊩[E;L] s ⇐ τ ⇝ e -> ctx_of Γ ⊢[ge;[];cc_of L] e : τ) /\
    (forall L Γ s a τ e, Γ ⊩[E;L] s ⦂ a ⇒ τ ⇝ e -> ctx_of Γ ⊢[ge;[];cc_of L] e : τ) /\
    (forall L Γ cs τs τ bs, Γ ⊩ᵇ[E;L] cs : τs ⇐ τ ⇝ bs -> ctx_of Γ ⊢ᵇ[ge;[];cc_of L] bs : τs ⇒ τ) /\
    (forall L Γ fes names fs es ixs, Γ ⊩ʳ[E;L] fes : names ; fs ⇝ es ; ixs ->
       exists taus, ctx_of Γ ⊢*[ge;[];cc_of L] es : taus /\
                    Forall2 (fun i τ => nth_error fs i = Some τ) ixs taus) /\
    (forall L Γ inits τs es, Γ ⊩ⁱ[E;L] inits ⇒ τs ⇝ es ->
       ctx_of Γ ⊢*[ge;[];cc_of L] es : τs /\ List.length inits = List.length τs) /\
    (forall L Γ upds names τs us, Γ ⊩ᵘ[E;L] upds : names ; τs ⇝ us ->
       Forall (fun yu => exists j τ, index_of (fst yu) names = Some j /\ nth_error τs j = Some τ /\
                                     ctx_of Γ ⊢[ge;[];cc_of L] snd yu : τ) us) /\
    (forall L Γ src e1 e2 it, Γ ⊩ˢ[E;L] src ⇝ e1 ; e2 ; it ->
       ctx_of Γ ⊢[ge;[];cc_of L] e1 : fi_t1 it /\ fi_t1 it :: ctx_of Γ ⊢[ge;[];cc_of L] e2 : fi_t2 it) /\
    (forall L Γ os τ oe, Γ ⊩ᵒ[E;L] os ⇐ τ ⇝ oe ->
       forall e, oe = Some e -> ctx_of Γ ⊢[ge;[];cc_of L] e : τ) /\
    (forall L Γ ss τs es, Γ ⊩*[E;L] ss ⇒ τs ⇝ es -> ctx_of Γ ⊢*[ge;[];cc_of L] es : τs) /\
    (forall L Γ ss τs es, Γ ⊩*[E;L] ss ⇐ τs ⇝ es -> ctx_of Γ ⊢*[ge;[];cc_of L] es : τs).
  Proof.
    apply elab_mutind; intros; simpl in *.
    all: repeat match goal with
                | H : params_syn _ _ _ |- _ => pose proof (params_len _ _ _ H); clear H
                | H : params_ann _ _ _ |- _ => pose proof (params_len _ _ _ H); clear H
                | H : context [ctx_of (List.app (lam_ctx ?ps ?τs) ?Γ)] |- _ =>
                    rewrite lam_ctx_ctx in H by assumption
                | H : _ /\ List.length ?l = List.length ?τs |- _ =>
                    let H1 := fresh "Hes" in let H2 := fresh "Hlen" in destruct H as [H1 H2]
                | Hl : List.length ?l = List.length ?τs,
                  H : context [ctx_of (List.app (names_ctx (map fst ?l) ?τs) ?Γ)] |- _ =>
                    rewrite names_ctx_ctx in H by (rewrite length_map; exact Hl)
                | Hl : List.length ?l = List.length ?τs,
                  H : context [ctx_of (fl_ctx ?it (map fst ?l) ?τs ?Γ)] |- _ =>
                    rewrite fl_ctx_ctx in H by (rewrite length_map; exact Hl)
                | H : context [map snd (fl_ctx ?it ?xs ?τs ?Γ)] |- _ =>
                    change (map snd (fl_ctx it xs τs Γ)) with (ctx_of (fl_ctx it xs τs Γ)) in H
                | H : context [map snd (List.app (names_ctx ?xs ?τs) ?Γ)] |- _ =>
                    change (map snd (List.app (names_ctx xs τs) Γ))
                      with (ctx_of (List.app (names_ctx xs τs) Γ)) in H
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
    (* records *)
    all: try solve [exists []; split; constructor].
    all: try solve [match goal with H : exists _, _ |- _ => destruct H as (taus & ? & ?) end;
                    eexists; split; [constructor; [first [eassumption | tc] | eassumption] | constructor; eauto]].
    all: try solve [match goal with H : exists _, _ |- _ => destruct H as (taus & ? & ?) end;
                    eapply record_typed; eauto].
    (* data types *)
    all: try solve [eapply field_proj_typed; eauto].
    all: try solve [eapply T_Constr; eauto;
                    match goal with H : cd_fields _ = [] |- _ => rewrite H end; repeat constructor].
    (* state and loops *)
    all: try solve [eapply upd_rhs_typed; [eassumption| |eassumption]; tc].
    all: try solve [apply (T_Mem _ _ _ _ (MSet _) [_; _]); simpl; constructor; [tc|constructor; [|constructor]];
                    eapply upd_rhs_typed; [eassumption| |eassumption]; tc].
    all: try solve [eapply field_cell_typed; eauto;
                    apply (T_Mem _ _ _ _ (MSet _) [_; _]); simpl; constructor; [tc|constructor; [|constructor]];
                    eapply upd_rhs_typed; [eassumption| |eassumption]; tc].
    all: try solve [eapply index_upd_typed; eauto].
    all: try solve [eapply ref_new_typed; eauto].
    all: try solve [eapply while_loop_typed; eauto; constructor].
    all: try discriminate.
    all: try solve [match goal with H : Some _ = Some _ |- _ => injection H as <- end; eauto].
    all: try solve [match goal with |- _ ⊢[_;_;_] for_loop _ _ _ None _ _ _ _ : _ =>
                      eapply for_loop_typed; [eassumption | exact I | eassumption
                                             | rewrite length_map; eassumption | eassumption] end].
    all: try solve [match goal with |- _ ⊢[_;_;_] for_loop _ _ _ ?c _ _ _ _ : _ => try destruct c end;
                    eapply for_loop_typed; eauto; try (rewrite length_map; assumption);
                    simpl; try split; first [solve [eauto] | constructor]].
    all: try solve [constructor; apply eblock_typed'; assumption].
    (* for .. in *)
    all: try solve [split; [eassumption|];
                    apply (T_Mem _ _ _ _ (MLength _ _) [_]); simpl; constructor; [constructor; reflexivity|constructor]].
    all: try solve [split; eassumption].
    all: try solve [match goal with Hs : _ /\ _ |- _ ⊢[_;_;_] forin_loop _ _ _ _ _ _ _ _ _ _ _ _ _ : _ =>
                      destruct Hs end;
                    match goal with Hp : fi_pat _ _ _ _ _ ?Δ _ _ |- _ =>
                      replace (List.length Δ) with (List.length (ctx_of Δ)) by apply length_map;
                      eapply forin_typed;
                      [eassumption | eassumption | eassumption | eapply fi_pat_scrut; exact Hp
                      | eapply fi_pat_pat; exact Hp | eassumption | eassumption
                      | first [eassumption | constructor] | rewrite length_map; assumption] end].
    all: try solve [apply eblock_typed'; assumption].
    all: try solve [eapply T_Jump; [eassumption|]; simpl; tc].
    (* errors *)
    all: try solve [apply raise_typed; assumption].
    all: try solve [apply raise_typed; eapply coerce_typed; [eassumption|]; apply fail_typed; assumption].
    all: try solve [eapply T_Try; [eassumption|constructor|constructor; reflexivity]].
    all: try solve [eapply try_typed; [eassumption|eassumption|first [constructor; reflexivity
                                                                     | apply noraise_typed; assumption]]].
    all: try solve [eapply T_Defer; eassumption].
    (* traits and methods *)
    all: try solve [eapply call_typed; eassumption].
    all: try solve [eapply meth_call_typed; eassumption].
    all: try solve [eapply tcall_typed; eassumption].
    all: try solve [eapply tcall_typed; [eassumption|eassumption|constructor; assumption|assumption]].
    all: try solve [match goal with Ho : obj_of _ ?t = Some _, Hr : _ ⊢[_;_;_] _ : ?t |- _ =>
                      rewrite (obj_of_ty _ _ Ho) in Hr end;
                    eapply wrap_call_typed; [eapply field_proj_typed; eassumption|eassumption|eassumption]].
    (* conversions and calls *)
    all: try solve [eapply coerce_typed; eauto].
    all: eapply wrap_call_typed; eauto.
  Qed.
End Typed.
