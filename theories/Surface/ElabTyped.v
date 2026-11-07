(** * Surface: elaboration produces well-typed Core

    [elab_typed]: whatever the rules of [ElabSpec.v] relate a surface
    expression to is well typed in Core, at the synthesized or expected
    type, in the Core view of the environments ([ctx_of Γ], [cc_of L]).
    Source programs mention no store locations: [Σ = []]. *)

From Stdlib Require Import List ZArith String Bool Arith Lia.
From MoonRocq.Prelude Require Import Result EqDec Ident.
From MoonRocq.Core Require Import Syntax Prim Subst Typing.
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

  Theorem elab_typed :
    (forall L Γ s τ e, Γ ⊩[E;L] s ⇒ τ ⇝ e -> ctx_of Γ ⊢[ge;[];cc_of L] e : τ) /\
    (forall L Γ s τ e, Γ ⊩[E;L] s ⇐ τ ⇝ e -> ctx_of Γ ⊢[ge;[];cc_of L] e : τ) /\
    (forall L Γ s a τ e, Γ ⊩[E;L] s ⦂ a ⇒ τ ⇝ e -> ctx_of Γ ⊢[ge;[];cc_of L] e : τ) /\
    (forall L Γ ss τs es, Γ ⊩*[E;L] ss ⇒ τs ⇝ es -> ctx_of Γ ⊢*[ge;[];cc_of L] es : τs) /\
    (forall L Γ ss τs es, Γ ⊩*[E;L] ss ⇐ τs ⇝ es -> ctx_of Γ ⊢*[ge;[];cc_of L] es : τs).
  Proof.
    apply elab_mutind; intros; simpl in *.
    all: repeat match goal with
                | H : params_syn _ _ _ |- _ => pose proof (params_len _ _ _ H); clear H
                | H : params_ann _ _ _ |- _ => pose proof (params_len _ _ _ H); clear H
                | H : context [ctx_of (List.app (lam_ctx ?ps ?τs) ?Γ)] |- _ =>
                    rewrite lam_ctx_ctx in H by assumption
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
    (* conversions and calls *)
    all: try solve [eapply coerce_typed; eauto].
    all: eapply wrap_call_typed; eauto; eapply T_Global; eauto.
  Qed.
End Typed.
