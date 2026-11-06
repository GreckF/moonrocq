(** * Type soundness of the Core IR

    Typing is lifted from expressions to frames, stacks and machine states.
    A frame has type [τ ⇒ τ'] when filling its hole with a value of type
    [τ] produces something of type [τ']; a stack composes frames down to
    the final type of the program.

    Main results:
    - [progress]     : a well-typed state is final or can step;
    - [preservation] : stepping preserves the type of the state;
    - [soundness]    : a well-typed program never reaches a stuck state, and
                       if it terminates normally its value has the program's type. *)

From Stdlib Require Import List.
From MoonRocq.Core Require Import Syntax Prim Subst Typing TypingLemmas Semantics.
Import ListNotations.

Section Soundness.
  Variable ge : genv.

  Inductive frame_typed : frame -> ty -> ty -> Prop :=
  | FT_AppFun args ps r :
      has_types ge [] args ps ->
      frame_typed (FAppFun args) (TArrow ps r) r
  | FT_AppArg f done rest psd τ psr r :
      value f ->
      has_type ge [] f (TArrow (psd ++ τ :: psr) r) ->
      Forall value done ->
      has_types ge [] done psd ->
      has_types ge [] rest psr ->
      frame_typed (FAppArg f done rest) τ r
  | FT_Let e2 τ1 τ2 :
      has_type ge [τ1] e2 τ2 ->
      frame_typed (FLet e2) τ1 τ2
  | FT_If t e τ :
      has_type ge [] t τ ->
      has_type ge [] e τ ->
      frame_typed (FIf t e) TBool τ
  | FT_Tuple done rest τsd τ τsr :
      Forall value done ->
      has_types ge [] done τsd ->
      has_types ge [] rest τsr ->
      frame_typed (FTuple done rest) τ (TTuple (τsd ++ τ :: τsr))
  | FT_Proj i τs τ :
      nth_error τs i = Some τ ->
      frame_typed (FProj i) (TTuple τs) τ
  | FT_Prim op done rest τsd τ τsr :
      fst (prim_sig op) = τsd ++ τ :: τsr ->
      Forall value done ->
      has_types ge [] done τsd ->
      has_types ge [] rest τsr ->
      frame_typed (FPrim op done rest) τ (snd (prim_sig op)).

  Inductive stack_typed : stack -> ty -> ty -> Prop :=
  | ST_nil τ : stack_typed [] τ τ
  | ST_cons F K τ1 τ2 τf :
      frame_typed F τ1 τ2 ->
      stack_typed K τ2 τf ->
      stack_typed (F :: K) τ1 τf.

  Inductive state_typed : state -> ty -> Prop :=
  | SS_Eval K e τ τf :
      has_type ge [] e τ ->
      stack_typed K τ τf ->
      state_typed (SEval K e) τf
  | SS_Ret K v τ τf :
      value v ->
      has_type ge [] v τ ->
      stack_typed K τ τf ->
      state_typed (SRet K v) τf
  | SS_Abort τf :
      state_typed SAbort τf.

  (** ** Canonical forms *)

  Lemma canonical_arrow v ps r :
    value v -> has_type ge [] v (TArrow ps r) ->
    exists b, v = ELam ps r b /\ has_type ge (ps ++ []) b r.
  Proof. intros Hv Ht; inversion Hv; subst; inversion Ht; subst; eauto. Qed.

  Lemma canonical_base v b :
    value v -> has_type ge [] v (TBase b) -> exists l, v = ELit l /\ lit_ty l = b.
  Proof. intros Hv Ht; inversion Hv; subst; inversion Ht; subst; eauto. Qed.

  Lemma canonical_bool v :
    value v -> has_type ge [] v TBool -> exists b, v = ELit (LBool b).
  Proof.
    intros Hv Ht. destruct (canonical_base _ _ Hv Ht) as (l & -> & Hl).
    destruct l; inversion Hl; eauto.
  Qed.

  Lemma canonical_tuple v τs :
    value v -> has_type ge [] v (TTuple τs) ->
    exists vs, v = ETuple vs /\ Forall value vs /\ has_types ge [] vs τs.
  Proof.
    intros Hv Ht; inversion Hv; subst; inversion Ht; subst; eauto.
  Qed.

  (** Values of primitive types are literals, so primitive operators can
      always read their arguments. *)
  Lemma as_lits_complete vs τs :
    Forall value vs -> has_types ge [] vs τs ->
    Forall (fun t => exists b, t = TBase b) τs ->
    exists ls, as_lits vs = Some ls /\ lits_typed ls τs.
  Proof.
    intros Hv Ht; remember (@nil ty) as Γ eqn:EΓ.
    induction Ht as [|Γ e es τ τs He Hs IH]; intros Hb; subst.
    - exists []; split; [reflexivity | constructor].
    - inversion Hv as [|? ? Hve Hvs]; subst.
      inversion Hb as [|? ? [b ->] Hbs]; subst.
      destruct (canonical_base _ _ Hve He) as (l & -> & Hl).
      destruct (IH Hvs eq_refl Hbs) as (ls & Els & Hls).
      exists (l :: ls); simpl; rewrite Els; split; [reflexivity|].
      constructor; [congruence | exact Hls].
  Qed.

  Lemma as_lits_typed vs τs ls :
    as_lits vs = Some ls -> has_types ge [] vs τs -> lits_typed ls τs.
  Proof.
    intros E Ht; revert ls E; induction Ht as [|Γ e es τ τs He Hs IH]; intros ls E.
    - inversion E; constructor.
    - simpl in E. destruct e; try discriminate.
      destruct (as_lits es) eqn:Ees; try discriminate. inversion E; subst.
      inversion He; subst. constructor; [reflexivity | exact (IH _ eq_refl)].
  Qed.

  (** ** Inversion helpers *)

  Lemma stack_cons_inv F K τ τf :
    stack_typed (F :: K) τ τf -> exists τ2, frame_typed F τ τ2 /\ stack_typed K τ2 τf.
  Proof. intros H; inversion H; subst; eauto. Qed.

  Lemma eval_inv K e τf :
    state_typed (SEval K e) τf -> exists τ, has_type ge [] e τ /\ stack_typed K τ τf.
  Proof. intros H; inversion H; subst; eauto. Qed.

  Lemma ret_inv K v τf :
    state_typed (SRet K v) τf ->
    exists τ, value v /\ has_type ge [] v τ /\ stack_typed K τ τf.
  Proof. intros H; inversion H; subst; eauto. Qed.

  Lemma Forall_snoc {A} (P : A -> Prop) xs x :
    Forall P xs -> P x -> Forall P (xs ++ [x]).
  Proof. intros; apply Forall_app; auto. Qed.

  Lemma has_types_snoc Γ es e τs τ :
    has_types ge Γ es τs -> has_type ge Γ e τ -> has_types ge Γ (es ++ [e]) (τs ++ [τ]).
  Proof. intros; apply has_types_app; auto using has_types. Qed.

  Lemma nil_lits_typed ts : has_types ge [] [] ts -> lits_typed [] ts.
  Proof. intros H; inversion H; subst; constructor. Qed.

  (** ** Progress *)

  Theorem progress s τf :
    genv_ok ge -> state_typed s τf -> final s \/ exists s', step ge s s'.
  Proof.
    intros Hok Hs. destruct Hs as [K e τ τf He HK | K v τ τf Hv Hvt HK | τf].
    - (* SEval *)
      right. remember (@nil ty) as Γ0 eqn:EΓ. destruct He; subst.
      + destruct x; discriminate.
      + eexists; eapply S_Global; eauto.
      + eexists; apply S_Lit.
      + eexists; apply S_Lam.
      + eexists; apply S_App.
      + eexists; apply S_Let.
      + eexists; apply S_If.
      + destruct es; eexists; [apply S_TupleNil | apply S_TupleCons].
      + eexists; apply S_Proj.
      + destruct args as [|a args].
        * assert (Hl := nil_lits_typed _ H).
          destruct (prim_eval_progress _ _ Hl) as [Ea | (l & El & _)].
          -- eexists; eapply S_PrimNilAbort; exact Ea.
          -- eexists; eapply S_PrimNil; exact El.
        * eexists; apply S_PrimCons.
    - (* SRet *)
      destruct K as [|F K]; [left; exact Hv | right].
      apply stack_cons_inv in HK as (τ2 & HF & HK).
      destruct HF.
      + destruct args.
        * destruct (canonical_arrow _ _ _ Hv Hvt) as (b & -> & _).
          eexists; apply S_AppFunNil.
        * eexists; apply S_AppFunCons.
      + destruct rest.
        * destruct (canonical_arrow _ _ _ H H0) as (b & -> & _).
          eexists; apply S_AppArgLast.
        * eexists; apply S_AppArgNext.
      + eexists; apply S_LetRet.
      + destruct (canonical_bool _ Hv Hvt) as ([] & ->); eexists;
          [apply S_IfTrue | apply S_IfFalse].
      + destruct rest; eexists; [apply S_TupleLast | apply S_TupleNext].
      + destruct (canonical_tuple _ _ Hv Hvt) as (vs & -> & _ & Hvs).
        destruct (has_types_nth_error _ _ _ _ _ _ Hvs H) as (w & Ew & _).
        eexists; apply S_ProjRet; eauto.
      + destruct rest as [|e rest].
        * inversion H2; subst.
          assert (Hb := prim_sig_args_base op). rewrite H in Hb.
          destruct (as_lits_complete (done ++ [v]) (τsd ++ [τ]))
            as (ls & Els & Hls).
          -- now apply Forall_snoc.
          -- now apply has_types_snoc.
          -- exact Hb.
          -- rewrite <- H in Hls.
             destruct (prim_eval_progress _ _ Hls) as [Ea | (l & El & _)].
             ++ eexists; eapply S_PrimLastAbort; eauto.
             ++ eexists; eapply S_PrimLast; eauto.
        * eexists; apply S_PrimNext.
    - left; exact I.
  Qed.

  (** ** Preservation *)

  Lemma has_types_cons_inv Γ e es ts :
    has_types ge Γ (e :: es) ts ->
    exists τ τs, ts = τ :: τs /\ has_type ge Γ e τ /\ has_types ge Γ es τs.
  Proof. intros H; inversion H; subst; eauto. Qed.

  Lemma has_type_prim_inv Γ op args τ :
    has_type ge Γ (EPrim op args) τ ->
    τ = snd (prim_sig op) /\ has_types ge Γ args (fst (prim_sig op)).
  Proof. intros H; inversion H; subst; auto. Qed.

  (* Unify two hypotheses [a = Some x], [a = Some y]. *)
  Local Ltac some_eq :=
    repeat match goal with
    | H1 : ?a = Some _, H2 : ?a = Some _ |- _ =>
        rewrite H1 in H2; inversion H2; subst; clear H2
    | H1 : ?a = PVal _, H2 : ?a = PVal _ |- _ =>
        rewrite H1 in H2; inversion H2; subst; clear H2
    end.

  (* Decompose [has_types] on syntactically empty / non-empty lists. *)
  Local Ltac inv_types :=
    repeat match goal with
    | H : has_types _ _ [] _ |- _ => inversion H; subst; clear H
    | H : has_types _ _ (_ :: _) _ |- _ => inversion H; subst; clear H
    end.

  (* Open a return state: value, its type, and the top frame's typing. *)
  Local Ltac open_ret Hs :=
    let τ := fresh "τv" in let Hv := fresh "Hv" in let Hvt := fresh "Hvt" in
    let HK := fresh "HK" in let τ2 := fresh "τk" in let HF := fresh "HF" in
    apply ret_inv in Hs as (τ & Hv & Hvt & HK);
    apply stack_cons_inv in HK as (τ2 & HF & HK);
    inversion HF; subst; clear HF.

  Theorem preservation s s' τf :
    genv_ok ge -> state_typed s τf -> step ge s s' -> state_typed s' τf.
  Proof.
    intros Hok Hs Hstep. destruct Hstep.
    (* ---- evaluation steps ---- *)
    - (* S_Lit *)
      apply eval_inv in Hs as (τ & He & HK). econstructor; eauto using value.
    - (* S_Lam *)
      apply eval_inv in Hs as (τ & He & HK). econstructor; eauto using value.
    - (* S_Global *)
      apply eval_inv in Hs as (τ & He & HK). inversion He; subst. some_eq.
      eapply SS_Ret; [apply V_Lam | eapply global_inst_typing; eauto | exact HK].
    - (* S_App *)
      apply eval_inv in Hs as (τ & He & HK). inversion He; subst.
      eapply SS_Eval; [eassumption|]. eapply ST_cons; [|exact HK].
      constructor; assumption.
    - (* S_Let *)
      apply eval_inv in Hs as (τ & He & HK). inversion He; subst.
      eapply SS_Eval; [eassumption|]. eapply ST_cons; [|exact HK].
      constructor; assumption.
    - (* S_If *)
      apply eval_inv in Hs as (τ & He & HK). inversion He; subst.
      eapply SS_Eval; [eassumption|]. eapply ST_cons; [|exact HK].
      constructor; assumption.
    - (* S_TupleNil *)
      apply eval_inv in Hs as (τ & He & HK). inversion He; subst. inv_types.
      eapply SS_Ret; [repeat constructor | repeat constructor | exact HK].
    - (* S_TupleCons *)
      apply eval_inv in Hs as (τ & He & HK). inversion He; subst. inv_types.
      eapply SS_Eval; [eassumption|]. eapply ST_cons; [|exact HK].
      apply (FT_Tuple [] es []); auto using has_types.
    - (* S_Proj *)
      apply eval_inv in Hs as (τ & He & HK). inversion He; subst.
      eapply SS_Eval; [eassumption|]. eapply ST_cons; [|exact HK].
      constructor; assumption.
    - (* S_PrimNil *)
      apply eval_inv in Hs as (τ & He & HK).
      apply has_type_prim_inv in He as [-> Hargs].
      destruct (prim_eval_progress _ _ (nil_lits_typed _ Hargs))
        as [Ea | (l' & El & Ht)]; [congruence|].
      some_eq.
      eapply SS_Ret; [constructor | | exact HK]. rewrite <- Ht. constructor.
    - (* S_PrimNilAbort *)
      constructor.
    - (* S_PrimCons *)
      apply eval_inv in Hs as (τ & He & HK).
      apply has_type_prim_inv in He as [-> Hargs].
      apply has_types_cons_inv in Hargs as (τ0 & τs & Ets & He0 & Hes).
      eapply SS_Eval; [exact He0|]. eapply ST_cons; [|exact HK].
      apply (FT_Prim op [] es [] τ0 τs); auto using has_types.
    (* ---- return steps ---- *)
    - (* S_AppFunNil *)
      open_ret Hs. inv_types. inversion Hvt; subst.
      eapply SS_Eval; [|exact HK].
      eapply subst_args_typing; [eassumption | constructor].
    - (* S_AppFunCons *)
      open_ret Hs. inv_types.
      eapply SS_Eval; [eassumption|]. eapply ST_cons; [|exact HK].
      eapply (FT_AppArg f [] args []); eauto using has_types, Forall.
    - (* S_AppArgLast *)
      open_ret Hs. inv_types.
      match goal with Hf : has_type _ _ (ELam _ _ _) _ |- _ => inversion Hf; subst end.
      eapply SS_Eval; [|exact HK].
      eapply subst_args_typing; [eassumption|].
      apply has_types_snoc; eassumption.
    - (* S_AppArgNext *)
      open_ret Hs. inv_types.
      eapply SS_Eval; [eassumption|]. eapply ST_cons; [|exact HK].
      match goal with
      | Hf : has_type _ _ f (TArrow (?psd ++ ?t :: ?ta :: ?psr) _) |- _ =>
          apply (FT_AppArg f (done ++ [v]) rest (psd ++ [t]) ta psr);
          [ assumption
          | rewrite <- app_assoc; exact Hf
          | apply Forall_snoc; assumption
          | apply has_types_snoc; assumption
          | assumption ]
      end.
    - (* S_LetRet *)
      open_ret Hs.
      eapply SS_Eval; [|exact HK].
      eapply (subst_args_typing ge [_]); [eassumption | eauto using has_types].
    - (* S_IfTrue *)
      open_ret Hs. eapply SS_Eval; [eassumption | exact HK].
    - (* S_IfFalse *)
      open_ret Hs. eapply SS_Eval; [eassumption | exact HK].
    - (* S_TupleLast *)
      open_ret Hs. inv_types.
      eapply SS_Ret; [ | | exact HK].
      + constructor; apply Forall_snoc; assumption.
      + constructor; apply has_types_snoc; assumption.
    - (* S_TupleNext *)
      open_ret Hs. inv_types.
      eapply SS_Eval; [eassumption|]. eapply ST_cons; [|exact HK].
      match goal with
      | |- frame_typed _ _ (TTuple (?a ++ ?t :: ?rest)) =>
          replace (a ++ t :: rest) with ((a ++ [t]) ++ rest) by (now rewrite <- app_assoc)
      end.
      constructor; [apply Forall_snoc | apply has_types_snoc | ]; assumption.
    - (* S_ProjRet *)
      open_ret Hs.
      inversion Hv as [| | ? Hvs]; subst. inversion Hvt; subst.
      match goal with
      | Hts : has_types _ _ vs ?ts, Hn : nth_error ?ts i = Some _ |- _ =>
          destruct (has_types_nth_error _ _ _ _ _ _ Hts Hn) as (w & Ew & Hw)
      end.
      some_eq.
      eapply SS_Ret; [ | eassumption | exact HK ].
      rewrite Forall_forall in Hvs. eapply Hvs, nth_error_In; eassumption.
    - (* S_PrimLast *)
      open_ret Hs. inv_types.
      assert (Hls : lits_typed ls (fst (prim_sig op))).
      { match goal with E : fst (prim_sig op) = _ |- _ => rewrite E end.
        eapply as_lits_typed; [eassumption|]. apply has_types_snoc; eassumption. }
      destruct (prim_eval_progress _ _ Hls) as [Ea | (l' & El & Ht)]; [congruence|].
      some_eq.
      eapply SS_Ret; [constructor | | exact HK]. rewrite <- Ht. constructor.
    - (* S_PrimLastAbort *)
      constructor.
    - (* S_PrimNext *)
      open_ret Hs. inv_types.
      eapply SS_Eval; [eassumption|]. eapply ST_cons; [|exact HK].
      match goal with
      | E : fst (prim_sig op) = ?a ++ ?t :: ?te :: ?r |- _ =>
          apply (FT_Prim op (done ++ [v]) rest (a ++ [t]) te r);
          [ rewrite E, <- app_assoc; reflexivity
          | apply Forall_snoc; assumption
          | apply has_types_snoc; assumption
          | assumption ]
      end.
  Qed.

  (** ** Soundness *)

  Lemma star_preservation s s' τf :
    genv_ok ge -> state_typed s τf -> star ge s s' -> state_typed s' τf.
  Proof. intros Hok Hs H; induction H; eauto using preservation. Qed.

  Lemma initial_typed e τ :
    has_type ge [] e τ -> state_typed (SEval [] e) τ.
  Proof. intros; econstructor; eauto; constructor. Qed.

  (** A well-typed program never gets stuck. *)
  Theorem soundness e τ s :
    genv_ok ge -> has_type ge [] e τ -> star ge (SEval [] e) s -> ~ stuck ge s.
  Proof.
    intros Hok He Hstar [Hnf Hns].
    destruct (progress s τ Hok (star_preservation _ _ _ Hok (initial_typed _ _ He) Hstar))
      as [Hf | Hstep]; contradiction.
  Qed.

  (** If a well-typed program terminates normally, the result is a value of
      the program's type. *)
  Theorem soundness_value e τ v :
    genv_ok ge -> has_type ge [] e τ -> star ge (SEval [] e) (SRet [] v) ->
    value v /\ has_type ge [] v τ.
  Proof.
    intros Hok He Hstar.
    apply (star_preservation _ _ _ Hok (initial_typed _ _ He)) in Hstar.
    apply ret_inv in Hstar as (τ' & Hv & Hvt & HK).
    inversion HK; subst; auto.
  Qed.
End Soundness.
