(** * Type soundness of the Core IR

    Typing is lifted from expressions to frames, stacks, stores and
    machine states.  A frame has type [τ ⇒ τ'] when filling its hole with a
    value of type [τ] produces something of type [τ']; a stack composes
    frames down to the final type of the program.

    Two invariants are new in milestone M3:
    - the store [σ] is typed by a store typing [Σ] (one entry per location),
      which only grows ([Σ ++ Σ']);
    - the expressions inside a frame are typed with the label context
      [labels K] of the stack [K] below it, so that every [break]/[continue]
      finds its loop.  Values do not depend on labels; they are typed with
      the empty label context.

    Main results:
    - [progress]     : a well-typed state is final or can step;
    - [preservation] : stepping preserves the type of the state;
    - [soundness]    : a well-typed program never reaches a stuck state, and
                       if it terminates normally its value has the program's type. *)

From Stdlib Require Import List ZArith Lia.
From MoonRocq.Prelude Require Import EqDec Ident.
From MoonRocq.Core Require Import Syntax Prim Subst Typing TypingLemmas Semantics.
Import ListNotations.

(** ** Judgment notations

    - [⊢ᶠ[ge;Σ;Λ] F : τ ⇒ τ'] : frame [F] turns a value of type [τ] into a
                                 computation of type [τ'] ([frame_typed]);
                                 [Λ] are the loops below it;
    - [⊢ᵏ[ge;Σ] K : τ ⇒ τ']   : the same for a whole stack ([stack_typed]);
    - [⊢ˢ[ge] s : τ]          : machine state [s] eventually produces a [τ]
                                 ([state_typed]). *)

Reserved Notation "⊢ᶠ[ ge ; Σ ; Λ ] F : τ ⇒ τ'"
  (at level 70, ge at level 200, Σ at level 200, Λ at level 200,
   F at level 60, τ at level 60, τ' at level 60,
   no associativity, format "⊢ᶠ[ ge ; Σ ; Λ ]  F  :  τ  ⇒  τ'").
Reserved Notation "⊢ᵏ[ ge ; Σ ] K : τ ⇒ τ'"
  (at level 70, ge at level 200, Σ at level 200, K at level 60, τ at level 60,
   τ' at level 60, no associativity, format "⊢ᵏ[ ge ; Σ ]  K  :  τ  ⇒  τ'").
Reserved Notation "⊢ˢ[ ge ] s : τ"
  (at level 70, ge at level 200, s at level 60, τ at level 60,
   no associativity, format "⊢ˢ[ ge ]  s  :  τ").

Inductive frame_typed (ge : genv) (Σ : styping) (Λ : lblctx) : frame -> ty -> ty -> Prop :=
| FT_AppFun args ps r :
    [] ⊢*[ge;Σ;Λ] args : ps ->
    ⊢ᶠ[ge;Σ;Λ] FAppFun args : TArrow ps r ⇒ r
| FT_AppArg f done rest psd τ psr r :
    value f ->
    [] ⊢[ge;Σ;[]] f : TArrow (psd ++ τ :: psr) r ->
    Forall value done ->
    [] ⊢*[ge;Σ;[]] done : psd ->
    [] ⊢*[ge;Σ;Λ] rest : psr ->
    ⊢ᶠ[ge;Σ;Λ] FAppArg f done rest : τ ⇒ r
| FT_Let e2 τ1 τ2 :
    [τ1] ⊢[ge;Σ;Λ] e2 : τ2 ->
    ⊢ᶠ[ge;Σ;Λ] FLet e2 : τ1 ⇒ τ2
| FT_If t e τ :
    [] ⊢[ge;Σ;Λ] t : τ ->
    [] ⊢[ge;Σ;Λ] e : τ ->
    ⊢ᶠ[ge;Σ;Λ] FIf t e : TBool ⇒ τ
| FT_Tuple done rest τsd τ τsr :
    Forall value done ->
    [] ⊢*[ge;Σ;[]] done : τsd ->
    [] ⊢*[ge;Σ;Λ] rest : τsr ->
    ⊢ᶠ[ge;Σ;Λ] FTuple done rest : τ ⇒ TTuple (τsd ++ τ :: τsr)
| FT_Proj i τs τ :
    nth_error τs i = Some τ ->
    ⊢ᶠ[ge;Σ;Λ] FProj i : TTuple τs ⇒ τ
| FT_Prim op done rest τsd τ τsr :
    fst (prim_sig op) = τsd ++ τ :: τsr ->
    Forall value done ->
    [] ⊢*[ge;Σ;[]] done : τsd ->
    [] ⊢*[ge;Σ;Λ] rest : τsr ->
    ⊢ᶠ[ge;Σ;Λ] FPrim op done rest : τ ⇒ snd (prim_sig op)
| FT_Constr T c ts td cd :
    lookup_ty ge T = Some td ->
    length ts = td_tparams td ->
    lookup_ctor td c = Some cd ->
    ⊢ᶠ[ge;Σ;Λ] FConstr T c ts : TTuple (map (tsubst (inst ts)) (cd_fields cd)) ⇒ TData T ts
| FT_Match τ bs τs :
    [] ⊢ᵇ[ge;Σ;Λ] bs : τs ⇒ τ ->
    ⊢ᶠ[ge;Σ;Λ] FMatch τ bs : τs ⇒ τ
| FT_Mem op done rest τsd τ τsr :
    fst (mem_sig op) = τsd ++ τ :: τsr ->
    Forall value done ->
    [] ⊢*[ge;Σ;[]] done : τsd ->
    [] ⊢*[ge;Σ;Λ] rest : τsr ->
    ⊢ᶠ[ge;Σ;Λ] FMem op done rest : τ ⇒ snd (mem_sig op)
| FT_LoopInit ps τ b :
    ps ++ [] ⊢[ge;Σ;(ps, τ) :: Λ] b : τ ->
    ⊢ᶠ[ge;Σ;Λ] FLoopInit ps τ b : TTuple ps ⇒ τ
| FT_Loop ps τ b :
    ps ++ [] ⊢[ge;Σ;(ps, τ) :: Λ] b : τ ->
    ⊢ᶠ[ge;Σ;Λ] FLoop ps τ b : τ ⇒ τ
| FT_Jump c k lbl τ' :
    nth_error Λ k = Some lbl ->
    ⊢ᶠ[ge;Σ;Λ] FJump c k : ctl_ty c lbl ⇒ τ'

where "⊢ᶠ[ ge ; Σ ; Λ ] F : τ ⇒ τ'" := (frame_typed ge Σ Λ F τ τ').

Inductive stack_typed (ge : genv) (Σ : styping) : stack -> ty -> ty -> Prop :=
| ST_nil τ :
    ⊢ᵏ[ge;Σ] [] : τ ⇒ τ
| ST_cons F K τ1 τ2 τf :
    ⊢ᶠ[ge;Σ;labels K] F : τ1 ⇒ τ2 ->
    ⊢ᵏ[ge;Σ] K : τ2 ⇒ τf ->
    ⊢ᵏ[ge;Σ] F :: K : τ1 ⇒ τf

where "⊢ᵏ[ ge ; Σ ] K : τ ⇒ τ'" := (stack_typed ge Σ K τ τ').

(** A store object of a store typing entry. *)
Definition sobj_typed (ge : genv) (Σ : styping) (o : sobj) (s : lty) : Prop :=
  match o, s with
  | OCell v, LCell τ => value v /\ [] ⊢[ge;Σ;[]] v : τ
  | OArr vs, LArr _ τ => Forall (fun v => value v /\ [] ⊢[ge;Σ;[]] v : τ) vs
  | _, _ => False
  end.

Definition store_typed (ge : genv) (Σ : styping) (σ : store) : Prop :=
  Forall2 (sobj_typed ge Σ) σ Σ.

Inductive state_typed (ge : genv) : state -> ty -> Prop :=
| SS_Eval Σ σ K e τ τf :
    store_typed ge Σ σ ->
    [] ⊢[ge;Σ;labels K] e : τ ->
    ⊢ᵏ[ge;Σ] K : τ ⇒ τf ->
    ⊢ˢ[ge] ⟨σ ∣ K ▷ e⟩ : τf
| SS_Ret Σ σ K v τ τf :
    store_typed ge Σ σ ->
    value v ->
    [] ⊢[ge;Σ;[]] v : τ ->
    ⊢ᵏ[ge;Σ] K : τ ⇒ τf ->
    ⊢ˢ[ge] ⟨σ ∣ K ◁ v⟩ : τf
| SS_Jump Σ σ K c k v lbl τ τf :
    store_typed ge Σ σ ->
    value v ->
    nth_error (labels K) k = Some lbl ->
    [] ⊢[ge;Σ;[]] v : ctl_ty c lbl ->
    ⊢ᵏ[ge;Σ] K : τ ⇒ τf ->
    ⊢ˢ[ge] ⟨σ ∣ K ⇑ c k v⟩ : τf
| SS_Abort τf :
    ⊢ˢ[ge] SAbort : τf

where "⊢ˢ[ ge ] s : τ" := (state_typed ge s τ).

(** ** Generic list facts *)

Lemma Forall2_nth_error_r {A B} (R : A -> B -> Prop) xs ys n y :
  Forall2 R xs ys -> nth_error ys n = Some y ->
  exists x, nth_error xs n = Some x /\ R x y.
Proof.
  intros H; revert n; induction H as [|x y' xs ys Hxy _ IH]; intros [|n] E;
    simpl in *; try discriminate.
  - inversion E; subst; eauto.
  - eauto.
Qed.

Lemma Forall2_set_nth {A B} (R : A -> B -> Prop) xs ys n x y :
  Forall2 R xs ys -> nth_error ys n = Some y -> R x y ->
  Forall2 R (set_nth n x xs) ys.
Proof.
  intros H; revert n; induction H as [|x' y' xs ys Hxy Hr' IH]; intros [|n] E Hr;
    simpl in *; try discriminate.
  - inversion E; subst; constructor; auto.
  - constructor; auto.
Qed.

Lemma Forall_set_nth {A} (P : A -> Prop) l n x :
  Forall P l -> P x -> Forall P (set_nth n x l).
Proof.
  intros H; revert n; induction H; intros [|n] Hx; simpl; constructor; auto.
Qed.

Lemma Forall_repeat' {A} (P : A -> Prop) x n : P x -> Forall P (repeat x n).
Proof. intros Hx; induction n; simpl; constructor; auto. Qed.

Lemma Forall_snoc {A} (P : A -> Prop) xs x :
  Forall P xs -> P x -> Forall P (xs ++ [x]).
Proof. intros; apply Forall_app; auto. Qed.

Lemma index_of_lt z n j : index_of z n = Some j -> j < n.
Proof.
  unfold index_of. destruct ((0 <=? z)%Z && (z <? Z.of_nat n)%Z)%bool eqn:E;
    [|discriminate].
  intros H; inversion H; subst.
  apply Bool.andb_true_iff in E as [E1 E2].
  apply Z.leb_le in E1. apply Z.ltb_lt in E2. lia.
Qed.

Lemma labels_nonloop F K : is_loop F = false -> labels (F :: K) = labels K.
Proof. destruct F; simpl; congruence. Qed.

Section Soundness.
  Variable ge : genv.

  (** ** Values do not depend on the label context *)

  Lemma value_labels_mut Σ :
    (forall Λ Γ e τ, Γ ⊢[ge;Σ;Λ] e : τ -> value e -> forall Λ', Γ ⊢[ge;Σ;Λ'] e : τ) /\
    (forall Λ Γ es τs, Γ ⊢*[ge;Σ;Λ] es : τs ->
       Forall value es -> forall Λ', Γ ⊢*[ge;Σ;Λ'] es : τs) /\
    (forall Λ Γ bs τs τ, Γ ⊢ᵇ[ge;Σ;Λ] bs : τs ⇒ τ -> True).
  Proof.
    apply has_type_mutind; intros;
      try match goal with Hv : value _ |- _ => inversion Hv; subst end;
      try match goal with Hv : Forall value (_ :: _) |- _ => inversion Hv; subst end;
      econstructor; eauto.
  Qed.

  Lemma value_any_labels Σ Λ Λ' Γ v τ :
    value v -> Γ ⊢[ge;Σ;Λ] v : τ -> Γ ⊢[ge;Σ;Λ'] v : τ.
  Proof. intros Hv Ht; exact (proj1 (value_labels_mut Σ) _ _ _ _ Ht Hv Λ'). Qed.

  Lemma values_any_labels Σ Λ Λ' Γ vs τs :
    Forall value vs -> Γ ⊢*[ge;Σ;Λ] vs : τs -> Γ ⊢*[ge;Σ;Λ'] vs : τs.
  Proof. intros Hv Ht; exact (proj1 (proj2 (value_labels_mut Σ)) _ _ _ _ Ht Hv Λ'). Qed.

  Lemma weaken_labels Σ Λ Γ e τ : Γ ⊢[ge;Σ;[]] e : τ -> Γ ⊢[ge;Σ;Λ] e : τ.
  Proof.
    intros H. rewrite <- (app_nil_r Σ).
    exact (proj1 (weaken_typing ge Σ) _ _ _ _ H [] Λ).
  Qed.

  (** ** Weakening of the store typing for frames, stacks and stores *)

  Lemma frame_weaken Σ Σ' Λ F τ τ' :
    ⊢ᶠ[ge;Σ;Λ] F : τ ⇒ τ' -> ⊢ᶠ[ge;Σ ++ Σ';Λ] F : τ ⇒ τ'.
  Proof.
    intros H; destruct H; econstructor;
      eauto using weaken_store, weaken_store_types, weaken_store_branches.
  Qed.

  Lemma stack_weaken Σ Σ' K τ τf :
    ⊢ᵏ[ge;Σ] K : τ ⇒ τf -> ⊢ᵏ[ge;Σ ++ Σ'] K : τ ⇒ τf.
  Proof. induction 1; econstructor; eauto using frame_weaken. Qed.

  Lemma sobj_weaken Σ Σ' o s : sobj_typed ge Σ o s -> sobj_typed ge (Σ ++ Σ') o s.
  Proof.
    destruct o, s; simpl; try (intros []; fail).
    - intros [Hv Ht]; split; [exact Hv | apply weaken_store; exact Ht].
    - intros H; eapply Forall_impl; [|exact H].
      intros v [Hv Ht]; split; [exact Hv | apply weaken_store; exact Ht].
  Qed.

  Lemma store_lookup Σ σ l s :
    store_typed ge Σ σ -> nth_error Σ l = Some s ->
    exists o, nth_error σ l = Some o /\ sobj_typed ge Σ o s.
  Proof. apply Forall2_nth_error_r. Qed.

  Lemma store_set Σ σ l s o :
    store_typed ge Σ σ -> nth_error Σ l = Some s -> sobj_typed ge Σ o s ->
    store_typed ge Σ (set_nth l o σ).
  Proof. apply Forall2_set_nth. Qed.

  Lemma store_alloc Σ σ o s :
    store_typed ge Σ σ -> sobj_typed ge (Σ ++ [s]) o s ->
    store_typed ge (Σ ++ [s]) (σ ++ [o]) /\
    [] ⊢[ge;Σ ++ [s];[]] ELoc (length σ) : lty_ty s.
  Proof.
    intros Hσ Ho. split.
    - apply Forall2_app; [|constructor; auto].
      eapply Forall2_impl; [|exact Hσ]. intros; apply sobj_weaken; assumption.
    - constructor. rewrite (Forall2_length Hσ), nth_error_app2, Nat.sub_diag by lia.
      reflexivity.
  Qed.

  (** ** Canonical forms *)

  Local Ltac canon Hv Ht :=
    inversion Hv; subst; inversion Ht; subst;
    try match goal with H : lty_ty ?s = _ |- _ => destruct s; simpl in H; inversion H; subst end;
    eauto 10.

  Lemma canonical_arrow Σ Λ v ps r :
    value v -> [] ⊢[ge;Σ;Λ] v : TArrow ps r ->
    exists b, v = ELam ps r b /\ ps ++ [] ⊢[ge;Σ;[]] b : r.
  Proof. intros Hv Ht; canon Hv Ht. Qed.

  Lemma canonical_base Σ Λ v b :
    value v -> [] ⊢[ge;Σ;Λ] v : TBase b -> exists l, v = ELit l /\ lit_ty l = b.
  Proof. intros Hv Ht; canon Hv Ht. Qed.

  Lemma canonical_bool Σ Λ v :
    value v -> [] ⊢[ge;Σ;Λ] v : TBool -> exists b, v = ELit (LBool b).
  Proof.
    intros Hv Ht. destruct (canonical_base _ _ _ _ Hv Ht) as (l & -> & Hl).
    destruct l; inversion Hl; eauto.
  Qed.

  Lemma canonical_int Σ Λ v k :
    value v -> [] ⊢[ge;Σ;Λ] v : TInt k -> exists z, v = ELit (LInt k z).
  Proof.
    intros Hv Ht. destruct (canonical_base _ _ _ _ Hv Ht) as (l & -> & Hl).
    destruct l; inversion Hl; eauto.
  Qed.

  Lemma canonical_tuple Σ Λ v τs :
    value v -> [] ⊢[ge;Σ;Λ] v : TTuple τs ->
    exists vs, v = ETuple vs /\ Forall value vs /\ [] ⊢*[ge;Σ;Λ] vs : τs.
  Proof. intros Hv Ht; canon Hv Ht. Qed.

  Lemma canonical_data Σ Λ v T ts :
    value v -> [] ⊢[ge;Σ;Λ] v : TData T ts ->
    exists c w td cd, v = EConstr T c ts w /\ value w /\
      lookup_ty ge T = Some td /\ lookup_ctor td c = Some cd /\
      [] ⊢[ge;Σ;Λ] w : TTuple (map (tsubst (inst ts)) (cd_fields cd)).
  Proof. intros Hv Ht; canon Hv Ht. Qed.

  Lemma canonical_ref Σ Λ v τ :
    value v -> [] ⊢[ge;Σ;Λ] v : TRef τ ->
    exists l, v = ELoc l /\ nth_error Σ l = Some (LCell τ).
  Proof. intros Hv Ht; canon Hv Ht. Qed.

  Lemma canonical_array Σ Λ v k τ :
    value v -> [] ⊢[ge;Σ;Λ] v : TArray k τ ->
    exists l, v = ELoc l /\ nth_error Σ l = Some (LArr k τ).
  Proof. intros Hv Ht; canon Hv Ht. Qed.

  Lemma cell_lookup Σ σ v τ :
    store_typed ge Σ σ -> value v -> [] ⊢[ge;Σ;[]] v : TRef τ ->
    exists l w, v = ELoc l /\ nth_error Σ l = Some (LCell τ) /\
      nth_error σ l = Some (OCell w) /\ value w /\ [] ⊢[ge;Σ;[]] w : τ.
  Proof.
    intros Hσ Hv Ht. destruct (canonical_ref _ _ _ _ Hv Ht) as (l & -> & Hl).
    destruct (store_lookup _ _ _ _ Hσ Hl) as ([w|ws] & Ho & Hw); [|contradiction].
    destruct Hw. eauto 10.
  Qed.

  Lemma array_lookup Σ σ v k τ :
    store_typed ge Σ σ -> value v -> [] ⊢[ge;Σ;[]] v : TArray k τ ->
    exists l ws, v = ELoc l /\ nth_error Σ l = Some (LArr k τ) /\
      nth_error σ l = Some (OArr ws) /\
      Forall (fun w => value w /\ [] ⊢[ge;Σ;[]] w : τ) ws.
  Proof.
    intros Hσ Hv Ht. destruct (canonical_array _ _ _ _ _ Hv Ht) as (l & -> & Hl).
    destruct (store_lookup _ _ _ _ Hσ Hl) as ([w|ws] & Ho & Hw); [contradiction|].
    eauto 10.
  Qed.

  (** ** Store operations

      On well-typed arguments a store operation is defined, and either
      aborts or returns a value of its result type in an extended store. *)

  Definition mres_ok (Σ : styping) (op : mem_op) (r : mres) : Prop :=
    match r with
    | MAbort => True
    | MOk σ' v => exists Σ', store_typed ge (Σ ++ Σ') σ' /\ value v /\
                   [] ⊢[ge;Σ ++ Σ';[]] v : snd (mem_sig op)
    end.

  Local Ltac inv_types :=
    repeat match goal with
    | H : has_types _ _ _ _ [] _ |- _ => inversion H; subst; clear H
    | H : has_types _ _ _ _ (_ :: _) _ |- _ => inversion H; subst; clear H
    | H : has_types _ _ _ _ _ [] |- _ => inversion H; subst; clear H
    | H : has_types _ _ _ _ _ (_ :: _) |- _ => inversion H; subst; clear H
    | H : Forall _ (_ :: _) |- _ => inversion H; subst; clear H
    end.

  Lemma has_types_repeat Σ Λ Γ vs τ n :
    Γ ⊢*[ge;Σ;Λ] vs : repeat τ n -> Forall (fun v => Γ ⊢[ge;Σ;Λ] v : τ) vs.
  Proof.
    revert vs; induction n; simpl; intros vs H; inversion H; subst; constructor; auto.
  Qed.

  Lemma ok_same Σ op σ v :
    store_typed ge Σ σ -> value v -> [] ⊢[ge;Σ;[]] v : snd (mem_sig op) ->
    mres_ok Σ op (MOk σ v).
  Proof. intros; exists []; rewrite app_nil_r; auto. Qed.

  Lemma ok_alloc Σ op σ o s :
    store_typed ge Σ σ -> sobj_typed ge (Σ ++ [s]) o s -> snd (mem_sig op) = lty_ty s ->
    mres_ok Σ op (alloc σ o).
  Proof.
    intros Hσ Ho E. destruct (store_alloc _ _ _ _ Hσ Ho) as [H1 H2].
    exists [s]; rewrite E; repeat split; auto using value.
  Qed.

  Lemma unit_typed Σ Λ : [] ⊢[ge;Σ;Λ] ELit LUnit : TBase BUnit.
  Proof. exact (T_Lit ge Σ Λ [] LUnit). Qed.

  (* Look up the cell / array a well-typed location argument points to. *)
  Local Ltac get_cell Hσ :=
    match goal with Hv : value ?v, Ht : has_type _ _ _ _ ?v (TRef _) |- _ =>
      destruct (cell_lookup _ _ _ _ Hσ Hv Ht) as (?l & ?w & -> & ?HΣ & ?Hl & ?Hw & ?Hwt)
    end.
  Local Ltac get_array Hσ :=
    match goal with Hv : value ?v, Ht : has_type _ _ _ _ ?v (TArray _ _) |- _ =>
      destruct (array_lookup _ _ _ _ _ Hσ Hv Ht) as (?l & ?ws & -> & ?HΣ & ?Hl & ?Hws)
    end.
  Local Ltac get_int :=
    match goal with Hv : value ?v, Ht : has_type _ _ _ _ ?v (TBase (BInt _)) |- _ =>
      destruct (canonical_int _ _ _ _ Hv Ht) as (?z & ->)
    end.

  Theorem mem_eval_sound Σ σ op vs :
    store_typed ge Σ σ -> Forall value vs -> [] ⊢*[ge;Σ;[]] vs : fst (mem_sig op) ->
    exists r, mem_eval op σ vs = Some r /\ mres_ok Σ op r.
  Proof.
    intros Hσ Hv Ht. destruct op as [t|t|t|k t n|k t|k t|k t|k t|t]; simpl in Ht.
    - (* MRef *)
      inv_types. eexists; split; [reflexivity|].
      apply ok_alloc with (s := LCell t); [exact Hσ | | reflexivity].
      split; [assumption | apply weaken_store; assumption].
    - (* MGet *)
      inv_types. get_cell Hσ.
      simpl. rewrite Hl. eexists; split; [reflexivity|]. apply ok_same; auto.
    - (* MSet *)
      inv_types. get_cell Hσ.
      simpl. rewrite Hl. eexists; split; [reflexivity|]. apply ok_same.
      + eapply store_set; [exact Hσ | exact HΣ | split; assumption].
      + constructor.
      + apply unit_typed.
    - (* MArray *)
      eexists; split; [reflexivity|].
      apply ok_alloc with (s := LArr k t); [exact Hσ | | reflexivity].
      simpl. apply has_types_repeat in Ht.
      induction Hv as [|v vs Hv1 Hvs IH]; inversion Ht; subst; constructor; auto.
      split; [assumption | apply weaken_store; assumption].
    - (* MMake *)
      inv_types. get_int. simpl.
      destruct (z <? 0)%Z; [eexists; split; [reflexivity | exact I]|].
      eexists; split; [reflexivity|].
      apply ok_alloc with (s := LArr k t); [exact Hσ | | reflexivity].
      simpl. apply Forall_repeat'. split; [assumption | apply weaken_store; assumption].
    - (* MIndex *)
      inv_types. get_array Hσ. get_int.
      simpl. rewrite Hl.
      destruct (index_of z (length ws)) as [j|] eqn:Ej; [|eexists; split; [reflexivity | exact I]].
      apply index_of_lt in Ej. apply nth_error_Some in Ej.
      destruct (nth_error ws j) as [w|] eqn:Ew; [|contradiction].
      eexists; split; [reflexivity|].
      rewrite Forall_forall in Hws. destruct (Hws w (nth_error_In _ _ Ew)).
      apply ok_same; auto.
    - (* MSetIndex *)
      inv_types. get_array Hσ. get_int.
      simpl. rewrite Hl.
      destruct (index_of z (length ws)) as [j|]; [|eexists; split; [reflexivity | exact I]].
      eexists; split; [reflexivity|].
      apply ok_same; [ | constructor | apply unit_typed].
      eapply store_set; [exact Hσ | exact HΣ |].
      simpl. apply Forall_set_nth; auto.
    - (* MLength *)
      inv_types. get_array Hσ.
      simpl. rewrite Hl. eexists; split; [reflexivity|].
      apply ok_same; [exact Hσ | constructor | exact (T_Lit ge Σ [] [] _)].
    - (* MPush *)
      inv_types. get_array Hσ.
      simpl. rewrite Hl. eexists; split; [reflexivity|].
      apply ok_same; [ | constructor | apply unit_typed].
      eapply store_set; [exact Hσ | exact HΣ |].
      simpl. apply Forall_snoc; auto.
  Qed.

  (** ** Pattern matching

      A successful match of a well-typed value binds values of the
      pattern's binding types. *)
  Lemma pmatch_typed Σ σ : store_typed ge Σ σ ->
    (forall p τ Δ, ⊢ᵖ[ge] p : τ ⇝ Δ ->
       forall v xs, value v -> [] ⊢[ge;Σ;[]] v : τ -> pmatch σ p v = Some xs ->
       Forall value xs /\ [] ⊢*[ge;Σ;[]] xs : Δ) /\
    (forall ps τs Δ, ⊢ᵖ*[ge] ps : τs ⇝ Δ ->
       forall vs xs, Forall value vs -> [] ⊢*[ge;Σ;[]] vs : τs ->
       pmatch_list (pmatch σ) ps vs = Some xs -> Forall value xs /\ [] ⊢*[ge;Σ;[]] xs : Δ).
  Proof.
    intros Hσ. apply pat_typed_mutind.
    - (* P_Wild *)
      intros τ v xs _ _ E. simpl in E. inversion E; split; constructor.
    - (* P_Var *)
      intros τ v xs Hv Ht E. simpl in E. inversion E; subst.
      split; [constructor; auto | eauto using has_types].
    - (* P_Lit *)
      intros l v xs _ _ E. destruct v; simpl in E; try discriminate.
      match type of E with context [if ?t then _ else _] => destruct t end;
        inversion E; split; constructor.
    - (* P_Tuple *)
      intros ps τs Δ _ IH v xs Hv Ht E.
      destruct (canonical_tuple _ _ _ _ Hv Ht) as (vs & -> & Hvs & Hts).
      exact (IH _ _ Hvs Hts E).
    - (* P_Constr *)
      intros c ps T ts fs Δ Hf _ IH v xs Hv Ht E.
      destruct (canonical_data _ _ _ _ _ Hv Ht)
        as (c' & w & td & cd & -> & Hw & Htd & Hcd & Hwt).
      destruct (canonical_tuple _ _ _ _ Hw Hwt) as (vs & -> & Hvs & Hts).
      cbn [pmatch] in E. destruct (eqb c c') eqn:Ec; [|discriminate].
      apply (proj1 (eqb_eq c c')) in Ec; subst c'.
      unfold ctor_fields in Hf. rewrite Htd, Hcd in Hf.
      inversion Hf; subst.
      exact (IH _ _ Hvs Hts E).
    - (* P_Ref *)
      intros p τ Δ _ IH v xs Hv Ht E.
      destruct (cell_lookup _ _ _ _ Hσ Hv Ht) as (l & w & -> & _ & Hl & Hw & Hwt).
      cbn [pmatch] in E. rewrite Hl in E.
      exact (IH _ _ Hw Hwt E).
    - (* Ps_nil *)
      intros vs xs _ Ht E. inversion Ht; subst. inversion E; split; constructor.
    - (* Ps_cons *)
      intros p ps τ τs Δ1 Δ2 _ IH1 _ IH2 vs xs Hv Ht E.
      inversion Ht as [|? ? w ws ? ? Hw Hws]; subst.
      inversion Hv as [|? ? Hwv Hwsv]; subst.
      cbn [pmatch_list] in E.
      destruct (pmatch σ p w) as [a|] eqn:Ea; [|discriminate].
      fold (pmatch_list (pmatch σ) ps ws) in E.
      destruct (pmatch_list (pmatch σ) ps ws) as [b|] eqn:Eb; [|discriminate].
      inversion E; subst.
      destruct (IH1 _ _ Hwv Hw Ea), (IH2 _ _ Hwsv Hws Eb).
      split; [apply Forall_app | apply has_types_app]; auto.
  Qed.

  Lemma first_match_typed Σ σ Λ bs v τs τ vs b :
    store_typed ge Σ σ ->
    [] ⊢ᵇ[ge;Σ;Λ] bs : τs ⇒ τ -> value v -> [] ⊢[ge;Σ;[]] v : τs ->
    first_match σ bs v = Some (vs, b) -> [] ⊢[ge;Σ;Λ] subst (args_sub vs) b : τ.
  Proof.
    intros Hσ H; remember (@nil ty) as Γ eqn:EΓ.
    induction H as [|Λ' Γ p b0 bs τs τ Δ Hp Hb Hbs IH]; intros Hv Ht E; subst.
    - discriminate.
    - simpl in E. destruct (pmatch σ p v) as [xs|] eqn:Em.
      + inversion E; subst.
        destruct (proj1 (pmatch_typed _ _ Hσ) _ _ _ Hp _ _ Hv Ht Em) as [Hxv Hxt].
        eapply subst_args_typing; [exact Hb|].
        intros Λ''. eapply values_any_labels; eassumption.
      + exact (IH eq_refl Hv Ht E).
  Qed.

  (** Values of primitive types are literals, so primitive operators can
      always read their arguments. *)
  Lemma as_lits_complete Σ Λ vs τs :
    Forall value vs -> [] ⊢*[ge;Σ;Λ] vs : τs ->
    Forall (fun t => exists b, t = TBase b) τs ->
    exists ls, as_lits vs = Some ls /\ lits_typed ls τs.
  Proof.
    intros Hv Ht; remember (@nil ty) as Γ eqn:EΓ.
    induction Ht as [|Λ' Γ e es τ τs He Hs IH]; intros Hb; subst.
    - exists []; split; [reflexivity | constructor].
    - inversion Hv as [|? ? Hve Hvs]; subst.
      inversion Hb as [|? ? [b ->] Hbs]; subst.
      destruct (canonical_base _ _ _ _ Hve He) as (l & -> & Hl).
      destruct (IH Hvs eq_refl Hbs) as (ls & Els & Hls).
      exists (l :: ls); simpl; rewrite Els; split; [reflexivity|].
      constructor; [congruence | exact Hls].
  Qed.

  Lemma as_lits_typed Σ Λ vs τs ls :
    as_lits vs = Some ls -> [] ⊢*[ge;Σ;Λ] vs : τs -> lits_typed ls τs.
  Proof.
    intros E Ht; revert ls E; induction Ht as [|Λ' Γ e es τ τs He Hs IH]; intros ls E.
    - inversion E; constructor.
    - simpl in E. destruct e; try discriminate.
      destruct (as_lits es) eqn:Ees; try discriminate. inversion E; subst.
      inversion He; subst. constructor; [reflexivity | exact (IH _ eq_refl)].
  Qed.

  (** ** Inversion helpers *)

  Lemma stack_cons_inv Σ F K τ τf :
    ⊢ᵏ[ge;Σ] F :: K : τ ⇒ τf ->
    exists τ2, ⊢ᶠ[ge;Σ;labels K] F : τ ⇒ τ2 /\ ⊢ᵏ[ge;Σ] K : τ2 ⇒ τf.
  Proof. intros H; inversion H; subst; eauto. Qed.

  Lemma eval_inv σ K e τf :
    ⊢ˢ[ge] ⟨σ ∣ K ▷ e⟩ : τf ->
    exists Σ τ, store_typed ge Σ σ /\ [] ⊢[ge;Σ;labels K] e : τ /\ ⊢ᵏ[ge;Σ] K : τ ⇒ τf.
  Proof. intros H; inversion H; subst; eauto 10. Qed.

  Lemma ret_inv σ K v τf :
    ⊢ˢ[ge] ⟨σ ∣ K ◁ v⟩ : τf ->
    exists Σ τ, store_typed ge Σ σ /\ value v /\ [] ⊢[ge;Σ;[]] v : τ /\
      ⊢ᵏ[ge;Σ] K : τ ⇒ τf.
  Proof. intros H; inversion H; subst; eauto 10. Qed.

  Lemma jump_inv σ K c k v τf :
    ⊢ˢ[ge] ⟨σ ∣ K ⇑ c k v⟩ : τf ->
    exists Σ lbl τ, store_typed ge Σ σ /\ value v /\ nth_error (labels K) k = Some lbl /\
      [] ⊢[ge;Σ;[]] v : ctl_ty c lbl /\ ⊢ᵏ[ge;Σ] K : τ ⇒ τf.
  Proof. intros H; inversion H; subst; eauto 10. Qed.

  Lemma has_types_snoc Σ Λ Γ es e τs τ :
    Γ ⊢*[ge;Σ;Λ] es : τs -> Γ ⊢[ge;Σ;Λ] e : τ -> Γ ⊢*[ge;Σ;Λ] es ++ [e] : τs ++ [τ].
  Proof. intros; apply has_types_app; auto using has_types. Qed.

  Lemma nil_lits_typed Σ Λ ts : [] ⊢*[ge;Σ;Λ] [] : ts -> lits_typed [] ts.
  Proof. intros H; inversion H; subst; constructor. Qed.

  (** ** Progress *)

  Theorem progress s τf :
    genv_ok ge -> ⊢ˢ[ge] s : τf -> final s \/ exists s', s ⟶[ge] s'.
  Proof.
    intros Hok Hs.
    destruct Hs as [Σ σ K e τ τf Hσ He HK | Σ σ K v τ τf Hσ Hv Hvt HK
                   | Σ σ K c k v lbl τ τf Hσ Hv Hk Hvt HK | τf].
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
        * assert (Hl := nil_lits_typed _ _ _ H).
          destruct (prim_eval_progress _ _ Hl) as [Ea | (l & El & _)].
          -- eexists; eapply S_PrimNilAbort; exact Ea.
          -- eexists; eapply S_PrimNil; exact El.
        * eexists; apply S_PrimCons.
      + eexists; apply S_Constr.
      + eexists; apply S_Match.
      + eexists; apply S_Loc.
      + destruct args as [|a args].
        * destruct (mem_eval_sound Σ σ op [] Hσ (Forall_nil _)
                      (values_any_labels _ _ _ _ _ _ (Forall_nil _) H)) as (r & Er & _).
          eexists; eapply S_MemNil; exact Er.
        * eexists; apply S_MemCons.
      + eexists; apply S_Loop.
      + eexists; apply S_Jump.
      + eexists; apply S_Abort.
    - (* SRet *)
      destruct K as [|F K]; [left; exact Hv | right].
      apply stack_cons_inv in HK as (τ2 & HF & HK).
      destruct HF.
      + destruct args.
        * destruct (canonical_arrow _ _ _ _ _ Hv Hvt) as (b & -> & _).
          eexists; apply S_AppFunNil.
        * eexists; apply S_AppFunCons.
      + destruct rest.
        * destruct (canonical_arrow _ _ _ _ _ H H0) as (b & -> & _).
          eexists; apply S_AppArgLast.
        * eexists; apply S_AppArgNext.
      + eexists; apply S_LetRet.
      + destruct (canonical_bool _ _ _ Hv Hvt) as ([] & ->); eexists;
          [apply S_IfTrue | apply S_IfFalse].
      + destruct rest; eexists; [apply S_TupleLast | apply S_TupleNext].
      + destruct (canonical_tuple _ _ _ _ Hv Hvt) as (vs & -> & _ & Hvs).
        destruct (has_types_nth_error _ _ _ _ _ _ _ _ Hvs H) as (w & Ew & _).
        eexists; apply S_ProjRet; eauto.
      + destruct rest as [|e rest].
        * inversion H2; subst.
          assert (Hb := prim_sig_args_base op). rewrite H in Hb.
          destruct (as_lits_complete Σ [] (done ++ [v]) (τsd ++ [τ]))
            as (ls & Els & Hls).
          -- now apply Forall_snoc.
          -- now apply has_types_snoc.
          -- exact Hb.
          -- rewrite <- H in Hls.
             destruct (prim_eval_progress _ _ Hls) as [Ea | (l & El & _)].
             ++ eexists; eapply S_PrimLastAbort; eauto.
             ++ eexists; eapply S_PrimLast; eauto.
        * eexists; apply S_PrimNext.
      + eexists; apply S_ConstrRet.
      + destruct (first_match σ bs v) as [[vs b]|] eqn:E; eexists;
          [eapply S_MatchRet | eapply S_MatchFail]; eauto.
      + destruct rest as [|e rest].
        * inversion H2; subst.
          destruct (mem_eval_sound Σ σ op (done ++ [v])) as (r & Er & _).
          -- exact Hσ.
          -- now apply Forall_snoc.
          -- rewrite H. now apply has_types_snoc.
          -- eexists; eapply S_MemLast; exact Er.
        * eexists; apply S_MemNext.
      + destruct (canonical_tuple _ _ _ _ Hv Hvt) as (vs & -> & _ & _).
        eexists; apply S_LoopEnter.
      + eexists; apply S_LoopRet.
      + eexists; apply S_JumpRet.
    - (* SJump *)
      right. destruct K as [|F K]; [destruct k; discriminate|].
      destruct (is_loop F) eqn:EF; [|eexists; apply S_UnwindPop; exact EF].
      destruct F; try discriminate.
      destruct k as [|k]; [|eexists; apply S_UnwindOuter].
      simpl in Hk. inversion Hk; subst.
      destruct c.
      + eexists; apply S_Break.
      + destruct (canonical_tuple _ _ _ _ Hv Hvt) as (vs & -> & _ & _).
        eexists; apply S_Continue.
    - left; exact I.
  Qed.

  (** ** Preservation *)

  Lemma has_types_cons_inv Σ Λ Γ e es ts :
    Γ ⊢*[ge;Σ;Λ] e :: es : ts ->
    exists τ τs, ts = τ :: τs /\ Γ ⊢[ge;Σ;Λ] e : τ /\ Γ ⊢*[ge;Σ;Λ] es : τs.
  Proof. intros H; inversion H; subst; eauto. Qed.

  Lemma has_type_prim_inv Σ Λ Γ op args τ :
    Γ ⊢[ge;Σ;Λ] EPrim op args : τ ->
    τ = snd (prim_sig op) /\ Γ ⊢*[ge;Σ;Λ] args : fst (prim_sig op).
  Proof. intros H; inversion H; subst; auto. Qed.

  Lemma has_type_mem_inv Σ Λ Γ op args τ :
    Γ ⊢[ge;Σ;Λ] EMem op args : τ ->
    τ = snd (mem_sig op) /\ Γ ⊢*[ge;Σ;Λ] args : fst (mem_sig op).
  Proof. intros H; inversion H; subst; auto. Qed.

  (* The state reached by a well-typed store operation is well typed. *)
  Lemma mres_state_typed Σ op r K τf :
    mres_ok Σ op r -> ⊢ᵏ[ge;Σ] K : snd (mem_sig op) ⇒ τf ->
    ⊢ˢ[ge] mres_state K r : τf.
  Proof.
    destruct r as [σ' v|]; simpl; [|constructor].
    intros (Σ' & Hσ & Hv & Ht) HK.
    eapply SS_Ret; [exact Hσ | exact Hv | exact Ht | apply stack_weaken, HK].
  Qed.

  (* Unify two hypotheses [a = Some x], [a = Some y]. *)
  Local Ltac some_eq :=
    repeat match goal with
    | H1 : ?a = Some _, H2 : ?a = Some _ |- _ =>
        rewrite H1 in H2; inversion H2; subst; clear H2
    | H1 : ?a = PVal _, H2 : ?a = PVal _ |- _ =>
        rewrite H1 in H2; inversion H2; subst; clear H2
    end.

  (* Open an evaluation state. *)
  Local Ltac open_eval Hs :=
    apply eval_inv in Hs as (Σ & ?τe & Hσ & He & HK).

  (* Open a return state: value, its type, and the top frame's typing. *)
  Local Ltac open_ret Hs :=
    apply ret_inv in Hs as (Σ & τv & Hσ & Hv & Hvt & HK);
    apply stack_cons_inv in HK as (τk & HF & HK);
    inversion HF; subst; clear HF.

  (* Push a frame: the new expression keeps the labels of [K]. *)
  Local Ltac push :=
    eapply SS_Eval; [eassumption | eassumption |]; eapply ST_cons; [|eassumption].

  (* Produce a value from an evaluation state. *)
  Local Ltac produce :=
    eapply SS_Ret; [eassumption | constructor
                   | eapply value_any_labels; [constructor | eassumption] | eassumption].

  Theorem preservation s s' τf :
    genv_ok ge -> ⊢ˢ[ge] s : τf -> s ⟶[ge] s' -> ⊢ˢ[ge] s' : τf.
  Proof.
    intros Hok Hs Hstep. destruct Hstep.
    (* ---- evaluation steps ---- *)
    - (* S_Lit *) open_eval Hs. produce.
    - (* S_Lam *) open_eval Hs. produce.
    - (* S_Global *)
      open_eval Hs. inversion He; subst. some_eq.
      eapply SS_Ret; [eassumption | apply V_Lam | eapply global_inst_typing; eauto | exact HK].
    - (* S_App *) open_eval Hs. inversion He; subst. push. constructor; assumption.
    - (* S_Let *) open_eval Hs. inversion He; subst. push. constructor; assumption.
    - (* S_If *) open_eval Hs. inversion He; subst. push. constructor; assumption.
    - (* S_TupleNil *)
      open_eval Hs. inversion He; subst. inv_types.
      eapply SS_Ret; [eassumption | repeat constructor | repeat constructor | exact HK].
    - (* S_TupleCons *)
      open_eval Hs. inversion He; subst. inv_types.
      push. apply (FT_Tuple ge Σ _ [] es []); auto using has_types.
    - (* S_Proj *) open_eval Hs. inversion He; subst. push. econstructor; eassumption.
    - (* S_PrimNil *)
      open_eval Hs. apply has_type_prim_inv in He as [-> Hargs].
      destruct (prim_eval_progress _ _ (nil_lits_typed _ _ _ Hargs))
        as [Ea | (l' & El & Ht)]; [congruence|].
      some_eq.
      eapply SS_Ret; [eassumption | constructor | | exact HK]. rewrite <- Ht. constructor.
    - (* S_PrimNilAbort *) constructor.
    - (* S_PrimCons *)
      open_eval Hs. apply has_type_prim_inv in He as [-> Hargs].
      apply has_types_cons_inv in Hargs as (τ0 & τs & Ets & He0 & Hes).
      push. apply (FT_Prim ge Σ _ op [] es [] τ0 τs); auto using has_types.
    (* ---- return steps ---- *)
    - (* S_AppFunNil *)
      open_ret Hs. inv_types. inversion Hvt; subst.
      eapply SS_Eval; [eassumption | | exact HK].
      apply weaken_labels. eapply subst_args_typing; [eassumption | intros; constructor].
    - (* S_AppFunCons *)
      open_ret Hs. inv_types.
      push. eapply (FT_AppArg ge Σ _ f [] args []); eauto using has_types, Forall.
    - (* S_AppArgLast *)
      open_ret Hs. inv_types.
      match goal with Hf : has_type _ _ _ _ (ELam _ _ _) _ |- _ => inversion Hf; subst end.
      eapply SS_Eval; [eassumption | | exact HK].
      apply weaken_labels. eapply subst_args_typing; [eassumption|].
      intros Λ'. eapply values_any_labels; [apply Forall_snoc; eassumption|].
      apply has_types_snoc; eassumption.
    - (* S_AppArgNext *)
      open_ret Hs. inv_types.
      push.
      match goal with
      | Hf : has_type _ _ _ _ f (TArrow (?psd ++ ?t :: ?ta :: ?psr) _) |- _ =>
          apply (FT_AppArg ge Σ _ f (done ++ [v]) rest (psd ++ [t]) ta psr);
          [ assumption
          | rewrite <- app_assoc; exact Hf
          | apply Forall_snoc; assumption
          | apply has_types_snoc; assumption
          | assumption ]
      end.
    - (* S_LetRet *)
      open_ret Hs.
      eapply SS_Eval; [eassumption | | exact HK].
      eapply (subst_args_typing ge Σ _ [_]); [eassumption|].
      intros Λ'. constructor; [eapply value_any_labels; eassumption | constructor].
    - (* S_IfTrue *) open_ret Hs. eapply SS_Eval; [eassumption | eassumption | exact HK].
    - (* S_IfFalse *) open_ret Hs. eapply SS_Eval; [eassumption | eassumption | exact HK].
    - (* S_TupleLast *)
      open_ret Hs. inv_types.
      eapply SS_Ret; [eassumption | | | exact HK].
      + constructor; apply Forall_snoc; assumption.
      + constructor; apply has_types_snoc; assumption.
    - (* S_TupleNext *)
      open_ret Hs. inv_types.
      push.
      match goal with
      | |- ⊢ᶠ[_;_;_] _ : _ ⇒ TTuple (?a ++ ?t :: ?rest) =>
          replace (a ++ t :: rest) with ((a ++ [t]) ++ rest) by (now rewrite <- app_assoc)
      end.
      constructor; [apply Forall_snoc | apply has_types_snoc | ]; assumption.
    - (* S_ProjRet *)
      open_ret Hs.
      inversion Hv as [| | ? Hvs | |]; subst. inversion Hvt; subst.
      match goal with
      | Hts : has_types _ _ _ _ vs ?ts, Hn : nth_error ?ts i = Some _ |- _ =>
          destruct (has_types_nth_error _ _ _ _ _ _ _ _ Hts Hn) as (w & Ew & Hw)
      end.
      some_eq.
      eapply SS_Ret; [eassumption | | eassumption | exact HK].
      rewrite Forall_forall in Hvs. eapply Hvs, nth_error_In; eassumption.
    - (* S_PrimLast *)
      open_ret Hs. inv_types.
      assert (Hls : lits_typed ls (fst (prim_sig op))).
      { match goal with E : fst (prim_sig op) = _ |- _ => rewrite E end.
        eapply as_lits_typed; [eassumption|]. apply has_types_snoc; eassumption. }
      destruct (prim_eval_progress _ _ Hls) as [Ea | (l' & El & Ht)]; [congruence|].
      some_eq.
      eapply SS_Ret; [eassumption | constructor | | exact HK]. rewrite <- Ht. constructor.
    - (* S_PrimLastAbort *) constructor.
    - (* S_PrimNext *)
      open_ret Hs. inv_types.
      push.
      match goal with
      | E : fst (prim_sig op) = ?a ++ ?t :: ?te :: ?r |- _ =>
          apply (FT_Prim ge Σ _ op (done ++ [v]) rest (a ++ [t]) te r);
          [ rewrite E, <- app_assoc; reflexivity
          | apply Forall_snoc; assumption
          | apply has_types_snoc; assumption
          | assumption ]
      end.
    (* ---- data types ---- *)
    - (* S_Constr *) open_eval Hs. inversion He; subst. push. econstructor; eassumption.
    - (* S_Match *) open_eval Hs. inversion He; subst. push. constructor; assumption.
    - (* S_ConstrRet *)
      open_ret Hs.
      eapply SS_Ret; [eassumption | constructor; assumption | econstructor; eassumption | exact HK].
    - (* S_MatchRet *)
      open_ret Hs.
      eapply SS_Eval; [eassumption | | exact HK]. eapply first_match_typed; eassumption.
    - (* S_MatchFail *) constructor.
    (* ---- store ---- *)
    - (* S_Loc *) open_eval Hs. produce.
    - (* S_MemNil *)
      open_eval Hs. apply has_type_mem_inv in He as [-> Hargs].
      destruct (mem_eval_sound Σ σ op [] Hσ (Forall_nil _)
                  (values_any_labels _ _ _ _ _ _ (Forall_nil _) Hargs)) as (r' & Er & Hr).
      some_eq. eapply mres_state_typed; eassumption.
    - (* S_MemCons *)
      open_eval Hs. apply has_type_mem_inv in He as [-> Hargs].
      apply has_types_cons_inv in Hargs as (τ0 & τs & Ets & He0 & Hes).
      push. apply (FT_Mem ge Σ _ op [] es [] τ0 τs); auto using has_types.
    - (* S_MemLast *)
      open_ret Hs. inv_types.
      destruct (mem_eval_sound Σ σ op (done ++ [v])) as (r' & Er & Hr).
      + eassumption.
      + apply Forall_snoc; assumption.
      + match goal with E : fst (mem_sig op) = _ |- _ => rewrite E end.
        apply has_types_snoc; assumption.
      + some_eq. eapply mres_state_typed; eassumption.
    - (* S_MemNext *)
      open_ret Hs. inv_types.
      push.
      match goal with
      | E : fst (mem_sig op) = ?a ++ ?t :: ?te :: ?r |- _ =>
          apply (FT_Mem ge Σ _ op (done ++ [v]) rest (a ++ [t]) te r);
          [ rewrite E, <- app_assoc; reflexivity
          | apply Forall_snoc; assumption
          | apply has_types_snoc; assumption
          | assumption ]
      end.
    (* ---- loops and jumps ---- *)
    - (* S_Loop *)
      open_eval Hs. inversion He; subst. push. constructor; assumption.
    - (* S_LoopEnter *)
      open_ret Hs.
      destruct (canonical_tuple _ _ _ _ Hv Hvt) as (vs' & E & Hvs & Hts).
      inversion E; subst.
      eapply SS_Eval; [eassumption | | eapply ST_cons; [constructor; eassumption | exact HK]].
      eapply subst_args_typing; [eassumption|].
      intros Λ'. eapply values_any_labels; eassumption.
    - (* S_LoopRet *)
      open_ret Hs. eapply SS_Ret; [eassumption | eassumption | eassumption | exact HK].
    - (* S_Jump *)
      open_eval Hs. inversion He; subst. push. constructor; assumption.
    - (* S_JumpRet *)
      open_ret Hs. eapply SS_Jump; eassumption.
    - (* S_UnwindPop *)
      apply jump_inv in Hs as (Σ & lbl & τ & Hσ & Hv & Hk & Hvt & HK).
      apply stack_cons_inv in HK as (τ2 & _ & HK).
      rewrite labels_nonloop in Hk by assumption.
      eapply SS_Jump; eassumption.
    - (* S_UnwindOuter *)
      apply jump_inv in Hs as (Σ & lbl & τ' & Hσ & Hv & Hk & Hvt & HK).
      apply stack_cons_inv in HK as (τ2 & _ & HK).
      simpl in Hk. eapply SS_Jump; eassumption.
    - (* S_Break *)
      apply jump_inv in Hs as (Σ & lbl & τ' & Hσ & Hv & Hk & Hvt & HK).
      simpl in Hk. inversion Hk; subst.
      apply stack_cons_inv in HK as (τ2 & HF & HK). inversion HF; subst.
      eapply SS_Ret; eassumption.
    - (* S_Continue *)
      apply jump_inv in Hs as (Σ & lbl & τ' & Hσ & Hv & Hk & Hvt & HK).
      simpl in Hk. inversion Hk; subst.
      assert (HK' := HK).
      apply stack_cons_inv in HK as (τ2 & HF & _). inversion HF; subst.
      inversion Hv as [| | ? Hvs | |]; subst. inversion Hvt; subst.
      eapply SS_Eval; [eassumption | | exact HK'].
      eapply subst_args_typing; [eassumption|].
      intros Λ'. eapply values_any_labels; eassumption.
    (* ---- explicit panic ---- *)
    - (* S_Abort *) constructor.
  Qed.

  (** ** Soundness *)

  Lemma star_preservation s s' τf :
    genv_ok ge -> ⊢ˢ[ge] s : τf -> s ⟶*[ge] s' -> ⊢ˢ[ge] s' : τf.
  Proof. intros Hok Hs H; induction H; eauto using preservation. Qed.

  Lemma initial_typed e τ :
    [] ⊢[ge;[];[]] e : τ -> ⊢ˢ[ge] ⟨[] ∣ [] ▷ e⟩ : τ.
  Proof. intros; eapply SS_Eval; [constructor | eassumption | constructor]. Qed.

  (** A well-typed program never gets stuck. *)
  Theorem soundness e τ s :
    genv_ok ge -> [] ⊢[ge;[];[]] e : τ -> ⟨[] ∣ [] ▷ e⟩ ⟶*[ge] s -> ~ stuck ge s.
  Proof.
    intros Hok He Hstar [Hnf Hns].
    destruct (progress s τ Hok (star_preservation _ _ _ Hok (initial_typed _ _ He) Hstar))
      as [Hf | Hstep]; contradiction.
  Qed.

  (** If a well-typed program terminates normally, the result is a value of
      the program's type (in the final store). *)
  Theorem soundness_value e τ σ v :
    genv_ok ge -> [] ⊢[ge;[];[]] e : τ -> ⟨[] ∣ [] ▷ e⟩ ⟶*[ge] ⟨σ ∣ [] ◁ v⟩ ->
    value v /\ exists Σ, store_typed ge Σ σ /\ [] ⊢[ge;Σ;[]] v : τ.
  Proof.
    intros Hok He Hstar.
    apply (star_preservation _ _ _ Hok (initial_typed _ _ He)) in Hstar.
    apply ret_inv in Hstar as (Σ & τ' & Hσ & Hv & Hvt & HK).
    inversion HK; subst; eauto.
  Qed.
End Soundness.
