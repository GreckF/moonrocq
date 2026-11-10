(** * First-order unification (milestone M6b)

    Metavariables are the type variables [TVar i] with [i >= nt]; those
    below [nt] are the type parameters of the current definition and are
    rigid.  A substitution is an association list [θ] acting by
    [sapp θ = tsubst (look θ)], kept idempotent.

    [unify] follows McBride's structurally recursive presentation: the
    outer recursion is on a bound on the number of unsolved
    metavariables (every binding solves one), the inner recursion is
    structural on the types.  Hence no well-founded recursion is needed and
    the function computes in the kernel.

    Results:
    - [unify_sound]: the result unifies the equations, and extends [θ];
    - [unify_mgu]: it is most general: every unifier extending [θ] factors
      through it;
    - [unify_complete]: if a unifier extending [θ] exists (one that leaves
      the rigid variables alone), [unify] succeeds. *)

From Stdlib Require Import List Arith Lia Bool.
From MoonRocq.Prelude Require Import EqDec.
From MoonRocq.Core Require Import Syntax Subst.
Import ListNotations.

(** ** Occurrences and size *)

Fixpoint occurs (k : nat) (t : ty) : bool :=
  match t with
  | TVar j => Nat.eqb k j
  | TBase _ | TError => false
  | TTuple ts | TData _ ts => existsb (occurs k) ts
  | TArrow ps r ε => (existsb (occurs k) ps || occurs k r || occurs k ε)%bool
  | TRef t | TArray _ t => occurs k t
  end.

Fixpoint tsize (t : ty) : nat :=
  match t with
  | TVar _ | TBase _ | TError => 1
  | TTuple ts | TData _ ts => S (list_sum (map tsize ts))
  | TArrow ps r ε => S (list_sum (map tsize ps) + tsize r + tsize ε)
  | TRef t | TArray _ t => S (tsize t)
  end.

Lemma existsb_occ k ts : existsb (occurs k) ts = true <-> exists u, In u ts /\ occurs k u = true.
Proof. apply existsb_exists. Qed.

Lemma tsubst_ext_occ σ σ' t :
  (forall k, occurs k t = true -> σ k = σ' k) -> tsubst σ t = tsubst σ' t.
Proof.
  induction t as [b|i|ts IH|ps r ε IHps IHr IHε|T ts IH|t IH|k t IH|] using ty_ind';
    simpl; intros H; try reflexivity.
  - apply H; apply Nat.eqb_refl.
  - f_equal; apply map_ext_in; intros u Hu; rewrite Forall_forall in IH; apply IH; auto.
    intros k Hk; apply H; apply existsb_occ; eauto.
  - f_equal.
    + apply map_ext_in; intros u Hu; rewrite Forall_forall in IHps; apply IHps; auto.
      intros k Hk; apply H; rewrite !orb_true_iff; left; left; apply existsb_occ; eauto.
    + apply IHr; intros k Hk; apply H; rewrite !orb_true_iff; left; right; exact Hk.
    + apply IHε; intros k Hk; apply H; rewrite !orb_true_iff; right; exact Hk.
  - f_equal; apply map_ext_in; intros u Hu; rewrite Forall_forall in IH; apply IH; auto.
    intros k Hk; apply H; apply existsb_occ; eauto.
  - f_equal; apply IH; exact H.
  - f_equal; apply IH; exact H.
Qed.

Lemma tsubst_var t : tsubst TVar t = t.
Proof.
  induction t as [b|i|ts IH|ps r ε IHps IHr IHε|T ts IH|t IH|k t IH|] using ty_ind';
    simpl; f_equal; auto;
    match goal with H : Forall _ ?l |- map _ ?l = ?l =>
      induction H; simpl; f_equal; auto end.
Qed.

Lemma occurs_tsubst σ k t :
  occurs k (tsubst σ t) = true -> exists j, occurs j t = true /\ occurs k (σ j) = true.
Proof.
  induction t as [b|i|ts IH|ps r ε IHps IHr IHε|T ts IH|t IH|k' t IH|] using ty_ind';
    simpl; intros H; try discriminate.
  - exists i; rewrite Nat.eqb_refl; auto.
  - apply existsb_occ in H as (u & Hu & Hk). apply in_map_iff in Hu as (v & <- & Hv).
    rewrite Forall_forall in IH; destruct (IH v Hv Hk) as (j & Hj & Hk').
    exists j; split; auto; apply existsb_occ; eauto.
  - rewrite !orb_true_iff in H; destruct H as [[H|H]|H].
    + apply existsb_occ in H as (u & Hu & Hk). apply in_map_iff in Hu as (v & <- & Hv).
      rewrite Forall_forall in IHps; destruct (IHps v Hv Hk) as (j & Hj & Hk').
      exists j; split; auto; rewrite !orb_true_iff; left; left; apply existsb_occ; eauto.
    + destruct (IHr H) as (j & Hj & Hk'); exists j; rewrite !orb_true_iff; auto.
    + destruct (IHε H) as (j & Hj & Hk'); exists j; rewrite !orb_true_iff; auto.
  - apply existsb_occ in H as (u & Hu & Hk). apply in_map_iff in Hu as (v & <- & Hv).
    rewrite Forall_forall in IH; destruct (IH v Hv Hk) as (j & Hj & Hk').
    exists j; split; auto; apply existsb_occ; eauto.
  - auto.
  - auto.
Qed.

Lemma occurs_tsubst_intro σ k j t :
  occurs j t = true -> occurs k (σ j) = true -> occurs k (tsubst σ t) = true.
Proof.
  induction t as [b|i|ts IH|ps r ε IHps IHr IHε|T ts IH|t IH|k' t IH|] using ty_ind';
    simpl; intros H Hk; try discriminate.
  - apply Nat.eqb_eq in H; subst; exact Hk.
  - apply existsb_occ in H as (u & Hu & Hj). apply existsb_occ.
    rewrite Forall_forall in IH; exists (tsubst σ u); split; [apply in_map; auto|auto].
  - rewrite !orb_true_iff in H |- *; destruct H as [[H|H]|H]; auto.
    left; left. apply existsb_occ in H as (u & Hu & Hj). apply existsb_occ.
    rewrite Forall_forall in IHps; exists (tsubst σ u); split; [apply in_map; auto|auto].
  - apply existsb_occ in H as (u & Hu & Hj). apply existsb_occ.
    rewrite Forall_forall in IH; exists (tsubst σ u); split; [apply in_map; auto|auto].
  - auto.
  - auto.
Qed.

(** A variable of a type fixed by [σ] is fixed by [σ]. *)
Lemma fixed_occ σ k t : tsubst σ t = t -> occurs k t = true -> σ k = TVar k.
Proof.
  induction t as [b|i|ts IH|ps r ε IHps IHr IHε|T ts IH|t IH|k' t IH|] using ty_ind';
    simpl; intros Ht H; try discriminate.
  - apply Nat.eqb_eq in H; subst; exact Ht.
  - injection Ht as Ht. apply existsb_occ in H as (u & Hu & Hk).
    rewrite Forall_forall in IH; apply (IH u Hu); auto.
    clear -Ht Hu; induction ts as [|v ts IHts]; simpl in *; [contradiction|].
    injection Ht as H1 H2; destruct Hu as [<-|Hu]; auto.
  - injection Ht as Hps Hr Hε. rewrite !orb_true_iff in H; destruct H as [[H|H]|H]; auto.
    apply existsb_occ in H as (u & Hu & Hk).
    rewrite Forall_forall in IHps; apply (IHps u Hu); auto.
    clear -Hps Hu; induction ps as [|v ps IHps]; simpl in *; [contradiction|].
    injection Hps as H1 H2; destruct Hu as [<-|Hu]; auto.
  - injection Ht as Ht. apply existsb_occ in H as (u & Hu & Hk).
    rewrite Forall_forall in IH; apply (IH u Hu); auto.
    clear -Ht Hu; induction ts as [|v ts IHts]; simpl in *; [contradiction|].
    injection Ht as H1 H2; destruct Hu as [<-|Hu]; auto.
  - injection Ht as Ht; auto.
  - injection Ht as Ht; auto.
Qed.

Lemma list_sum_in (f : ty -> nat) u l : In u l -> f u <= list_sum (map f l).
Proof. induction l as [|v l IH]; simpl; [contradiction|]; intros [<-|H]; [lia|]; specialize (IH H); lia. Qed.

(** An occurrence of [k] in [t] makes [tsubst s t] at least as large as
    [s k], and larger unless [t] is [k] itself. *)
Lemma occurs_size s k t :
  occurs k t = true -> tsize (s k) + (match t with TVar _ => 0 | _ => 1 end) <= tsize (tsubst s t).
Proof.
  induction t as [b|i|ts IH|ps r ε IHps IHr IHε|T ts IH|t IH|k' t IH|] using ty_ind';
    simpl; intros H; try discriminate.
  - apply Nat.eqb_eq in H; subst; lia.
  - apply existsb_occ in H as (u & Hu & Hk). rewrite Forall_forall in IH.
    specialize (IH u Hu Hk). rewrite map_map.
    pose proof (list_sum_in (fun x => tsize (tsubst s x)) u ts Hu); simpl in *.
    destruct u; lia.
  - rewrite !orb_true_iff in H; destruct H as [[H|H]|H].
    + apply existsb_occ in H as (u & Hu & Hk). rewrite Forall_forall in IHps.
      specialize (IHps u Hu Hk). rewrite map_map.
      pose proof (list_sum_in (fun x => tsize (tsubst s x)) u ps Hu); simpl in *.
      destruct u; lia.
    + specialize (IHr H); destruct r; lia.
    + specialize (IHε H); destruct ε; lia.
  - apply existsb_occ in H as (u & Hu & Hk). rewrite Forall_forall in IH.
    specialize (IH u Hu Hk). rewrite map_map.
    pose proof (list_sum_in (fun x => tsize (tsubst s x)) u ts Hu); simpl in *.
    destruct u; lia.
  - specialize (IH H); destruct t; lia.
  - specialize (IH H); destruct t; lia.
Qed.

(** ** Substitutions *)

Definition sub : Type := list (nat * ty).

Fixpoint look (θ : sub) (i : nat) : ty :=
  match θ with
  | [] => TVar i
  | (k, u) :: θ' => if Nat.eqb k i then u else look θ' i
  end.

Definition sapp (θ : sub) (t : ty) : ty := tsubst (look θ) t.

Definition single (i : nat) (t : ty) (j : nat) : ty := if Nat.eqb j i then t else TVar j.

Definition bind (i : nat) (t : ty) (θ : sub) : sub :=
  (i, t) :: map (fun ku => (fst ku, tsubst (single i t) (snd ku))) θ.

(** [θ] is idempotent. *)
Definition idem (θ : sub) : Prop := forall j, sapp θ (look θ j) = look θ j.

(** [s] absorbs [θ]: [s] is [s] after [θ]. *)
Definition absorbs (s : nat -> ty) (θ : sub) : Prop := forall j, tsubst s (look θ j) = s j.

Lemma absorbs_sapp s θ t : absorbs s θ -> tsubst s (sapp θ t) = tsubst s t.
Proof.
  intros H; unfold sapp; rewrite tsubst_comp; apply tsubst_ext_occ; intros k _; apply H.
Qed.

Lemma idem_absorbs θ : idem θ -> absorbs (look θ) θ.
Proof. intros H j; apply H. Qed.

Lemma sapp_idem θ t : idem θ -> sapp θ (sapp θ t) = sapp θ t.
Proof. intros H; apply (absorbs_sapp (look θ)), idem_absorbs, H. Qed.

Lemma look_map_single i t θ j :
  j <> i ->
  look (map (fun ku => (fst ku, tsubst (single i t) (snd ku))) θ) j = tsubst (single i t) (look θ j).
Proof.
  intros Hj; induction θ as [|[k u] θ IH]; simpl.
  - unfold single; apply Nat.eqb_neq in Hj; rewrite Hj; reflexivity.
  - destruct (Nat.eqb k j); auto.
Qed.

Lemma look_bind i t θ j :
  look θ i = TVar i -> look (bind i t θ) j = tsubst (single i t) (look θ j).
Proof.
  intros Hi; unfold bind; simpl.
  destruct (Nat.eqb i j) eqn:E.
  - apply Nat.eqb_eq in E; subst; rewrite Hi; simpl; unfold single; rewrite Nat.eqb_refl; reflexivity.
  - apply look_map_single; apply Nat.eqb_neq in E; auto.
Qed.

Lemma sapp_bind i t θ x :
  look θ i = TVar i -> sapp (bind i t θ) x = tsubst (single i t) (sapp θ x).
Proof.
  intros Hi; unfold sapp; rewrite tsubst_comp; apply tsubst_ext_occ; intros k _; apply look_bind; auto.
Qed.

Lemma single_fresh i t u : occurs i u = false -> tsubst (single i t) u = u.
Proof.
  intros H; rewrite <- (tsubst_var u) at 2; apply tsubst_ext_occ; intros k Hk.
  unfold single; destruct (Nat.eqb k i) eqn:E; auto.
  apply Nat.eqb_eq in E; subst; congruence.
Qed.

(** The conditions under which [i := t] may be added to [θ]. *)
Definition can_bind (θ : sub) (i : nat) (t : ty) : Prop :=
  look θ i = TVar i /\ sapp θ t = t /\ occurs i t = false.

Lemma single_at i t : single i t i = t.
Proof. unfold single; rewrite Nat.eqb_refl; reflexivity. Qed.

Lemma single_ne i t k : k <> i -> single i t k = TVar k.
Proof. intros H; unfold single; apply Nat.eqb_neq in H; rewrite H; reflexivity. Qed.

Lemma bind_idem θ i t : idem θ -> can_bind θ i t -> idem (bind i t θ).
Proof.
  intros Hid (Hi & Ht & Ho) j.
  rewrite look_bind by exact Hi; rewrite sapp_bind by exact Hi.
  unfold sapp; rewrite !tsubst_comp.
  apply tsubst_ext_occ; intros k Hk; cbv beta.
  pose proof (fixed_occ _ _ _ (Hid j) Hk) as Hkk.
  destruct (Nat.eq_dec k i) as [->|Hne].
  - rewrite !single_at, <- tsubst_comp. unfold sapp in Ht; rewrite Ht.
    apply single_fresh; exact Ho.
  - rewrite (single_ne _ _ _ Hne); simpl; rewrite Hkk; simpl; apply single_ne; exact Hne.
Qed.

Lemma bind_absorbs θ i t : idem θ -> can_bind θ i t -> absorbs (look (bind i t θ)) θ.
Proof.
  intros Hid (Hi & Ht & Ho) j.
  change (sapp (bind i t θ) (look θ j) = look (bind i t θ) j).
  rewrite sapp_bind, look_bind by exact Hi. rewrite (Hid j). reflexivity.
Qed.

Lemma bind_general s θ i t :
  can_bind θ i t -> absorbs s θ -> s i = tsubst s t -> absorbs s (bind i t θ).
Proof.
  intros (Hi & Ht & Ho) Hs Hst j.
  rewrite look_bind by exact Hi. rewrite tsubst_comp.
  rewrite <- (Hs j). apply tsubst_ext_occ; intros k _.
  unfold single; destruct (Nat.eqb k i) eqn:E; simpl; auto.
  apply Nat.eqb_eq in E; subst; auto.
Qed.

Lemma absorbs_trans s θ1 θ : absorbs s θ1 -> absorbs (look θ1) θ -> absorbs s θ.
Proof.
  intros H1 H j. rewrite <- (H1 j), <- (H j).
  change (tsubst s (look θ j) = tsubst s (sapp θ1 (look θ j))).
  symmetry; apply absorbs_sapp; exact H1.
Qed.

(** ** The algorithm *)

Section Unify.
  (** Type variables below [nt] are rigid. *)
  Variable nt : nat.

  Definition meta (i : nat) : bool := Nat.leb nt i.

  (** One step on a pair of types to which [θ] is already applied: fail,
      succeed without binding anything, or bind one metavariable and leave
      the pairs [rest] still to be unified (under the new substitution). *)
  Definition r1 : Type := option (option (sub * list (ty * ty))).

  Definition bindr (θ : sub) (i : nat) (t : ty) : r1 :=
    if occurs i t then None else Some (Some (bind i t θ, [])).

  (** After a step [r], the pairs [pairs]; if [r] bound nothing, [k]. *)
  Definition seqr (r : r1) (pairs : list (ty * ty)) (k : r1) : r1 :=
    match r with
    | None => None
    | Some None => k
    | Some (Some (θ', rest)) => Some (Some (θ', rest ++ pairs))
    end.

  (** Pairwise, for lists of the same length. *)
  Definition unis_with (f : ty -> ty -> r1) : list ty -> list ty -> r1 :=
    fix go xs ys :=
      match xs, ys with
      | [], [] => Some None
      | x :: xs', y :: ys' =>
          if Nat.eqb (length xs') (length ys')
          then seqr (f x y) (combine xs' ys') (go xs' ys')
          else None
      | _, _ => None
      end.

  Fixpoint uni (θ : sub) (a b : ty) {struct a} : r1 :=
    match a, b with
    | TVar i, TVar j =>
        if Nat.eqb i j then Some None
        else if meta i then bindr θ i b
        else if meta j then bindr θ j a
        else None
    | TVar i, _ => if meta i then bindr θ i b else None
    | _, TVar j => if meta j then bindr θ j a else None
    | TBase x, TBase y => if base_ty_eq_dec x y then Some None else None
    | TTuple xs, TTuple ys => unis_with (uni θ) xs ys
    | TArrow ps r ε, TArrow ps' r' ε' =>
        seqr (unis_with (uni θ) ps ps') [(r, r'); (ε, ε')] (seqr (uni θ r r') [(ε, ε')] (uni θ ε ε'))
    | TData T xs, TData U ys => if eq_dec T U then unis_with (uni θ) xs ys else None
    | TRef x, TRef y => uni θ x y
    | TArray k x, TArray k' y => if array_kind_eq_dec k k' then uni θ x y else None
    | TError, TError => Some None
    | _, _ => None
    end.

  Definition unis (θ : sub) : list ty -> list ty -> r1 := unis_with (uni θ).

  Lemma uni_tuple θ xs ys : uni θ (TTuple xs) (TTuple ys) = unis θ xs ys.
  Proof. reflexivity. Qed.

  Lemma uni_arrow θ ps r ε ps' r' ε' :
    uni θ (TArrow ps r ε) (TArrow ps' r' ε') =
    seqr (unis θ ps ps') [(r, r'); (ε, ε')] (seqr (uni θ r r') [(ε, ε')] (uni θ ε ε')).
  Proof. reflexivity. Qed.

  Lemma uni_data θ T U xs ys :
    uni θ (TData T xs) (TData U ys) = if eq_dec T U then unis θ xs ys else None.
  Proof. reflexivity. Qed.

  (** Unify the pairs [eqs] under [θ]; [n] bounds the number of bindings. *)
  Fixpoint unify_n (n : nat) (θ : sub) (eqs : list (ty * ty)) {struct n} : option sub :=
    match n with
    | 0 => if forallb (fun p => ty_eqb (sapp θ (fst p)) (sapp θ (snd p))) eqs then Some θ else None
    | S n' =>
        let fix loop (eqs : list (ty * ty)) : option sub :=
          match eqs with
          | [] => Some θ
          | (a, b) :: eqs' =>
              match uni θ (sapp θ a) (sapp θ b) with
              | None => None
              | Some None => loop eqs'
              | Some (Some (θ', rest)) => unify_n n' θ' (rest ++ eqs')
              end
          end in
        loop eqs
    end.
End Unify.

(** ** Specification of one step *)

Section Spec.
  Variable nt : nat.

  (** [s] leaves the rigid variables alone. *)
  Definition rigid (s : nat -> ty) : Prop := forall i, meta nt i = false -> s i = TVar i.

  Definition eqs_by (s : nat -> ty) (eqs : list (ty * ty)) : Prop :=
    Forall (fun p => tsubst s (fst p) = tsubst s (snd p)) eqs.

  (** What a step [r] means, for a problem with variables [V] and
      solutions [P] (the substitutions making both sides equal). *)
  Definition uspec (θ : sub) (V : nat -> bool) (P : (nat -> ty) -> Prop) (r : r1) : Prop :=
    match r with
    | None => forall s, absorbs s θ -> rigid s -> ~ P s
    | Some None => forall s, P s
    | Some (Some (θ', rest)) =>
        (exists i t, θ' = bind i t θ /\ can_bind θ i t /\ meta nt i = true /\ V i = true /\
                     (forall k, occurs k t = true -> V k = true)) /\
        (forall p k, In p rest -> (occurs k (fst p) || occurs k (snd p))%bool = true -> V k = true) /\
        (forall s, absorbs s θ' -> eqs_by s rest -> P s) /\
        (forall s, absorbs s θ -> P s -> absorbs s θ' /\ eqs_by s rest)
    end.

  Lemma uspec_weaken θ V P V' P' r :
    (forall k, V k = true -> V' k = true) -> (forall s, P s <-> P' s) ->
    uspec θ V P r -> uspec θ V' P' r.
  Proof.
    intros HV HP; destruct r as [[[θ' rest]|]|]; simpl.
    - intros ((i & t & H1 & H2 & H3 & H4 & H5) & H6 & H7 & H8).
      split; [|split; [|split]].
      + exists i, t; split; [exact H1|split; [exact H2|split; [exact H3|split]]]; auto.
      + eauto.
      + intros s Ha Hr; apply HP; eauto.
      + intros s Ha Hp; apply H8; auto; apply HP; auto.
    - intros H s; apply HP; auto.
    - intros H s Ha Hr Hp; apply (H s Ha Hr); apply HP; auto.
  Qed.

  Lemma eqs_by_app s l1 l2 : eqs_by s (l1 ++ l2) <-> eqs_by s l1 /\ eqs_by s l2.
  Proof. unfold eqs_by; rewrite Forall_app; tauto. Qed.

  Lemma uspec_seq θ V1 P1 V2 P2 r pairs k :
    uspec θ V1 P1 r -> uspec θ V2 P2 k ->
    (forall p k0, In p pairs -> (occurs k0 (fst p) || occurs k0 (snd p))%bool = true -> V2 k0 = true) ->
    (forall s, P2 s <-> eqs_by s pairs) ->
    uspec θ (fun k0 => (V1 k0 || V2 k0)%bool) (fun s => P1 s /\ P2 s) (seqr r pairs k).
  Proof.
    intros H1 H2 Hp HP; destruct r as [[[θ' rest]|]|]; simpl in *.
    - destruct H1 as ((i & t & E1 & E2 & E3 & E4 & E5) & E6 & E7 & E8).
      split; [|split; [|split]].
      + exists i, t; split; [exact E1|split; [exact E2|split; [exact E3|split]]].
        * rewrite E4; reflexivity.
        * intros k0 Hk; rewrite (E5 k0 Hk); reflexivity.
      + intros p k0 Hin Hk; apply in_app_or in Hin as [Hin|Hin].
        * rewrite (E6 p k0 Hin Hk); reflexivity.
        * rewrite (Hp p k0 Hin Hk), orb_true_r; reflexivity.
      + intros s Ha He; apply eqs_by_app in He as [He1 He2]; split; [apply E7; auto|apply HP; auto].
      + intros s Ha [Hp1 Hp2]; split; [apply E8; auto|].
        apply eqs_by_app; split; [apply E8; auto|apply HP; auto].
    - eapply uspec_weaken; [| |exact H2].
      + intros k0 Hk; rewrite Hk, orb_true_r; reflexivity.
      + intros s; split; [intros; split; auto|tauto].
    - intros s Ha Hr [Hp1 _]; exact (H1 s Ha Hr Hp1).
  Qed.

  Definition tvars (a b : ty) (k : nat) : bool := (occurs k a || occurs k b)%bool.
  Definition teq (a b : ty) (s : nat -> ty) : Prop := tsubst s a = tsubst s b.

  Lemma map_fixed {A} (f : A -> A) xs : map f xs = xs -> Forall (fun x => f x = x) xs.
  Proof.
    induction xs as [|x xs IH]; simpl; intros H; constructor; injection H as H1 H2; auto.
  Qed.

  Lemma bindr_spec θ i b :
    sapp θ (TVar i) = TVar i -> sapp θ b = b -> meta nt i = true -> b <> TVar i ->
    uspec θ (tvars (TVar i) b) (teq (TVar i) b) (bindr θ i b).
  Proof.
    intros Hi Hb Hm Hne; change (look θ i = TVar i) in Hi; unfold bindr.
    destruct (occurs i b) eqn:Ho; simpl.
    - intros s _ _ H; unfold teq in H; simpl in H.
      pose proof (occurs_size s i b Ho) as Hs.
      destruct b; try (rewrite <- H in Hs; lia).
      simpl in Ho; apply Nat.eqb_eq in Ho; subst; contradiction.
    - assert (Hcb : can_bind θ i b) by (repeat split; auto).
      split; [|split; [|split]].
      + exists i, b; split; [reflexivity|split; [exact Hcb|split; [exact Hm|split]]].
        * unfold tvars; simpl; rewrite Nat.eqb_refl; reflexivity.
        * intros k Hk; unfold tvars; rewrite Hk, orb_true_r; reflexivity.
      + intros p k [].
      + intros s Ha _; unfold teq; simpl. rewrite <- (Ha i).
        rewrite look_bind by exact Hi. rewrite Hi; simpl; rewrite single_at; reflexivity.
      + intros s Ha Hp; split; [apply bind_general; auto|constructor].
  Qed.

  Lemma tvars_sym a b k : tvars a b k = tvars b a k.
  Proof. unfold tvars; apply orb_comm. Qed.

  Lemma teq_sym a b s : teq a b s <-> teq b a s.
  Proof. unfold teq; split; auto. Qed.
End Spec.

Section Step.
  Variable nt : nat.

  Lemma bindr_spec_sym θ j a :
    sapp θ (TVar j) = TVar j -> sapp θ a = a -> meta nt j = true -> a <> TVar j ->
    uspec nt θ (tvars a (TVar j)) (teq a (TVar j)) (bindr θ j a).
  Proof.
    intros H1 H2 H3 H4.
    apply (uspec_weaken nt θ (tvars (TVar j) a) (teq (TVar j) a)).
    - intros k Hk; rewrite tvars_sym; exact Hk.
    - intros s; apply teq_sym.
    - apply bindr_spec; auto.
  Qed.

  Definition lvars (xs ys : list ty) (k : nat) : bool := (existsb (occurs k) xs || existsb (occurs k) ys)%bool.
  Definition leq (xs ys : list ty) (s : nat -> ty) : Prop := map (tsubst s) xs = map (tsubst s) ys.

  Lemma combine_vars xs ys p k :
    In p (combine xs ys) -> (occurs k (fst p) || occurs k (snd p))%bool = true -> lvars xs ys k = true.
  Proof.
    intros Hin H; destruct p as [x y].
    pose proof (in_combine_l _ _ _ _ Hin); pose proof (in_combine_r _ _ _ _ Hin).
    unfold lvars; simpl in H; apply orb_true_iff in H as [H|H]; apply orb_true_iff; [left|right];
      apply existsb_occ; eauto.
  Qed.

  Lemma combine_eqs s xs ys : length xs = length ys -> (leq xs ys s <-> eqs_by s (combine xs ys)).
  Proof.
    revert ys; induction xs as [|x xs IH]; intros [|y ys] Hl; simpl in *; try discriminate.
    - split; intros; [constructor|reflexivity].
    - injection Hl as Hl; unfold leq, eqs_by in *; simpl. split.
      + intros H; injection H as H1 H2; constructor; auto; apply (IH ys Hl); exact H2.
      + intros H; inversion H; subst; f_equal; auto; apply (IH ys Hl); assumption.
  Qed.

  Lemma unis_spec θ xs :
    Forall (fun x => forall y, sapp θ x = x -> sapp θ y = y -> uspec nt θ (tvars x y) (teq x y) (uni nt θ x y)) xs ->
    Forall (fun x => sapp θ x = x) xs ->
    forall ys, Forall (fun y => sapp θ y = y) ys ->
    uspec nt θ (lvars xs ys) (leq xs ys) (unis nt θ xs ys).
  Proof.
    induction 1 as [|x xs Hx Hxs IH]; intros Hax [|y ys] Hys.
    - change (uspec nt θ (lvars [] []) (leq [] []) (Some None)); intros s; reflexivity.
    - change (uspec nt θ (lvars [] (y :: ys)) (leq [] (y :: ys)) None).
      intros s _ _ H; discriminate H.
    - change (uspec nt θ (lvars (x :: xs) []) (leq (x :: xs) []) None).
      intros s _ _ H; discriminate H.
    - inversion Hax as [|? ? Hx0 Hax']; subst; inversion Hys as [|? ? Hy Hys']; subst.
      change (uspec nt θ (lvars (x :: xs) (y :: ys)) (leq (x :: xs) (y :: ys))
                (if Nat.eqb (length xs) (length ys)
                 then seqr (uni nt θ x y) (combine xs ys) (unis nt θ xs ys) else None)).
      destruct (Nat.eqb (length xs) (length ys)) eqn:Hl.
      + apply Nat.eqb_eq in Hl.
        pose proof (uspec_seq nt θ (tvars x y) (teq x y) (lvars xs ys) (leq xs ys)
                      (uni nt θ x y) (combine xs ys) (unis nt θ xs ys)
                      (Hx y Hx0 Hy) (IH Hax' ys Hys') (combine_vars xs ys)
                      (fun s => combine_eqs s xs ys Hl)) as Hs.
        refine (uspec_weaken nt θ _ _ _ _ _ _ _ Hs).
        * intros k; unfold lvars, tvars; simpl; rewrite !orb_true_iff; tauto.
        * intros s; unfold leq, teq; simpl; split.
          -- intros [H1 H2]; f_equal; auto.
          -- intros H; injection H as H1 H2; auto.
      + intros s _ _ H; unfold leq in H; simpl in H; injection H as _ H.
        apply (f_equal (@length ty)) in H; rewrite !length_map in H.
        apply Nat.eqb_neq in Hl; contradiction.
  Qed.
End Step.

Section Main.
  Variable nt : nat.

  Lemma applied_sub θ t :
    sapp θ t = t ->
    match t with
    | TTuple ts | TData _ ts => Forall (fun x => sapp θ x = x) ts
    | TArrow ps r ε => Forall (fun x => sapp θ x = x) ps /\ sapp θ r = r /\ sapp θ ε = ε
    | TRef x | TArray _ x => sapp θ x = x
    | _ => True
    end.
  Proof.
    unfold sapp; destruct t; simpl; intros H; auto; injection H; intros; repeat split;
      try apply map_fixed; auto.
  Qed.

  Lemma uni_spec θ :
    forall a b, sapp θ a = a -> sapp θ b = b -> uspec nt θ (tvars a b) (teq a b) (uni nt θ a b).
  Proof.
    intros a; induction a as [x|i|xs IH|ps r ε IHps IHr IHε|T xs IH|x IH|k x IH|] using ty_ind';
      intros b Ha Hb; pose proof (applied_sub θ _ Ha) as Ha';
      destruct b as [y|j|ys|ps' r' ε'|U ys|y|k' y|]; pose proof (applied_sub θ _ Hb) as Hb';
      simpl in Ha', Hb';
      (* constructor clashes *)
      try solve [cbn [uni uspec]; intros s _ _ H; unfold teq in H; simpl in H; discriminate H];
      (* a metavariable or a rigid variable against a constructor *)
      try solve [cbn [uni]; destruct (meta nt i) eqn:Hm;
                 [apply bindr_spec; auto; discriminate
                 |cbn [uspec]; intros s _ Hr H; unfold teq in H; simpl in H;
                  rewrite (Hr i Hm) in H; discriminate H]];
      try solve [cbn [uni]; destruct (meta nt j) eqn:Hm;
                 [apply bindr_spec_sym; auto; discriminate
                 |cbn [uspec]; intros s _ Hr H; unfold teq in H; simpl in H;
                  rewrite (Hr j Hm) in H; discriminate H]].
    - (* TBase *)
      cbn [uni]; destruct (base_ty_eq_dec x y) as [<-|Hne]; cbn [uspec].
      + intros s; reflexivity.
      + intros s _ _ H; unfold teq in H; simpl in H; injection H; auto.
    - (* TVar, TVar *)
      cbn [uni]; destruct (Nat.eqb i j) eqn:E.
      + apply Nat.eqb_eq in E; subst; cbn [uspec]; intros s; reflexivity.
      + apply Nat.eqb_neq in E. destruct (meta nt i) eqn:Hi.
        * apply bindr_spec; auto; congruence.
        * destruct (meta nt j) eqn:Hj.
          -- apply bindr_spec_sym; auto; congruence.
          -- cbn [uspec]; intros s _ Hr H; unfold teq in H; simpl in H.
             rewrite (Hr i Hi), (Hr j Hj) in H; congruence.
    - (* TTuple *)
      rewrite uni_tuple.
      refine (uspec_weaken nt θ _ _ _ _ _ _ _ (unis_spec nt θ xs IH Ha' ys Hb')).
      + intros k0 H0; exact H0.
      + intros s; unfold leq, teq; simpl; split; [intros ->; reflexivity|intros H; injection H; auto].
    - (* TArrow *)
      rewrite uni_arrow; destruct Ha' as (Hps & Hr & Hε); destruct Hb' as (Hps' & Hr' & Hε').
      pose proof (uspec_seq nt θ (tvars r r') (teq r r') (tvars ε ε') (teq ε ε')
                    (uni nt θ r r') [(ε, ε')] (uni nt θ ε ε') (IHr r' Hr Hr') (IHε ε' Hε Hε')) as H2.
      assert (H2' : uspec nt θ (fun k0 => (tvars r r' k0 || tvars ε ε' k0)%bool)
                      (fun s => teq r r' s /\ teq ε ε' s)
                      (seqr (uni nt θ r r') [(ε, ε')] (uni nt θ ε ε'))).
      { apply H2.
        - intros p k0 [<-|[]] Hk; exact Hk.
        - intros s; unfold eqs_by; split.
          + intros H; constructor; auto.
          + intros H; inversion H; auto. }
      pose proof (uspec_seq nt θ (lvars ps ps') (leq ps ps') _ _
                    (unis nt θ ps ps') [(r, r'); (ε, ε')] _ (unis_spec nt θ ps IHps Hps ps' Hps') H2')
        as H1.
      assert (H1' : uspec nt θ (fun k0 => (lvars ps ps' k0 || (tvars r r' k0 || tvars ε ε' k0))%bool)
                      (fun s => leq ps ps' s /\ (teq r r' s /\ teq ε ε' s))
                      (seqr (unis nt θ ps ps') [(r, r'); (ε, ε')]
                            (seqr (uni nt θ r r') [(ε, ε')] (uni nt θ ε ε')))).
      { apply H1.
        - intros p k0 [<-|[<-|[]]] Hk; unfold tvars; simpl in Hk |- *; rewrite Hk;
            rewrite ?orb_true_r; reflexivity.
        - intros s; unfold eqs_by; split.
          + intros [H3 H4]; constructor; auto.
          + intros H; inversion H as [|? ? H3 H4]; subst; inversion H4; auto. }
      refine (uspec_weaken nt θ _ _ _ _ _ _ _ H1').
      + intros k0; unfold lvars, tvars; simpl; rewrite !orb_true_iff; tauto.
      + intros s; unfold leq, teq; simpl; split.
        * intros (H3 & H4 & H5); rewrite H3, H4, H5; reflexivity.
        * intros H; injection H; auto.
    - (* TData *)
      rewrite uni_data; destruct (eq_dec T U) as [<-|Hne].
      + refine (uspec_weaken nt θ _ _ _ _ _ _ _ (unis_spec nt θ xs IH Ha' ys Hb')).
        * intros k0 H0; exact H0.
        * intros s; unfold leq, teq; simpl; split; [intros ->; reflexivity|intros H; injection H; auto].
      + cbn [uspec]; intros s _ _ H; unfold teq in H; simpl in H; injection H; auto.
    - (* TRef *)
      cbn [uni]; refine (uspec_weaken nt θ _ _ _ _ _ _ _ (IH y Ha' Hb')).
      + intros k0 H0; exact H0.
      + intros s; unfold teq; simpl; split; [intros ->; reflexivity|intros H; injection H; auto].
    - (* TArray *)
      cbn [uni]; destruct (array_kind_eq_dec k k') as [<-|Hne].
      + refine (uspec_weaken nt θ _ _ _ _ _ _ _ (IH y Ha' Hb')).
        * intros k0 H0; exact H0.
        * intros s; unfold teq; simpl; split; [intros ->; reflexivity|intros H; injection H; auto].
      + cbn [uspec]; intros s _ _ H; unfold teq in H; simpl in H; injection H; auto.
    - (* TError *)
      cbn [uni uspec]; intros s; reflexivity.
  Qed.
End Main.

(** ** Soundness and generality *)

Section Outer.
  Variable nt : nat.

  Theorem unify_n_sound : forall n θ eqs θ',
    idem θ -> unify_n nt n θ eqs = Some θ' ->
    idem θ' /\ absorbs (look θ') θ /\ eqs_by (look θ') eqs /\
    (forall s, absorbs s θ -> eqs_by s eqs -> absorbs s θ').
  Proof.
    induction n as [|n IHn]; intros θ eqs θ' Hid H.
    - simpl in H. destruct (forallb _ eqs) eqn:Hf; [|discriminate]. injection H as <-.
      split; [exact Hid|split; [apply idem_absorbs; exact Hid|split]].
      + unfold eqs_by; rewrite Forall_forall; intros [a b] Hin.
        rewrite forallb_forall in Hf; specialize (Hf _ Hin); apply ty_eqb_eq in Hf; exact Hf.
      + intros s Ha _; exact Ha.
    - revert θ' H; induction eqs as [|[a b] eqs IHe]; intros θ' H.
      + simpl in H; injection H as <-.
        split; [exact Hid|split; [apply idem_absorbs; exact Hid|split; [constructor|]]].
        intros s Ha _; exact Ha.
      + cbn [unify_n] in H.
        pose proof (uni_spec nt θ (sapp θ a) (sapp θ b) (sapp_idem θ a Hid) (sapp_idem θ b Hid)) as Hu.
        destruct (uni nt θ (sapp θ a) (sapp θ b)) as [[[θ1 rest]|]|] eqn:Eu; [| |discriminate].
        * destruct Hu as ((i & t & -> & Hcb & _ & _ & _) & _ & Hs & Hg).
          pose proof (bind_idem θ i t Hid Hcb) as Hid1.
          destruct (IHn _ _ _ Hid1 H) as (Hid' & Habs1 & Heq & Hgen).
          pose proof (absorbs_trans _ _ _ Habs1 (bind_absorbs θ i t Hid Hcb)) as Habs.
          apply eqs_by_app in Heq as [Hrest Heqs].
          split; [exact Hid'|split; [exact Habs|split]].
          -- constructor; [|exact Heqs].
             specialize (Hs _ Habs1 Hrest); unfold teq in Hs; simpl.
             rewrite <- (absorbs_sapp _ θ a Habs), <- (absorbs_sapp _ θ b Habs); exact Hs.
          -- intros s Ha He; inversion He as [|? ? Hab He']; subst; simpl in Hab.
             assert (Ht : teq (sapp θ a) (sapp θ b) s)
               by (unfold teq; rewrite !(absorbs_sapp _ θ _ Ha); exact Hab).
             destruct (Hg s Ha Ht) as [Ha1 Hr].
             apply Hgen; [exact Ha1|apply eqs_by_app; auto].
        * specialize (IHe θ' H) as (Hid' & Habs & Heqs & Hgen).
          split; [exact Hid'|split; [exact Habs|split]].
          -- constructor; [|exact Heqs].
             specialize (Hu (look θ')); unfold teq in Hu; simpl.
             rewrite <- (absorbs_sapp _ θ a Habs), <- (absorbs_sapp _ θ b Habs); exact Hu.
          -- intros s Ha He; inversion He; subst; apply Hgen; auto.
  Qed.

  (** ** Completeness *)

  Definition vlt (N : nat) (t : ty) : Prop := forall k, occurs k t = true -> k < N.
  Definition bounded (N : nat) (θ : sub) : Prop := forall j, j < N -> vlt N (look θ j).
  Definition unbound (θ : sub) (j : nat) : bool := ty_eqb (look θ j) (TVar j).

  (** The unsolved metavariables below [N]. *)
  Definition free_count (N : nat) (θ : sub) : nat := length (filter (unbound θ) (seq nt (N - nt))).

  Lemma vlt_sapp N θ t : bounded N θ -> vlt N t -> vlt N (sapp θ t).
  Proof.
    intros Hb Ht k Hk; apply occurs_tsubst in Hk as (j & Hj & Hk).
    exact (Hb j (Ht j Hj) k Hk).
  Qed.

  Lemma filter_drop {A} (f g : A -> bool) (l : list A) (x : A) :
    NoDup l -> In x l -> f x = true -> g x = false ->
    (forall y, y <> x -> In y l -> g y = f y) -> S (length (filter g l)) = length (filter f l).
  Proof.
    revert x; induction l as [|y l IH]; intros x Hnd Hin Hf Hg Hy; [contradiction|].
    inversion Hnd as [|? ? Hy' Hnd']; subst. simpl.
    destruct Hin as [<-|Hin].
    - rewrite Hf, Hg. f_equal.
      assert (Heq : filter g l = filter f l).
      { apply filter_ext_in; intros z Hz; apply Hy; [intros ->; contradiction|right; exact Hz]. }
      rewrite Heq; reflexivity.
    - assert (Hne : y <> x) by (intros ->; contradiction).
      rewrite (Hy y Hne (or_introl eq_refl)).
      destruct (f y); simpl; [f_equal|]; apply (IH x); auto; intros w Hw Hin'; apply Hy; simpl; auto.
  Qed.

  Lemma unbound_bind_ne θ i t j :
    can_bind θ i t -> j <> i -> unbound (bind i t θ) j = unbound θ j.
  Proof.
    intros (Hi & Ht & Ho) Hj; unfold unbound.
    apply Bool.eq_iff_eq_true; rewrite !ty_eqb_eq. rewrite look_bind by exact Hi.
    split.
    - destruct (look θ j) as [| m | | | | | |] eqn:E; simpl; try discriminate.
      unfold single; destruct (Nat.eqb m i) eqn:Em; intros H.
      + subst t. apply Nat.eqb_eq in Em; subst m.
        pose proof (fixed_occ _ j _ Ht) as Hf; simpl in Hf. rewrite Nat.eqb_refl in Hf.
        specialize (Hf eq_refl); rewrite E in Hf; exact Hf.
      + exact H.
    - intros ->; simpl; apply single_ne; exact Hj.
  Qed.

  Lemma free_count_bind N θ i t :
    can_bind θ i t -> nt <= i -> i < N -> S (free_count N (bind i t θ)) = free_count N θ.
  Proof.
    intros Hcb Hnt HN; unfold free_count.
    apply (filter_drop _ _ _ i); [apply seq_NoDup|apply in_seq; lia| | |].
    - destruct Hcb as (Hi & _ & _); unfold unbound; rewrite Hi; apply ty_eqb_eq; reflexivity.
    - destruct Hcb as (Hi & Ht & Ho); unfold unbound.
      rewrite look_bind by exact Hi; rewrite Hi; simpl; rewrite single_at.
      destruct (ty_eqb t (TVar i)) eqn:E; auto.
      apply ty_eqb_eq in E; subst; simpl in Ho; rewrite Nat.eqb_refl in Ho; discriminate.
    - intros y Hy _; apply unbound_bind_ne; auto.
  Qed.

  Lemma free_count_le N θ : free_count N θ <= N - nt.
  Proof. unfold free_count; rewrite <- (length_seq (N - nt) nt) at 2; apply filter_length_le. Qed.

  Lemma no_free N θ k : free_count N θ = 0 -> nt <= k -> k < N -> unbound θ k = false.
  Proof.
    unfold free_count; intros H Hk HN; apply length_zero_iff_nil in H.
    destruct (unbound θ k) eqn:E; auto.
    assert (Hin : In k (filter (unbound θ) (seq nt (N - nt))))
      by (apply filter_In; split; auto; apply in_seq; lia).
    rewrite H in Hin; contradiction.
  Qed.

  Theorem unify_n_complete N : forall n θ eqs s,
    idem θ -> bounded N θ -> Forall (fun p => vlt N (fst p) /\ vlt N (snd p)) eqs ->
    absorbs s θ -> rigid nt s -> eqs_by s eqs -> free_count N θ <= n ->
    exists θ', unify_n nt n θ eqs = Some θ'.
  Proof.
    induction n as [|n IHn]; intros θ eqs s Hid Hb Hv Ha Hr He Hn.
    - exists θ; simpl. replace (forallb _ eqs) with true; [reflexivity|symmetry].
      apply forallb_forall; intros [a b] Hin. apply ty_eqb_eq.
      unfold eqs_by in He; rewrite Forall_forall in Hv, He; destruct (Hv _ Hin) as [Hva Hvb]; specialize (He _ Hin); simpl in *.
      assert (Hfix : forall x, vlt N x -> tsubst s (sapp θ x) = sapp θ x).
      { intros x Hx. rewrite <- (tsubst_var (sapp θ x)) at 2. apply tsubst_ext_occ; intros k Hk.
        pose proof (fixed_occ _ _ _ (sapp_idem θ x Hid) Hk) as Hu.
        pose proof (vlt_sapp N θ x Hb Hx k Hk) as HkN.
        destruct (meta nt k) eqn:Hm.
        - unfold meta in Hm; apply Nat.leb_le in Hm.
          assert (Hz : free_count N θ = 0) by lia.
          pose proof (no_free N θ k Hz Hm HkN) as Hnf; unfold unbound in Hnf.
          rewrite Hu in Hnf; simpl in Hnf; rewrite Nat.eqb_refl in Hnf; discriminate.
        - apply Hr; exact Hm. }
      rewrite <- (Hfix a Hva), <- (Hfix b Hvb), !(absorbs_sapp _ θ _ Ha); exact He.
    - induction eqs as [|[a b] eqs IHe].
      + exists θ; reflexivity.
      + inversion Hv as [|? ? [Hva Hvb] Hv']; subst. inversion He as [|? ? Hab He']; subst.
        simpl in Hab.
        assert (Ht : teq (sapp θ a) (sapp θ b) s)
          by (unfold teq; rewrite !(absorbs_sapp _ θ _ Ha); exact Hab).
        pose proof (uni_spec nt θ (sapp θ a) (sapp θ b) (sapp_idem θ a Hid) (sapp_idem θ b Hid)) as Hu.
        cbn [unify_n].
        destruct (uni nt θ (sapp θ a) (sapp θ b)) as [[[θ1 rest]|]|] eqn:Eu.
        * destruct Hu as ((i & t & -> & Hcb & Hm & Hvi & Hvt) & Hvr & _ & Hg).
          destruct (Hg s Ha Ht) as [Ha1 Hrest].
          pose proof (vlt_sapp N θ a Hb Hva) as Hva'; pose proof (vlt_sapp N θ b Hb Hvb) as Hvb'.
          assert (HV : forall k, tvars (sapp θ a) (sapp θ b) k = true -> k < N).
          { intros k Hk; unfold tvars in Hk; apply orb_true_iff in Hk as [Hk|Hk]; auto. }
          apply (IHn _ _ s); auto.
          -- apply bind_idem; auto.
          -- intros j Hj k Hk. destruct Hcb as (Hi & Hti & Hoi).
             rewrite look_bind in Hk by exact Hi.
             apply occurs_tsubst in Hk as (m & Hm' & Hk).
             unfold single in Hk; destruct (Nat.eqb m i).
             ++ exact (HV k (Hvt k Hk)).
             ++ simpl in Hk; apply Nat.eqb_eq in Hk; subst; exact (Hb j Hj m Hm').
          -- apply Forall_app; split; auto.
             rewrite Forall_forall; intros p Hp; split; intros k Hk; apply HV; apply (Hvr p k Hp);
               rewrite Hk; [reflexivity|apply orb_true_r].
          -- apply eqs_by_app; auto.
          -- unfold meta in Hm; apply Nat.leb_le in Hm.
             pose proof (free_count_bind N θ i t Hcb Hm (HV i Hvi)); lia.
        * destruct (IHe Hv' He') as [θ' H']. exists θ'; exact H'.
        * exfalso; exact (Hu s Ha Hr Ht).
  Qed.
End Outer.

(** ** Interface

    [unify nt N θ a b]: unify [a] and [b] under [θ], where the variables
    below [nt] are rigid and the metavariables are below [N] (the fuel is
    the number of metavariables).  Most generality is stated as
    absorption: every unifier [s] extending [θ] is [s] after the result. *)

Definition unify (nt N : nat) (θ : sub) (a b : ty) : option sub := unify_n nt (N - nt) θ [(a, b)].

Lemma idem_nil : idem [].
Proof. intros j; reflexivity. Qed.

Lemma bounded_nil N : bounded N [].
Proof. intros j Hj k Hk; simpl in Hk; apply Nat.eqb_eq in Hk; subst; exact Hj. Qed.

Theorem unify_sound nt N θ a b θ' :
  idem θ -> unify nt N θ a b = Some θ' ->
  idem θ' /\ absorbs (look θ') θ /\ sapp θ' a = sapp θ' b.
Proof.
  intros Hid H; destruct (unify_n_sound nt _ _ _ _ Hid H) as (H1 & H2 & H3 & _).
  split; [exact H1|split; [exact H2|]]. inversion H3; auto.
Qed.

Theorem unify_mgu nt N θ a b θ' s :
  idem θ -> unify nt N θ a b = Some θ' ->
  absorbs s θ -> tsubst s a = tsubst s b -> absorbs s θ'.
Proof.
  intros Hid H Ha Hab; destruct (unify_n_sound nt _ _ _ _ Hid H) as (_ & _ & _ & Hg).
  apply Hg; [exact Ha|constructor; [exact Hab|constructor]].
Qed.

Theorem unify_complete nt N θ a b s :
  idem θ -> bounded N θ -> vlt N a -> vlt N b ->
  absorbs s θ -> rigid nt s -> tsubst s a = tsubst s b ->
  exists θ', unify nt N θ a b = Some θ'.
Proof.
  intros Hid Hb Ha Hbv Hs Hr Hab.
  apply (unify_n_complete nt N _ _ _ s Hid Hb).
  - constructor; [split; auto|constructor].
  - exact Hs.
  - exact Hr.
  - constructor; [exact Hab|constructor].
  - apply free_count_le.
Qed.
