(** * Decidable equality

    A boolean equality together with a *propositional* specification.  The
    specification lives in [Prop] so that extraction erases it: the extracted
    code of an [EqDec] instance is just the boolean function. *)

From Stdlib Require Import Bool String List ZArith.

Class EqDec (A : Type) := {
  eqb : A -> A -> bool;
  eqb_eq : forall x y, eqb x y = true <-> x = y
}.

Arguments eqb {A _} _ _.

Infix "==?" := eqb (at level 70, no associativity).

Section Facts.
  Context {A : Type} `{EqDec A}.

  Lemma eqb_refl (x : A) : eqb x x = true.
  Proof. apply eqb_eq; reflexivity. Qed.

  Lemma eqb_neq (x y : A) : eqb x y = false <-> x <> y.
  Proof.
    split.
    - intros Hf Heq. apply eqb_eq in Heq. congruence.
    - intros Hne. destruct (eqb x y) eqn:E; auto.
      apply eqb_eq in E. contradiction.
  Qed.

  Lemma eqb_spec (x y : A) : reflect (x = y) (eqb x y).
  Proof.
    destruct (eqb x y) eqn:E; constructor.
    - now apply eqb_eq.
    - now apply eqb_neq.
  Qed.

  (** Computational decision procedure derived from [eqb]. *)
  Definition eq_dec (x y : A) : {x = y} + {x <> y}.
  Proof.
    destruct (eqb x y) eqn:E; [left; now apply eqb_eq | right; now apply eqb_neq].
  Defined.
End Facts.

(** Build an instance from a [sumbool] decision procedure (handy for
    enumerations, where [decide equality] does all the work). *)
Definition eqb_of_dec {A} (dec : forall x y : A, {x = y} + {x <> y}) (x y : A) : bool :=
  if dec x y then true else false.

Lemma eqb_of_dec_eq {A} (dec : forall x y : A, {x = y} + {x <> y}) x y :
  eqb_of_dec dec x y = true <-> x = y.
Proof. unfold eqb_of_dec; destruct (dec x y); split; congruence. Qed.

Definition EqDec_of_dec {A} (dec : forall x y : A, {x = y} + {x <> y}) : EqDec A :=
  {| eqb := eqb_of_dec dec; eqb_eq := eqb_of_dec_eq dec |}.

(** ** Instances for the base types used throughout the development *)

#[export] Instance EqDec_bool : EqDec bool :=
  { eqb := Bool.eqb; eqb_eq := fun x y => conj (proj1 (Bool.eqb_true_iff x y)) (proj2 (Bool.eqb_true_iff x y)) }.

#[export] Instance EqDec_nat : EqDec nat := { eqb := Nat.eqb; eqb_eq := Nat.eqb_eq }.

#[export] Instance EqDec_Z : EqDec Z := { eqb := Z.eqb; eqb_eq := Z.eqb_eq }.

#[export] Instance EqDec_N : EqDec N := { eqb := N.eqb; eqb_eq := N.eqb_eq }.

#[export] Instance EqDec_positive : EqDec positive := { eqb := Pos.eqb; eqb_eq := Pos.eqb_eq }.

#[export] Instance EqDec_string : EqDec string := { eqb := String.eqb; eqb_eq := String.eqb_eq }.

Definition prod_eqb {A B} `{EqDec A} `{EqDec B} (p q : A * B) : bool :=
  (eqb (fst p) (fst q) && eqb (snd p) (snd q))%bool.

Lemma prod_eqb_eq {A B} `{EqDec A} `{EqDec B} (x y : A * B) :
  prod_eqb x y = true <-> x = y.
Proof.
  destruct x as [a b], y as [c d]; unfold prod_eqb; simpl.
  rewrite andb_true_iff, !eqb_eq. split.
  - intros [-> ->]; reflexivity.
  - intros E; inversion E; auto.
Qed.

#[export] Instance EqDec_prod {A B} `{EqDec A} `{EqDec B} : EqDec (A * B) :=
  { eqb := prod_eqb; eqb_eq := prod_eqb_eq }.

Fixpoint list_eqb {A} `{EqDec A} (xs ys : list A) : bool :=
  match xs, ys with
  | nil, nil => true
  | cons x xs', cons y ys' => (eqb x y && list_eqb xs' ys')%bool
  | _, _ => false
  end.

Lemma list_eqb_eq {A} `{EqDec A} (x y : list A) : list_eqb x y = true <-> x = y.
Proof.
  revert y; induction x as [|a xs IH]; intros [|b ys]; simpl.
  - split; reflexivity.
  - split; discriminate.
  - split; discriminate.
  - rewrite andb_true_iff, eqb_eq, IH. split.
    + intros [-> ->]; reflexivity.
    + intros E; inversion E; auto.
Qed.

#[export] Instance EqDec_list {A} `{EqDec A} : EqDec (list A) :=
  { eqb := list_eqb; eqb_eq := list_eqb_eq }.

Definition option_eqb {A} `{EqDec A} (x y : option A) : bool :=
  match x, y with
  | None, None => true
  | Some a, Some b => eqb a b
  | _, _ => false
  end.

Lemma option_eqb_eq {A} `{EqDec A} (x y : option A) : option_eqb x y = true <-> x = y.
Proof.
  destruct x as [a|], y as [b|]; simpl.
  - rewrite eqb_eq. split; [intros ->; reflexivity | intros E; inversion E; auto].
  - split; discriminate.
  - split; discriminate.
  - split; reflexivity.
Qed.

#[export] Instance EqDec_option {A} `{EqDec A} : EqDec (option A) :=
  { eqb := option_eqb; eqb_eq := option_eqb_eq }.
