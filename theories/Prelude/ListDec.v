(** * Computable decision procedures on lists

    Stdlib's [ListDec.NoDup_dec] is opaque, so it neither reduces inside
    Rocq nor yields useful extracted code.  These versions are boolean
    functions with [Prop] specifications, packaged as transparent
    decisions. *)

From Stdlib Require Import List Bool.
From MoonRocq.Prelude Require Import EqDec.
Import ListNotations.

Section ListDec.
  Context {A : Type} `{EqDec A}.

  Definition memb (x : A) (l : list A) : bool := existsb (eqb x) l.

  Lemma memb_In x l : memb x l = true <-> In x l.
  Proof.
    unfold memb; rewrite existsb_exists; split.
    - intros (y & Hy & E). apply (proj1 (eqb_eq x y)) in E. rewrite E; exact Hy.
    - intros Hx; exists x; split; [exact Hx | apply eqb_refl].
  Qed.

  Fixpoint nodupb (l : list A) : bool :=
    match l with
    | [] => true
    | x :: l' => (negb (memb x l') && nodupb l')%bool
    end.

  Lemma nodupb_NoDup l : nodupb l = true <-> NoDup l.
  Proof.
    induction l as [|x l IH]; simpl.
    - split; constructor.
    - rewrite andb_true_iff, negb_true_iff, IH. split.
      + intros [Hm Hn]. constructor; auto.
        intros Hin; apply memb_In in Hin; congruence.
      + intros Hn; inversion Hn as [|? ? Hnin Hn']; subst; split; auto.
        destruct (memb x l) eqn:E; auto. apply memb_In in E; contradiction.
  Qed.

  Definition NoDup_dec (l : list A) : {NoDup l} + {~ NoDup l}.
  Proof.
    destruct (nodupb l) eqn:E.
    - left; now apply nodupb_NoDup.
    - right; intros Hn; apply nodupb_NoDup in Hn; congruence.
  Defined.
End ListDec.
