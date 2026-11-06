(** * Result monad

    All executable checkers in MoonRocq return [result A E] rather than
    [option A], so that the extracted tool can report *why* a program is
    rejected.  The error payload never influences soundness theorems: those
    are stated about the [Ok] case only.

    Kept deliberately free of dependent types so that extraction produces a
    plain OCaml variant. *)

From Stdlib Require Import List.
Import ListNotations.

Inductive result (A E : Type) : Type :=
| Ok  : A -> result A E
| Err : E -> result A E.

Arguments Ok  {A E} _.
Arguments Err {A E} _.

Definition ret {A E} (a : A) : result A E := Ok a.

Definition bind {A B E} (m : result A E) (k : A -> result B E) : result B E :=
  match m with
  | Ok a => k a
  | Err e => Err e
  end.

Definition map_result {A B E} (f : A -> B) (m : result A E) : result B E :=
  match m with
  | Ok a => Ok (f a)
  | Err e => Err e
  end.

Definition map_err {A E E'} (f : E -> E') (m : result A E) : result A E' :=
  match m with
  | Ok a => Ok a
  | Err e => Err (f e)
  end.

(** Fail unless the boolean holds. *)
Definition guard {E} (b : bool) (e : E) : result unit E :=
  if b then Ok tt else Err e.

Declare Scope result_scope.
Delimit Scope result_scope with result.

Notation "x <- m ;; k" := (bind m (fun x => k))
  (at level 61, m at next level, right associativity) : result_scope.
Notation "' p <- m ;; k" := (bind m (fun x => match x with p => k end))
  (at level 61, p pattern, m at next level, right associativity) : result_scope.
Notation "m ;;; k" := (bind m (fun _ => k))
  (at level 61, right associativity) : result_scope.

Open Scope result_scope.

(** Monadic traversal of a list. *)
Fixpoint mapM {A B E} (f : A -> result B E) (xs : list A) : result (list B) E :=
  match xs with
  | [] => Ok []
  | x :: xs' => y <- f x ;; ys <- mapM f xs' ;; Ok (y :: ys)
  end.

(** ** Reasoning principles *)

Lemma bind_ok_inv {A B E} (m : result A E) (k : A -> result B E) b :
  bind m k = Ok b -> exists a, m = Ok a /\ k a = Ok b.
Proof. destruct m; simpl; [eauto | discriminate]. Qed.

Lemma guard_ok_inv {E} b (e : E) : guard b e = Ok tt -> b = true.
Proof. destruct b; simpl; congruence. Qed.

Lemma mapM_ok_inv {A B E} (f : A -> result B E) xs ys :
  mapM f xs = Ok ys -> Forall2 (fun x y => f x = Ok y) xs ys.
Proof.
  revert ys; induction xs as [|x xs IH]; simpl; intros ys H.
  - inversion H; constructor.
  - apply bind_ok_inv in H as (y & Hy & H).
    apply bind_ok_inv in H as (ys' & Hys & H).
    inversion H; subst; constructor; auto.
Qed.

(** Tactic: decompose hypotheses of the form [bind m k = Ok _]. *)
Ltac inv_bind :=
  repeat match goal with
  | H : bind _ _ = Ok _ |- _ =>
      let a := fresh "a" in let Ha := fresh "Ha" in
      apply bind_ok_inv in H as (a & Ha & H)
  | H : guard _ _ = Ok tt |- _ => apply guard_ok_inv in H
  | H : Ok _ = Ok _ |- _ => inversion H; subst; clear H
  end.
