(** * Core IR: main results (milestone M1)

    One place that states the guarantees of the Core layer:

    1. [check_program] is the certified checker for a whole program
       (global environment + entry expression).  Its successful results
       carry proofs, so it is sound by construction.
    2. [check_program_complete]: it accepts every well-typed program.
    3. [program_ok_dec]: well-typedness of programs is decidable.
    4. [checked_program_safe]: an accepted program never gets stuck under
       the small-step semantics, and a normal result has the program's type. *)

From Stdlib Require Import List.
From MoonRocq.Prelude Require Import Result.
From MoonRocq.Core Require Import Syntax Typing Check CheckComplete Semantics Soundness.
Import ListNotations.

Definition program_ok (ge : genv) (e : expr) (τ : ty) : Prop :=
  genv_ok ge /\ has_type ge [] e τ.

Definition check_program (ge : genv) (e : expr) :
    result {τ | program_ok ge e τ} type_error :=
  Hg <- check_genv ge ;;
  '(exist _ τ He) <- infer ge [] e ;;
  Ok (exist _ τ (conj Hg He)).

Theorem check_program_complete ge e τ :
  program_ok ge e τ -> exists H, check_program ge e = Ok (exist _ τ H).
Proof.
  intros [Hg He]; unfold check_program.
  destruct (check_genv_complete ge Hg) as [pg Eg]; rewrite Eg; cbn [bind].
  destruct (infer_complete ge [] e τ He) as [pe Ee]; rewrite Ee; cbn [bind].
  eauto.
Qed.

Definition program_ok_dec ge e τ : {program_ok ge e τ} + {~ program_ok ge e τ}.
Proof.
  destruct (genv_ok_dec ge) as [Hg|Hg]; [|right; intros [H _]; contradiction].
  destruct (has_type_dec ge [] e τ) as [He|He]; [left; split; assumption|].
  right; intros [_ H]; contradiction.
Defined.

Theorem checked_program_safe ge e τ H :
  check_program ge e = Ok (exist _ τ H) ->
  (forall s, star ge (SEval [] e) s -> ~ stuck ge s) /\
  (forall v, star ge (SEval [] e) (SRet [] v) -> value v /\ has_type ge [] v τ).
Proof.
  intros _. destruct H as [Hg He]. split.
  - intros s; apply soundness with (τ := τ); assumption.
  - intros v; apply soundness_value; assumption.
Qed.
