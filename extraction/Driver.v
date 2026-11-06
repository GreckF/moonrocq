(** * Driver: from MoonBit source text to a certified verdict

    This file is the only place where MoonRocq meets the outside world.  It
    is not part of the [MoonRocq] library (which depends on Stdlib only):
    it lives next to the MoonBit project in [mbt/] and is compiled with the
    rocq2mbt plugin.

    The pipeline is
    {v
      source ──parse_string──▶ @syntax AST ──lower──▶ sprog ──elab_prog──▶ Core
             (MoonBit parser)            (MoonBit glue)       (Rocq)
                                                   ──check_program──▶ verdict
                                                         (Rocq, certified)
    v}
    - [parse_string] is the official MoonBit parser, imported through the
      axioms that [mbti2rocq] generated from its interface ([Parser.v]);
    - [lower] is hand-written MoonBit glue ([mbt/checker/lower.mbt]): a
      purely syntactic projection of the parser AST onto [sprog], rejecting
      what the Surface layer does not cover yet;
    - [elab_prog] and [check_program] are ordinary Rocq definitions.

    Neither axiom is trusted: [check_source_sound] below holds whatever the
    parser and the glue do, because an [O_Ok] verdict carries the Core
    typing proof of the program it reports. *)

From RocqMbt Require Import Prelude.
From MoonRocqExtr Require Import Parser.
From Stdlib Require Import List.
From Corelib Require Import PrimInt63.
From MoonRocq.Prelude Require Import Result.
From MoonRocq.Core Require Import Syntax Typing Check Semantics Soundness Theorems.
From MoonRocq.Surface Require Import Syntax Elab.
Import ListNotations.

(** ** The glue (implemented in MoonBit) *)

Inductive lower_error : Type :=
| LowerUnsupported (what : Prelude.String) (p : pos).

Axiom lower : list_List syntax_Impl -> result sprog lower_error.
Extract MoonBit Function lower => "lower_impls($0)".

(** ** Verdicts *)

Inductive outcome : Type :=
| O_Parse       (reports : Array basic_Report)
| O_Unsupported (e : lower_error)
| O_Elab        (e : elab_error)
| O_Type        (e : type_error)
| O_Ok          (ge : genv) (main : expr) (τ : ty) (H : program_ok ge main τ).

Definition check_core (ge : genv) (main : expr) : outcome :=
  match check_program ge main with
  | Ok (exist _ τ H) => O_Ok ge main τ H
  | Err e => O_Type e
  end.

Definition check_sprog (sp : sprog) : outcome :=
  match elab_prog sp with
  | Ok (ge, main) => check_core ge main
  | Err e => O_Elab e
  end.

Definition check_source (src : Prelude.String) : outcome :=
  let (impls, reports) := parse_string src in
  if Int_eqb (Array_length reports) (Int_of_uint63 0%uint63) then
    match lower impls with
    | Ok sp => check_sprog sp
    | Err e => O_Unsupported e
    end
  else O_Parse reports.

(** ** Guarantee

    An accepted program is well typed in Core, never gets stuck, and its
    normal result has the reported type.  This depends on no property of
    the parser or of the glue. *)
Theorem check_source_sound src ge main τ H :
  check_source src = O_Ok ge main τ H ->
  program_ok ge main τ /\
  (forall s, ⟨[] ∣ [] ▷ main⟩ ⟶*[ge] s -> ~ stuck ge s) /\
  (forall σ v, ⟨[] ∣ [] ▷ main⟩ ⟶*[ge] ⟨σ ∣ [] ◁ v⟩ ->
     value v /\ exists Σ, store_typed ge Σ σ /\ [] ⊢[ge;Σ;cc0] v : τ).
Proof.
  intros _. split; [exact H|].
  destruct H as [Hg Hm]. split.
  - intros s; apply soundness with (τ := τ); assumption.
  - intros σ v; apply soundness_value; assumption.
Qed.

(** ** Extraction *)

Extraction "../mbt/checker/moonrocq.mbt" check_source check_sprog.
