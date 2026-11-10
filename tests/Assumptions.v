(* Axiom audit for the main results.  Each line must print
   "Closed under the global context". *)
From MoonRocq.Core Require Import Soundness CheckComplete Theorems.
Print Assumptions Soundness.soundness.
Print Assumptions Soundness.soundness_value.
Print Assumptions CheckComplete.infer_complete.
Print Assumptions CheckComplete.has_type_dec.
Print Assumptions CheckComplete.genv_ok_dec.
Print Assumptions Theorems.check_program_complete.
Print Assumptions Theorems.program_ok_dec.
Print Assumptions Theorems.checked_program_safe.
Print Assumptions Soundness.progress.
Print Assumptions Soundness.preservation.
From MoonRocq.Surface Require Import Resolve.
Print Assumptions Resolve.resolve_complete.
Print Assumptions Resolve.entails_unique.
Print Assumptions Resolve.entails_typed.
From MoonRocq.Surface Require Import ElabTyped.
Print Assumptions ElabTyped.elab_typed.
From MoonRocq.Surface Require Import ElabProg.
Print Assumptions ElabProg.body_typed.
From MoonRocq.Surface Require Import Unify.
Print Assumptions Unify.unify_sound.
Print Assumptions Unify.unify_mgu.
Print Assumptions Unify.unify_complete.
From MoonRocq.Surface Require Import ElabAlg.
Print Assumptions ElabAlg.alg_sound.
