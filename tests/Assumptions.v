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
