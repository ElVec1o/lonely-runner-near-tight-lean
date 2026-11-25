import LRSpectrumFull.Sext6.Gap.OneRVal

/-!
# Axioms19: audit of the one-entry deletion `[N] \ {r}` (Plan 3)  [2026-11-25]

`#print axioms` and `#check` for the statements of `OneRBase`, `OneRArc`, `OneRVal`.

This module proves nothing: it prints `#print axioms` (and `#check`) for the declarations it names, and is imported by `Sext6.Gap.All`.
-/

open LRSpectrumFull.Sext6.Gap

#print axioms ML_ge_delB
#print axioms gap_le_two_div
#print axioms ML_eq_two_div
#print axioms ML_bFam
#print axioms eqtime_classify
#print axioms gap_eq_at_inv
#print axioms runners_at_eq
#print axioms V1_holds
#print axioms V2_holds
#print axioms vmu_eq
#print axioms one_entry_value
#print axioms one_entry_value_dFam

#check @ML_eq_two_div
#check @eqtime_classify
#check @gap_eq_at_inv
#check @runners_at_eq
#check @V1_holds
#check @V2_holds
#check @vmu_eq
#check @one_entry_value
#check @one_entry_value_dFam
