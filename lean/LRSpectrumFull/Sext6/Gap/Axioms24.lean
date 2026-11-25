import LRSpectrumFull.Sext6.Gap.ThmXEx

/-!
# Axioms24: audit of Theorem X (window family `([N] \ {r}) ∪ W`)  [2026-11-25]

`#print axioms` and `#check` for the statements of `ThmXRun`, `ThmXTab`, `ThmXWit`, `ThmXArc`, `ThmXMain`, `ThmXEx`.

This module proves nothing: it prints `#print axioms` (and `#check`) for the declarations it names.
-/

open LRSpectrumFull.Sext6.Gap

#print axioms xholds_iff_dspec
#print axioms xholds_of_le_three
#print axioms xholds_run
#print axioms not_xholds_of_ge
#print axioms lastExc_of_finite
#print axioms lastExc_r2
#print axioms lastExc_r4
#print axioms lastExc_r6
#print axioms lastExc_r10
#print axioms lastExc_r12
#print axioms lastExc_r18
#print axioms lastExc_r24
#print axioms lastExc_r30
#print axioms lastExc_r42
#print axioms lastExc_r60
#print axioms nonInterval_42
#print axioms wit_far
#print axioms ML_ge_of_witness
#print axioms ML_ge_of_le
#print axioms ML_ge_of_drop
#print axioms arcV_pos
#print axioms coreV
#print axioms gapV_le
#print axioms ML_le_two_div_2N1
#print axioms thmX_iff
#print axioms thmX_dFam
#print axioms thmX_xholds
#print axioms thmX_le_three
#print axioms thmX_run
#print axioms thmX_last
#print axioms thmX_minimal
#print axioms thmX_last_r6
#print axioms isV_example
#print axioms example_lt

#check @xholds_iff_dspec
#check @xholds_run
#check @LastExc
#check @IsV
#check @thmX_iff
#check @thmX_dFam
#check @thmX_xholds
#check @thmX_run
#check @thmX_last
#check @thmX_minimal
