import LRSpectrumFull.Sext6.Gap.InsLower
import LRSpectrumFull.Sext6.Gap.InsDescent2

/-!
# Theorem INS: axiom audit  [2026-11-25]

This module proves nothing: it prints `#print axioms` (and `#check`) for the declarations it names, and is imported by `Sext6.Gap.All`.
-/

open LRSpectrumFull.Sext6.Gap

#print axioms ML_snoc_ge_LIP
#print axioms Hform_reflect
#print axioms Hform_lt_mu
#print axioms Hform_le_mu
#print axioms Hcap_right
#print axioms Hcap_left
#print axioms Hcap
#print axioms peak_gen
#print axioms ML_snoc_le_Hform
#print axioms peak_right_lower
#print axioms peak_left_lower
#print axioms peak_lower
#print axioms ins_E_lower
#print axioms ins_E
#print axioms descent_D1
#print axioms descent_D2_forward
#print axioms descent_D3
#print axioms descent_D3_of_LRC
#print axioms Hform_sep
#print axioms peak_unif
#print axioms descent_D2_backward
#print axioms descent_D2
