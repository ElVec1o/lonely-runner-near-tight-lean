import LRSpectrumFull.Sext6.Gap.CThm
import LRSpectrumFull.Sext6.Gap.GFam

/-!
# Theorem C and G(N): axiom audit  [2026-11-24]

This module proves nothing: it prints `#print axioms` (and `#check`) for the declarations it names, and is imported by `Sext6.Gap.All`.
-/

open LRSpectrumFull.Sext6.Gap

#print axioms gNT_ge
#print axioms CSpec.spec
#print axioms C_value
#print axioms C_scaled
#print axioms exists_next_prime
#print axioms cspec_primorial
#print axioms liminf_gap_zero
#print axioms liminf_gap_zero_frequently
#print axioms gapScaled_nonneg
#print axioms no_inv_sq_lower_bound
#print axioms stab_fails_31
#print axioms ML_nontight
#print axioms gNT_le_Phi
#print axioms gNT_le_Gfam
#print axioms Gfam_le_Phi
#print axioms Gfam_attained
#print axioms mFam_nonTight
#print axioms mFam_le
#print axioms mFam_ge_two
#print axioms PhiFam_mono
