import LRSpectrumFull.Sext6.Gap.CopWinFinal
import LRSpectrumFull.Sext6.Gap.CopWinBlock

/-!
# CopWin: axiom audit  [2026-11-25]

This module proves nothing: it prints `#print axioms` (and `#check`) for the declarations it names, and is imported by `Sext6.Gap.All`.
-/

open LRSpectrumFull.Sext6.Gap

#print axioms prod_dvd_of_pairwise_coprime
#print axioms cop_pow_card_le
#print axioms cop_card_dvd_le
#print axioms spoil_single_card_le_cop
#print axioms chain_cop
#print axioms copWin_of_primeWin
#print axioms robust_core_cop
#print axioms ML_ge_robust_cop
#print axioms ML_ge_robust_of_prime
#print axioms cor_a_cop
#print axioms block_coprime
#print axioms bad_card_le
#print axioms hyp_bound
#print axioms ML_ge_robust_all_cop
#print axioms cor_a_all_cop
#print axioms OE_low_all_cop
#print axioms ML_ge_wFam2_cop
#print axioms theoremW_all_cop
