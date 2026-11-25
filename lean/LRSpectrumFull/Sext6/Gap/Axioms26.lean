import LRSpectrumFull.Sext6.Gap.LinLFinal8

/-!
# Axioms26: audit of Theorem L (`LinLMeas`, `LinLCount`, `LinLCore`, `LinLFinal`, `LinLLattice`,
`LinLCount8`, `LinLFinal8`)  [2026-11-25]

`#print axioms` for the statements of the `LinL*` modules.  This module proves nothing.
-/

open LRSpectrumFull.Sext6.Gap

-- LinLMeas
#print axioms LinL.exists_good_point_gen
#print axioms LinL.badMeas_osc
#print axioms LinL.bad_subset_arc
#print axioms LinL.arc_data'
#print axioms LinL.arc_data
-- LinLCount (Stage A)
#print axioms LinL.cop_card_le_two
#print axioms LinL.zero_forces
#print axioms LinL.small_total
#print axioms LinL.smallTot_18
-- LinLCore
#print axioms LinL.exists_alive
#print axioms robust_core_linC
#print axioms ML_ge_robust_linC
#print axioms robust_core_lin
#print axioms ML_ge_robust_lin
-- LinLFinal (Stage A corollaries)
#print axioms theoremS_linC
#print axioms cor_a_linC
#print axioms theoremS_lin18
#print axioms cor_a_lin18
#print axioms theoremS_lin18_big
-- LinLLattice (Stage B)
#print axioms LinL.lam_neg
#print axioms LinL.lam_mono_rho
#print axioms LinL.lam_anti
#print axioms LinL.lam_scale_le
#print axioms LinL.lam_le_vol
#print axioms LinL.cell_sum_le
#print axioms LinL.lam_lattice_sum
-- LinLCount8
#print axioms LinL.small_total8
#print axioms LinL.smallTot_8
-- LinLFinal8
#print axioms ML_ge_robust_lin8
#print axioms theoremS_linear
#print axioms cor_a_linear
#print axioms theoremS_linear_big
#print axioms chebCond_lin8_table
#print axioms theoremS_linear_table
#print axioms mchebLin_le_mcheb
#print axioms mchebLin_lt_mcheb
