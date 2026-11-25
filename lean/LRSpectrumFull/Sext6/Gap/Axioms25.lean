import LRSpectrumFull.Sext6.Gap.ThmXGrow

/-!
# Axioms25: audit of the Theorem X completion (`ThmXPhi`, `ThmXLast`, `ThmXGrow`)  [2026-11-25]

`#print axioms` and `#check` for the statements of `ThmXPhi`, `ThmXLast`, `ThmXGrow`.

This module proves nothing: it prints `#print axioms` (and `#check`) for the declarations it names.
-/

open LRSpectrumFull.Sext6.Gap

-- ThmXPhi
#print axioms winSet_card
#print axioms isV_out_eq
#print axioms isV_out_card
#print axioms isV_ne_r
#print axioms exists_isV

-- ThmXLast
#print axioms lastExc_lastN
#print axioms lastN_lt
#print axioms lastExc_unique
#print axioms exceptional_finite
#print axioms lstar_spec
#print axioms not_runOK_of_odd
#print axioms not_xholds_three_add_one_of_odd
#print axioms lstar_odd
#print axioms lastN_odd
#print axioms lstar_lt_maxPrimeFactor
#print axioms le_lstar_of_least_prime_not_dvd
#print axioms lstar_lt_jac
#print axioms lstar_eq_of_primorial_like
#print axioms lstar_primorial
#print axioms primorial_vals
#print axioms lstar_primorials
#print axioms lstar_r6_table
#print axioms lstar_r30_table
#print axioms lstar_r42_table

-- ThmXGrow
#print axioms excAt_of_xholds
#print axioms excAt_lastN
#print axioms exception_family
#print axioms exception_last_sharp
#print axioms n0ge_phi
#print axioms n0ge_phi_three
#print axioms ratio_ge
#print axioms exists_ratio_gt
#print axioms exists_ratio_gt_big
#print axioms growth_unbounded
#print axioms growth_frequently
#print axioms n0_growth

#check @winSet_card
#check @isV_out_card
#check @lastExc_lastN
#check @lstar_spec
#check @lstar_odd
#check @lstar_lt_maxPrimeFactor
#check @le_lstar_of_least_prime_not_dvd
#check @lstar_lt_jac
#check @lstar_primorial
#check @lstar_primorials
#check @exception_family
#check @n0ge_phi
#check @growth_unbounded
#check @growth_frequently
