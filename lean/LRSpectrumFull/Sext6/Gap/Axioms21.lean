import LRSpectrumFull.Sext6.Gap.OneRL2Val
import LRSpectrumFull.Sext6.Gap.OneRGh

/-!
# Axioms21: audit of the one-entry deletion `[N] \ {r}`, the bound `L2`, the sharper exact value, Proposition G  [2026-11-25]

`#print axioms` and `#check` for the statements of `OneRL2`, `OneRL2Val`, `OneRG`, `OneRGh`.

This module proves nothing: it prints `#print axioms` (and `#check`) for the declarations it names.
-/

open LRSpectrumFull.Sext6.Gap

#print axioms arc_local_max
#print axioms local_max_classify
#print axioms L2_delB
#print axioms ML_wFam_eq_snoc
#print axioms ML_snoc_le_self
#print axioms spec_d1Fam
#print axioms one_entry_value_aux
#print axioms one_entry_value_thr
#print axioms one_entry_value_2N2
#print axioms one_entry_value_2N2_dFam
#print axioms prop_G_core
#print axioms prop_G
#print axioms G_form_eq
#print axioms prop_G_h

#check @local_max_classify
#check @L2_delB
#check @one_entry_value_thr
#check @one_entry_value_2N2
#check @one_entry_value_2N2_dFam
#check @prop_G
#check @prop_G_h
