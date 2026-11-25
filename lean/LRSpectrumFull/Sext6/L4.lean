/-
# L4 (piece 3a): the second ratio-closed sextuple `(10,12,15,20,30,60)` has ML > 1/7.
Exact rational witness `t = 1/40`: the distances `‖v_i / 40‖` are `1/4, 3/10, 3/8, 1/2, 1/4, 1/2`,
all at least `1/4 > 1/7`.  Stated for every vector whose entries lie in the set of entries of `v2`
(so it covers every permutation without a permutation-invariance lemma).
-/
import LRSpectrumFull.Sext6.L1prime

namespace LRSpectrumFull
namespace Sext6

theorem v2_dist (k : Fin 6) : (1 : ℝ) / 4 ≤ nearestIntDist ((v2 k : ℝ) * (1 / 40)) := by
  have h := nearestIntDist_div_eq (v2 k) 40 (by norm_num)
  have e : (v2 k : ℝ) * (1 / 40) = ((v2 k : ℤ) : ℝ) / ((40 : ℕ) : ℝ) := by push_cast; ring
  rw [e, h]
  have hb : (10 : ℤ) ≤ bdist 40 (v2 k) :=
    (by decide : ∀ k : Fin 6, (10 : ℤ) ≤ bdist 40 (v2 k)) k
  rw [le_div_iff₀ (by norm_num)]
  have : ((10 : ℤ) : ℝ) ≤ ((bdist 40 (v2 k) : ℤ) : ℝ) := by exact_mod_cast hb
  push_cast at this ⊢
  linarith

/-- **L4.** Any vector with all entries among those of `(10,12,15,20,30,60)` has `ML > 1/7`. -/
theorem L4 (v : Fin 6 → ℤ) (hv : ∀ i, ∃ k, v i = v2 k) : ¬ ML v ≤ 1 / 7 := by
  intro hML
  have hgap : (1 : ℝ) / 4 ≤ gap v (1 / 40) := by
    apply le_gap
    intro i
    obtain ⟨k, hk⟩ := hv i
    rw [hk]
    exact v2_dist k
  have h2 : (1 : ℝ) / 4 ≤ ML v := le_trans hgap (le_csSup (bddAbove_range_gap v) ⟨_, rfl⟩)
  linarith

end Sext6
end LRSpectrumFull

#print axioms LRSpectrumFull.Sext6.L4
