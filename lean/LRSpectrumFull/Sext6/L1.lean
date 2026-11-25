/-
# L1 (closed hitting set), VERIFIED target.
If ML v ≤ 1/7 (six speeds), then for every prime p (indeed every modulus p > 0) the set of
speeds, as residues mod p, is a closed hitting set: for each class a there is i with
‖v_i a / p‖ ≤ 1/7, i.e. 7 · bdist p (v_i a) ≤ p.
-/
import LRSpectrumFull.Sext6.Statement

namespace LRSpectrumFull
namespace Sext6

/-- `‖z / p‖ = bdist p z / p`. -/
theorem nearestIntDist_div_eq (z : ℤ) (p : ℕ) (hp : 0 < p) :
    nearestIntDist ((z : ℝ) / p) = ((bdist p z : ℤ) : ℝ) / p := by
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp
  have hfract : Int.fract ((z : ℝ) / p) = ((z % p : ℤ) : ℝ) / p :=
    Int.fract_div_intCast_eq_div_intCast_mod
  unfold nearestIntDist bdist
  rw [hfract]
  have h1 : (1 : ℝ) - ((z % p : ℤ) : ℝ) / p = ((p : ℝ) - ((z % p : ℤ) : ℝ)) / p := by
    field_simp
  rw [h1]
  push_cast
  rcases le_total ((z % p : ℤ) : ℝ) ((p : ℝ) - ((z % p : ℤ) : ℝ)) with h | h
  · rw [min_eq_left (div_le_div_of_nonneg_right h hpR.le)]
    rw [min_eq_left (by exact_mod_cast (by exact_mod_cast h : (z % p : ℤ) ≤ (p : ℤ) - z % p))]
  · rw [min_eq_right (div_le_div_of_nonneg_right h hpR.le)]
    rw [min_eq_right (by exact_mod_cast (by exact_mod_cast h : (p : ℤ) - z % p ≤ z % p))]

/-- **L1.** `ML v ≤ 1/7` makes the speeds, as residues mod `p`, a closed hitting set. -/
theorem L1 (v : Fin 6 → ℤ) (hML : ML v ≤ 1 / 7) (p : ℕ) (hp : 0 < p) :
    Hit p (Finset.univ.image v) := by
  intro a _
  have hgap : gap v ((a : ℝ) / p) ≤ 1 / 7 :=
    le_trans (le_csSup (bddAbove_range_gap v) ⟨_, rfl⟩) hML
  simp only [gap, Finset.inf'_le_iff] at hgap
  obtain ⟨i, _, hi⟩ := hgap
  refine ⟨v i, Finset.mem_image_of_mem _ (Finset.mem_univ i), ?_⟩
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp
  have e : (v i : ℝ) * ((a : ℝ) / p) = ((v i * a : ℤ) : ℝ) / p := by push_cast; ring
  rw [e, nearestIntDist_div_eq _ p hp, div_le_iff₀ hpR] at hi
  have : (7 : ℝ) * ((bdist p (v i * a) : ℤ) : ℝ) ≤ p := by linarith
  exact_mod_cast this

end Sext6
end LRSpectrumFull

#print axioms LRSpectrumFull.Sext6.L1
