/-
# Dilation invariance of ML (piece 3b).  `ML (c • v) = ML v` for every nonzero integer `c`.
Reason: `gap (c v) t = gap v (c t)` and `t ↦ c t` is a bijection of ℝ, so the two ranges coincide.
-/
import LRSpectrumFull.MaxLoneliness

namespace LRSpectrumFull
namespace Sext6

theorem gap_smul {k : ℕ} (c : ℤ) (v : Fin (k + 1) → ℤ) (t : ℝ) :
    gap (fun i => c * v i) t = gap v ((c : ℝ) * t) := by
  unfold gap
  congr 1
  funext i
  push_cast
  ring_nf

theorem ML_smul {k : ℕ} (c : ℤ) (hc : c ≠ 0) (v : Fin (k + 1) → ℤ) :
    ML (fun i => c * v i) = ML v := by
  have hc' : (c : ℝ) ≠ 0 := Int.cast_ne_zero.mpr hc
  unfold ML
  congr 1
  ext y
  simp only [Set.mem_range, gap_smul]
  constructor
  · rintro ⟨t, rfl⟩
    exact ⟨(c : ℝ) * t, rfl⟩
  · rintro ⟨t, rfl⟩
    refine ⟨t / c, ?_⟩
    rw [show (c : ℝ) * (t / c) = t by field_simp]

end Sext6
end LRSpectrumFull

#print axioms LRSpectrumFull.Sext6.ML_smul
