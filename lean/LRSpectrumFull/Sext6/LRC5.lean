import LRSpectrumFull.Sext6.Height
import LRSpectrumFull.L5S5.FiveSpeedFinal3

/-! # LRC 5 from the five-speed spectrum (our own unconditional Lean theorem)

`Sext6.LRC 5` (any five distinct positive integer speeds have `ML ≥ 1/6`) follows from
`L5S5.five_speed_spectrum_final`: if `ML v < 1/5` then `ML v = s/(5s+1) ≥ 1/6` (`s ≥ 1`), else `ML v ≥ 1/5 > 1/6`.
So the hypothesis `LRC 5` of `TheoremA16_LRC5` is discharged by an in-tree theorem. -/
namespace LRSpectrumFull
namespace Sext6

theorem LRC5 : LRC 5 := by
  intro k hk v hinj hpos
  have hk4 : k = 4 := by omega
  subst hk4
  have h6 : (((5 : ℕ) : ℝ) + 1) = 6 := by norm_num
  rw [h6]
  by_cases h : ML v < 1 / 5
  · obtain ⟨s, hs, he⟩ := L5S5.five_speed_spectrum_final v hpos hinj h
    have hs' : (1 : ℝ) ≤ s := by exact_mod_cast hs
    rw [he, div_le_div_iff₀ (by norm_num) (by positivity)]
    nlinarith
  · push_neg at h
    linarith

end Sext6
end LRSpectrumFull

#print axioms LRSpectrumFull.Sext6.LRC5
