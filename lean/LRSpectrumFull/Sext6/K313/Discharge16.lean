import Mathlib.Tactic.NormNum.Prime
import LRSpectrumFull.Sext6.K313.Discharge
import LRSpectrumFull.Sext6.K313.P409.Top
import LRSpectrumFull.Sext6.K313.P419.Top
import LRSpectrumFull.Sext6.K313.P433.Top
import LRSpectrumFull.Sext6.K313.P439.Top
import LRSpectrumFull.Sext6.K313.P443.Top
import LRSpectrumFull.Sext6.K313.P449.Top
import LRSpectrumFull.Sext6.K313.P463.Top
import LRSpectrumFull.Sext6.K313.P467.Top

/- Discharge of `ResidueDataSub P16` (P8 from Discharge.lean plus the 8 further primes) and the unconditional 16-prime box theorems. -/
namespace LRSpectrumFull
namespace Sext6

theorem ResidueDataSub_P16 : ResidueDataSub P16 := by
  intro p hp
  rw [P16_eq] at hp
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact ResidueDataSub_P8 313 (by rw [P8_eq]; simp)
  · exact ResidueDataSub_P8 359 (by rw [P8_eq]; simp)
  · exact ResidueDataSub_P8 373 (by rw [P8_eq]; simp)
  · exact ResidueDataSub_P8 379 (by rw [P8_eq]; simp)
  · exact ResidueDataSub_P8 383 (by rw [P8_eq]; simp)
  · exact ResidueDataSub_P8 389 (by rw [P8_eq]; simp)
  · exact ResidueDataSub_P8 397 (by rw [P8_eq]; simp)
  · exact ResidueDataSub_P8 401 (by rw [P8_eq]; simp)
  · exact ⟨by norm_num, KC.CleanPrime409⟩
  · exact ⟨by norm_num, KC.CleanPrime419⟩
  · exact ⟨by norm_num, KC.CleanPrime433⟩
  · exact ⟨by norm_num, KC.CleanPrime439⟩
  · exact ⟨by norm_num, KC.CleanPrime443⟩
  · exact ⟨by norm_num, KC.CleanPrime449⟩
  · exact ⟨by norm_num, KC.CleanPrime463⟩
  · exact ⟨by norm_num, KC.CleanPrime467⟩

/-- `TheoremBox 41912890`, no hypotheses. -/
theorem TheoremBox_P16_unconditional : TheoremBox 41912890 := TheoremBox_P16 ResidueDataSub_P16

/-- the YGB-range box `17010000`, no hypotheses. -/
theorem TheoremBox_P16_YGB_unconditional : TheoremBox 17010000 := TheoremBox_P16_YGB ResidueDataSub_P16

end Sext6
end LRSpectrumFull

#print axioms LRSpectrumFull.Sext6.ResidueDataSub_P16
#print axioms LRSpectrumFull.Sext6.TheoremBox_P16_unconditional
#print axioms LRSpectrumFull.Sext6.TheoremBox_P16_YGB_unconditional
