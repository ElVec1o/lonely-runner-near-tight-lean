import Mathlib.Tactic.NormNum.Prime
import LRSpectrumFull.Sext6.PairFinal
import LRSpectrumFull.Sext6.K313.P313.Top
import LRSpectrumFull.Sext6.K313.P359.Top
import LRSpectrumFull.Sext6.K313.P373.Top
import LRSpectrumFull.Sext6.K313.P379.Top
import LRSpectrumFull.Sext6.K313.P383.Top
import LRSpectrumFull.Sext6.K313.P389.Top
import LRSpectrumFull.Sext6.K313.P397.Top
import LRSpectrumFull.Sext6.K313.P401.Top

/- Discharge of `ResidueDataSub P8` from the kernel-checked `KC.CleanPrimeP` theorems (each `KC.CleanPrimeP : Sext6.CleanPrime P`,
   stated in P<P>/Top.lean with `open LRSpectrumFull.Sext6`), and the unconditional box theorem for the 8 smallest clean primes. -/
namespace LRSpectrumFull
namespace Sext6

theorem ResidueDataSub_P8 : ResidueDataSub P8 := by
  intro p hp
  rw [P8_eq] at hp
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨by norm_num, KC.CleanPrime313⟩
  · exact ⟨by norm_num, KC.CleanPrime359⟩
  · exact ⟨by norm_num, KC.CleanPrime373⟩
  · exact ⟨by norm_num, KC.CleanPrime379⟩
  · exact ⟨by norm_num, KC.CleanPrime383⟩
  · exact ⟨by norm_num, KC.CleanPrime389⟩
  · exact ⟨by norm_num, KC.CleanPrime397⟩
  · exact ⟨by norm_num, KC.CleanPrime401⟩

/-- `TheoremBox 10215`, no hypotheses. -/
theorem TheoremBox_P8_unconditional : TheoremBox 10215 := TheoremBox_P8 ResidueDataSub_P8

end Sext6
end LRSpectrumFull

#print axioms LRSpectrumFull.Sext6.ResidueDataSub_P8
#print axioms LRSpectrumFull.Sext6.TheoremBox_P8_unconditional
