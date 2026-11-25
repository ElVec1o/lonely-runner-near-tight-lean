/-
# PairFinal: instances of the pair-agreement box theorem and Theorem A  [AL, 2026-11-24]

Hypotheses: `ResidueDataSub P` (the listed primes are prime and clean; computed, uncertified) and, for
`TheoremA`, the height bound of YGB.  Nothing else.
* `P8`  = the 8 smallest clean primes (313..401): `6*1 + 1 + 1 = 8`, box `B = 10215` (no height bound).
* `P16` = the 16 smallest clean primes (313..467): `6*2 + 3 + 1 = 16`, box `B = 41,912,890`
  (hence `17,010,000`) (no height bound).
* `P150` = all 150 (`ResidueData`): `6*21 + 22 + 1 = 149 <= 150`, box `B = 10^57`, and the exact
  maximal `B = 8887468835591605986541378593783692034973388144092713606810` (`counts.py`).
* `TheoremA16` : `HeightBoundYGB6 -> LRC 5 -> LRC 4 -> ResidueDataSub P16 -> TheoremA`.
-/
import LRSpectrumFull.Sext6.PairCount
import LRSpectrumFull.Sext6.Height

namespace LRSpectrumFull
namespace Sext6

def P8 : List ℕ := cleanPrimes150.take 8
def P16 : List ℕ := cleanPrimes150.take 16

theorem P8_eq : P8 = [313, 359, 373, 379, 383, 389, 397, 401] := by decide +kernel
theorem P16_eq : P16 = [313, 359, 373, 379, 383, 389, 397, 401, 409, 419, 433, 439, 443, 449, 463, 467] := by
  decide +kernel

theorem ResidueDataSub_of_ResidueData (h : ResidueData) : ResidueDataSub cleanPrimes150 := h.2

theorem ResidueDataSub_take (n : ℕ) (h : ResidueDataSub cleanPrimes150) :
    ResidueDataSub (cleanPrimes150.take n) := fun p hp => h p (List.mem_of_mem_take hp)

theorem pairData_P8 (h : ResidueDataSub P8) : PairData P8 :=
  PairData.mk' P8 (by decide +kernel) (by decide +kernel) h

theorem pairData_P16 (h : ResidueDataSub P16) : PairData P16 :=
  PairData.mk' P16 (by decide +kernel) (by decide +kernel) h

theorem pairData_P150 (h : ResidueDataSub cleanPrimes150) : PairData cleanPrimes150 :=
  PairData.mk' cleanPrimes150 (by decide +kernel) (by decide +kernel) h

/-- the arithmetic of the counting condition `6 beta(B) + beta(11 B) + 1 <= |P|`. -/
theorem count_P8 : 6 * betaOf P8 10215 + betaOf P8 (11 * 10215) + 1 ≤ P8.length := by decide +kernel
theorem count_P16 : 6 * betaOf P16 41912890 + betaOf P16 (11 * 41912890) + 1 ≤ P16.length := by
  decide +kernel
theorem count_P150 : 6 * betaOf cleanPrimes150 (10 ^ 57) + betaOf cleanPrimes150 (11 * 10 ^ 57) + 1 ≤
    cleanPrimes150.length := by decide +kernel
theorem count_P150_max :
    6 * betaOf cleanPrimes150 8887468835591605986541378593783692034973388144092713606810 +
      betaOf cleanPrimes150 (11 * 8887468835591605986541378593783692034973388144092713606810) + 1 ≤
    cleanPrimes150.length := by decide +kernel
/-- sharpness of the maximal `B` for the 150 primes: one more and the count fails. -/
theorem count_P150_max_sharp :
    cleanPrimes150.length <
    6 * betaOf cleanPrimes150 (8887468835591605986541378593783692034973388144092713606810 + 1) +
      betaOf cleanPrimes150 (11 * (8887468835591605986541378593783692034973388144092713606810 + 1)) + 1 := by
  decide +kernel
/-- the margin at the thresholds for `P8`: `10216` fails. -/
theorem count_P8_sharp : P8.length < 6 * betaOf P8 10216 + betaOf P8 (11 * 10216) + 1 := by decide +kernel

theorem TheoremBox_P8 (h : ResidueDataSub P8) : TheoremBox 10215 :=
  TheoremBoxPair P8 (pairData_P8 h) 10215 (by norm_num) count_P8

theorem TheoremBox_P16 (h : ResidueDataSub P16) : TheoremBox 41912890 :=
  TheoremBoxPair P16 (pairData_P16 h) 41912890 (by norm_num) count_P16

theorem TheoremBox_P16_YGB (h : ResidueDataSub P16) : TheoremBox 17010000 :=
  (TheoremBox_P16 h).mono (by norm_num)

theorem TheoremBox_P150 (h : ResidueDataSub cleanPrimes150) : TheoremBox (10 ^ 57) :=
  TheoremBoxPair cleanPrimes150 (pairData_P150 h) (10 ^ 57) (by norm_num) count_P150

theorem TheoremBox_P150_max (h : ResidueDataSub cleanPrimes150) :
    TheoremBox 8887468835591605986541378593783692034973388144092713606810 :=
  TheoremBoxPair cleanPrimes150 (pairData_P150 h) _ (by norm_num) count_P150_max

/-- **Theorem A**, from the height bound `HeightBound` and the 16 smallest clean primes only. -/
theorem TheoremA16_conditional : HeightBound → ResidueDataSub P16 → TheoremA :=
  fun hH hres => TheoremA_of_box 41912890 (by norm_num) (TheoremBox_P16 hres) hH

/-- **Theorem A**, fidelity form: YGB Thm 11.1(i) at `n = 6` (with `LRC 5`, `LRC 4`) and the 16 primes. -/
theorem TheoremA16 : HeightBoundYGB6 → LRC 5 → LRC 4 → ResidueDataSub P16 → TheoremA :=
  fun h h5 h4 hres => TheoremA16_conditional (heightBound_of_ygb h h5 h4) hres

/-- Theorem A from `HeightBound` and `ResidueData` (150 primes), through the pair route. -/
theorem TheoremA150_pair : HeightBound → ResidueData → TheoremA :=
  fun hH hres => TheoremA_of_box (10 ^ 57) (by norm_num) (TheoremBox_P150 hres.2) hH

end Sext6
end LRSpectrumFull

#print axioms LRSpectrumFull.Sext6.TheoremBox_P8
#print axioms LRSpectrumFull.Sext6.TheoremBox_P16
#print axioms LRSpectrumFull.Sext6.TheoremBox_P16_YGB
#print axioms LRSpectrumFull.Sext6.TheoremBox_P150
#print axioms LRSpectrumFull.Sext6.TheoremBox_P150_max
#print axioms LRSpectrumFull.Sext6.count_P150_max_sharp
#print axioms LRSpectrumFull.Sext6.count_P8_sharp
#print axioms LRSpectrumFull.Sext6.TheoremA16_conditional
#print axioms LRSpectrumFull.Sext6.TheoremA16
#print axioms LRSpectrumFull.Sext6.TheoremA150_pair
