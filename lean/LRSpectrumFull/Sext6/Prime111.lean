/-
# The 111-prime variant.

`cleanPrimes111` = the clean primes in [571, 1361] (recounted from the per-prime search outputs
(not shipped) by a bounded C program: exactly one CLASS line, equal to 1 2 3 4 5 6; count 111).  `ResidueData111` is the hypothesis (computed, no
certificate) and is implied by `ResidueData` (the 150-prime set).  No sorry, no axiom.
-/
import LRSpectrumFull.Sext6.Statement

namespace LRSpectrumFull
namespace Sext6

/-- The 111 clean primes in [571, 1361] (list read from the engine logs, 2026-11-24). -/
def cleanPrimes111 : List ℕ :=
  [   571, 577, 587, 593, 601, 607, 613, 617, 631, 641, 643, 647, 653, 659, 661, 673, 677, 683, 691, 
   701, 709, 719, 727, 733, 739, 743, 751, 761, 769, 773, 787, 797, 809, 811, 821, 823, 827, 829, 
   839, 853, 857, 859, 863, 877, 881, 883, 887, 907, 911, 919, 929, 937, 941, 947, 953, 967, 971, 
   977, 983, 991, 997, 1009, 1013, 1019, 1021, 1031, 1033, 1039, 1049, 1051, 1061, 1063, 1069, 
   1087, 1091, 1093, 1097, 1103, 1109, 1117, 1123, 1129, 1151, 1153, 1163, 1171, 1181, 1187, 1193, 
   1201, 1213, 1217, 1223, 1229, 1231, 1237, 1249, 1259, 1277, 1279, 1283, 1289, 1291, 1297, 1301, 
   1303, 1307, 1319, 1321, 1327, 1361]

theorem cleanPrimes111_length : cleanPrimes111.length = 111 := by decide +kernel

theorem cleanPrimes111_nodup : cleanPrimes111.Nodup := by decide +kernel

/-- the 111-set is exactly the part of the 150-set lying in [571, 1361]. -/
theorem cleanPrimes111_eq :
    cleanPrimes111 = cleanPrimes150.filter (fun p => 571 ≤ p ∧ p ≤ 1361) := by decide +kernel

theorem cleanPrimes111_sub : ∀ p ∈ cleanPrimes111, p ∈ cleanPrimes150 := by decide +kernel

/-- Hypothesis (COMPUTED, C search, no certificate yet): the 111 primes are clean. -/
def ResidueData111 : Prop :=
  cleanPrimes111.length = 111 ∧ ∀ p ∈ cleanPrimes111, p.Prime ∧ CleanPrime p

theorem ResidueData111_of_150 (h : ResidueData) : ResidueData111 :=
  ⟨cleanPrimes111_length, fun p hp => h.2 p (cleanPrimes111_sub p hp)⟩

end Sext6
end LRSpectrumFull

#print axioms LRSpectrumFull.Sext6.cleanPrimes111_eq
#print axioms LRSpectrumFull.Sext6.ResidueData111_of_150
