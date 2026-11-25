/-
# Six-speed tight classification (PRR route): statement file  [pilot, 2026-11-24]

Reuses `LRSpectrumFull.ML` (`MaxLoneliness.lean`): `ML v = sSup_t min_i ‖v_i t‖` for `v : Fin (k+1) → ℤ`.

Theorem A (six distinct positive integers with ML ≤ 1/7 are c·(1..6)) is STATED here as a Prop,
with its two external inputs as explicit hypotheses, never axioms:
* `HeightBound`   : Yi-Gill-Bu Thm 11.1(i) consequence, primitive v with ML ≤ 1/7 has max < 17,010,000;
* `ResidueData`   : the 150 primes 313..1459 are "clean" (computer search, C engine prr.c).
No `sorry`, no `axiom`.
-/
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Order.Interval.Finset.Defs
import Mathlib.Data.Int.Interval
import LRSpectrumFull.MaxLoneliness

namespace LRSpectrumFull
namespace Sext6

/-- Balanced distance of the residue of `x` mod `p` to 0: `min (x mod p, p - x mod p)`. -/
def bdist (p : ℕ) (x : ℤ) : ℤ := min (x % p) ((p : ℤ) - x % p)

/-- `S` (residues, taken up to sign) is a closed hitting set mod `p` at threshold 1/7:
every nonzero class `a` has some `r ∈ S` with `‖r a / p‖ ≤ 1/7`, i.e. `7 · bdist p (r a) ≤ p`. -/
def Hit (p : ℕ) (S : Finset ℤ) : Prop :=
  ∀ a : ℤ, ¬ (p : ℤ) ∣ a → ∃ r ∈ S, 7 * bdist p (r * a) ≤ p

/-- `p` is *clean* (six speeds): every closed hitting set of at most 6 nonzero residues contains a
unit multiple, up to sign, of `{1,…,6}`.  (Equivalent to: the only inclusion-minimal such set is the
class of `(1,…,6)`, the engine's notion.) -/
def CleanPrime (p : ℕ) : Prop :=
  ∀ S : Finset ℤ, S.card ≤ 6 → (∀ r ∈ S, ¬ (p : ℤ) ∣ r) → Hit p S →
    ∃ u : ℤ, ¬ (p : ℤ) ∣ u ∧ ∀ i ∈ Finset.Icc (1 : ℤ) 6,
      ∃ r ∈ S, (p : ℤ) ∣ r - u * i ∨ (p : ℤ) ∣ r + u * i

/-- Primitive: no integer `d > 1` divides every entry. -/
def Primitive {k : ℕ} (v : Fin (k + 1) → ℤ) : Prop :=
  ∀ d : ℕ, (∀ i, (d : ℤ) ∣ v i) → d = 1

/-- Hypothesis (CITED, unrefereed): Yi-Gill-Bu, arXiv 2610.40694v1, Thm 11.1(i) at n = 6,
κ₆ = 30⁴, giving |v| < 21 κ₆ = 17,010,000 for primitive positive v with ML v ≤ 1/7. -/
def HeightBound : Prop :=
  ∀ v : Fin 6 → ℤ, (∀ i, 0 < v i) → Primitive v → ML v ≤ 1 / 7 → ∀ i, v i < 17010000

/-- The 150 clean primes in [313, 1459] found by the per-prime search (list from the per-prime search outputs
(not shipped), recounted 2026-11-24). -/
def cleanPrimes150 : List ℕ :=
  [313, 359, 373, 379, 383, 389, 397, 401, 409, 419, 433, 439, 443, 449, 463, 467, 479, 491, 499, 509,  521, 541, 547, 557, 563, 571, 577, 587, 593, 601, 607, 613, 617, 631, 641, 643, 647, 653, 659, 661,  673, 677, 683, 691, 701, 709, 719, 727, 733, 739, 743, 751, 761, 769, 773, 787, 797, 809, 811, 821,  823, 827, 829, 839, 853, 857, 859, 863, 877, 881, 883, 887, 907, 911, 919, 929, 937, 941, 947, 953,  967, 971, 977, 983, 991, 997, 1009, 1013, 1019, 1021, 1031, 1033, 1039, 1049, 1051, 1061, 1063,  1069, 1087, 1091, 1093, 1097, 1103, 1109, 1117, 1123, 1129, 1151, 1153, 1163, 1171, 1181, 1187,  1193, 1201, 1213, 1217, 1223, 1229, 1231, 1237, 1249, 1259, 1277, 1279, 1283, 1289, 1291, 1297,  1301, 1303, 1307, 1319, 1321, 1327, 1361, 1367, 1373, 1381, 1399, 1409, 1423, 1427, 1429, 1433,  1439, 1447, 1451, 1453, 1459]

/-- Hypothesis (COMPUTED, C search, no certificate yet): residue data. -/
def ResidueData : Prop :=
  cleanPrimes150.length = 150 ∧ ∀ p ∈ cleanPrimes150, p.Prime ∧ CleanPrime p

/-- **Theorem A (statement).** Six distinct positive integers with `ML ≤ 1/7` are `c · (1,…,6)`
up to order. -/
def TheoremA : Prop :=
  ∀ v : Fin 6 → ℤ, Function.Injective v → (∀ i, 0 < v i) → ML v ≤ 1 / 7 →
    ∃ (c : ℤ) (σ : Equiv.Perm (Fin 6)), 0 < c ∧ ∀ i, v i = c * ((σ i : ℕ) + 1)

/-- The conditional form actually claimed. -/
def TheoremA_conditional : Prop := HeightBound → ResidueData → TheoremA

end Sext6
end LRSpectrumFull
