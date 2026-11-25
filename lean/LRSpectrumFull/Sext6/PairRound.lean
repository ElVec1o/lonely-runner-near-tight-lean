/-
# PairRound: the rounding lemma (F2 pair-agreement, part 2).  [AK, 2026-11-24]

If `(a,b)` is a 30-grid witness for the relative labeling `c` (`bd_30(a*m + b*c_m) >= 5`, m = 1..6, `|c_m| <= 6`)
and `p, q >= 253` (naturals, not necessarily prime), the nearest-integer roundings
`x = round(p*a/30)`, `y = round(q*b/30)` (`x = (2*p*a+30)/60` floor division, exactly as `roundcheck.c`)
satisfy, for every `m`, with `N = p*q`:

    7 * bdist_N( x*m*q + c_m*y*p ) > N ,      equivalently  ‖ m*x/p + c_m*y/q ‖ > 1/7 .

Hand derivation: `60 z = 2 N T + F`, `T = a m + b c_m`, `|F| <= 180 (p+q)`, and `N > 126 (p+q)` for `p,q >= 253`
(`253^2 = 64009 > 126*506 = 63756`; the threshold is sharp up to 252, where `6/252 = 1/42`).
-/
import LRSpectrumFull.Sext6.PairGrid
import LRSpectrumFull.Sext6.L1
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.LinearCombination

namespace LRSpectrumFull
namespace Sext6

theorem prod_bound (k u : ℤ) (hk : -6 ≤ k ∧ k ≤ 6) (hu : -30 ≤ u ∧ u ≤ 30) :
    -180 ≤ k * u ∧ k * u ≤ 180 := by
  have h : |k * u| ≤ 6 * 30 := by
    rw [abs_mul]
    exact mul_le_mul (abs_le.2 hk) (abs_le.2 hu) (abs_nonneg _) (by norm_num)
  have := abs_le.1 h
  constructor <;> linarith [this.1, this.2]

/-- Core integer inequality for one slot. -/
theorem round_slot (p q : ℕ) (hp : 253 ≤ p) (hq : 253 ≤ q) (a b k c : ℤ)
    (hk : 1 ≤ k ∧ k ≤ 6) (hc : -6 ≤ c ∧ c ≤ 6) (hg : 5 ≤ bdist 30 (a * k + b * c)) :
    ((p * q : ℕ) : ℤ) <
      7 * bdist (p * q) (((2 * (p : ℤ) * a + 30) / 60) * k * q + c * ((2 * (q : ℤ) * b + 30) / 60) * p) := by
  have hP : (253 : ℤ) ≤ p := by exact_mod_cast hp
  have hQ : (253 : ℤ) ≤ q := by exact_mod_cast hq
  unfold bdist at hg ⊢
  push_cast at hg ⊢
  rw [le_min_iff] at hg
  obtain ⟨g1, g2⟩ := hg
  generalize (p : ℤ) = P at *
  generalize (q : ℤ) = Q at *
  have e1 := Int.mul_ediv_add_emod (2 * P * a + 30) 60
  have e2 := Int.mul_ediv_add_emod (2 * Q * b + 30) 60
  have r1a := Int.emod_nonneg (2 * P * a + 30) (by norm_num : (60 : ℤ) ≠ 0)
  have r1b := Int.emod_lt_of_pos (2 * P * a + 30) (by norm_num : (0 : ℤ) < 60)
  have r2a := Int.emod_nonneg (2 * Q * b + 30) (by norm_num : (60 : ℤ) ≠ 0)
  have r2b := Int.emod_lt_of_pos (2 * Q * b + 30) (by norm_num : (0 : ℤ) < 60)
  have hT := Int.mul_ediv_add_emod (a * k + b * c) 30
  generalize (2 * P * a + 30) / 60 = x at *
  generalize (2 * P * a + 30) % 60 = r1 at *
  generalize (2 * Q * b + 30) / 60 = y at *
  generalize (2 * Q * b + 30) % 60 = r2 at *
  generalize (a * k + b * c) / 30 = j at *
  generalize (a * k + b * c) % 30 = ρ at *
  have hg' : 5 ≤ ρ ∧ ρ ≤ 25 := by omega
  have hF1 := prod_bound k (30 - r1) ⟨by linarith, by linarith⟩ ⟨by linarith, by linarith⟩
  have hF2 := prod_bound c (30 - r2) hc ⟨by linarith, by linarith⟩
  obtain ⟨Z, hZdef⟩ : ∃ Z, Z = x * k * Q + c * y * P - P * Q * j := ⟨_, rfl⟩
  have hZ : 60 * Z = 2 * (P * Q) * ρ + (Q * (k * (30 - r1)) + P * (c * (30 - r2))) := by
    rw [hZdef]
    linear_combination (k * Q) * e1 + (c * P) * e2 + (-2 * P * Q) * hT
  have hQ0 : 0 ≤ Q := by linarith
  have hP0 : 0 ≤ P := by linarith
  have hN : 0 ≤ P * Q := mul_nonneg hP0 hQ0
  have q1 : Q * (k * (30 - r1)) ≤ Q * 180 := mul_le_mul_of_nonneg_left hF1.2 hQ0
  have q2 : Q * (-180) ≤ Q * (k * (30 - r1)) := mul_le_mul_of_nonneg_left hF1.1 hQ0
  have q3 : P * (c * (30 - r2)) ≤ P * 180 := mul_le_mul_of_nonneg_left hF2.2 hP0
  have q4 : P * (-180) ≤ P * (c * (30 - r2)) := mul_le_mul_of_nonneg_left hF2.1 hP0
  have n1 : (P * Q) * 5 ≤ (P * Q) * ρ := mul_le_mul_of_nonneg_left hg'.1 hN
  have n2 : (P * Q) * ρ ≤ (P * Q) * 25 := mul_le_mul_of_nonneg_left hg'.2 hN
  have hbig : 126 * (P + Q) < P * Q := by
    nlinarith [mul_nonneg (sub_nonneg.2 hP) (sub_nonneg.2 hQ)]
  have h7a : P * Q < 7 * Z := by nlinarith
  have h7b : 7 * Z < 6 * (P * Q) := by nlinarith
  have hzZ : x * k * Q + c * y * P = Z + (P * Q) * j := by rw [hZdef]; ring
  have hNpos : 0 < P * Q := by nlinarith
  have hZ0 : 0 ≤ Z := by linarith
  have hZN : Z < P * Q := by linarith
  have hmod : (x * k * Q + c * y * P) % (P * Q) = Z := by
    rw [hzZ, Int.add_mul_emod_self_left, Int.emod_eq_of_lt hZ0 hZN]
  rw [hmod]
  rcases le_total Z (P * Q - Z) with h | h
  · rw [min_eq_left h]; linarith
  · rw [min_eq_right h]; linarith

end Sext6
end LRSpectrumFull
