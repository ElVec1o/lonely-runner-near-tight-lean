import LRSpectrumFull.Sext6.Gap.Cheb30Core
import Mathlib.Analysis.SpecialFunctions.Stirling
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Real.Pi.Bounds

/-!
# Chebyshev's 30-combination: Stirling-type bounds  [2026-11-25]

* `log_factorial_ge`  : `n log n - n ≤ log n!`   (`n ≠ 0`; Mathlib's `Stirling.le_log_factorial_stirling`).
* `log_factorial_le`  : `log n! ≤ n log n - n + log n + 1`  (`n ≥ 1`; induction, `log (1+1/n) ≥ 1/(n+1)`).
* `A30 = (14 log 2 + 9 log 3 + 5 log 5)/30`, with `91/100 ≤ A30 ≤ 95/100` (Mathlib's `*_d9` bounds).
* `b30_bounds` : for `m ≥ 1`,
    `30 A30 m - 3 log (30m) - 3 ≤ b30 m ≤ 30 A30 m + 2 log (30m) + 2`.
* `psiN_le_log_factorial` : `psiN n ≤ log n!`.
No `sorry`, no `axiom`.

Convention: No speed vector is involved in this module (number theory or real analysis); `N` denotes a natural number, the size of the ambient interval `[1,N]`.
Hypotheses: those of the individual statements (numerical bounds, structural conditions and, where named in the list above, window predicates such as `PrimeWin`, `CopWin`, `PrimeWindow7`, which later modules discharge for explicit ranges). The unproved predicates `DusartPi`, `LRCHyp`, `CopWinHyp` are not hypotheses of any statement in this module.
Axiom audit: covered by `Cheb30Axioms` (first); every later audit module imports this module (`#print axioms`; declarations not printed there are bricks of printed ones, so their axioms are bounded by the printed lines).
-/

open scoped ArithmeticFunction.vonMangoldt
open scoped Nat
open Finset

namespace LRSpectrumFull
namespace Sext6
namespace Gap
namespace Cheb30

theorem log_factorial_ge {n : ℕ} (hn : n ≠ 0) :
    (n : ℝ) * Real.log n - n ≤ Real.log ((n ! : ℕ) : ℝ) := by
  have h := Stirling.le_log_factorial_stirling hn
  have h1 : 0 ≤ Real.log (n : ℝ) :=
    Real.log_nonneg (by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hn)
  have h2 : 0 ≤ Real.log (2 * Real.pi) := Real.log_nonneg (by linarith [Real.pi_gt_three])
  linarith

theorem log_factorial_le (n : ℕ) (hn : 1 ≤ n) :
    Real.log ((n ! : ℕ) : ℝ) ≤ (n : ℝ) * Real.log n - n + Real.log n + 1 := by
  induction n, hn using Nat.le_induction with
  | base => simp
  | succ n hn ih =>
    have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
    have hn1 : (n : ℝ) + 1 ≠ 0 := by positivity
    have key : 1 ≤ ((n : ℝ) + 1) * (Real.log ((n : ℝ) + 1) - Real.log n) := by
      have h := Real.one_sub_inv_le_log_of_pos (x := ((n : ℝ) + 1) / n) (by positivity)
      rw [Real.log_div hn1 hn0.ne', inv_div] at h
      have e : 1 - (n : ℝ) / (n + 1) = 1 / (n + 1) := by field_simp; ring
      rw [e] at h
      have h' := mul_le_mul_of_nonneg_left h (by positivity : (0 : ℝ) ≤ n + 1)
      calc (1 : ℝ) = ((n : ℝ) + 1) * (1 / ((n : ℝ) + 1)) := by field_simp
        _ ≤ _ := h'
    rw [Nat.factorial_succ, Nat.cast_mul,
      Real.log_mul (Nat.cast_ne_zero.mpr n.succ_ne_zero)
        (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero n))]
    push_cast
    nlinarith [key, ih]

theorem psiN_le_log_factorial (n : ℕ) : psiN n ≤ Real.log ((n ! : ℕ) : ℝ) := by
  rw [log_factorial_eq]
  unfold psiN Lf
  apply Finset.sum_le_sum
  intro d hd
  rw [Finset.mem_Ioc] at hd
  have h1 : (1 : ℝ) ≤ ((n / d : ℕ) : ℝ) := by
    exact_mod_cast Nat.div_pos hd.2 hd.1
  have h0 : 0 ≤ Λ d := ArithmeticFunction.vonMangoldt_nonneg
  nlinarith

/-- `A30 = (14 log 2 + 9 log 3 + 5 log 5)/30 = 0.92129...`. -/
noncomputable def A30 : ℝ := (14 * Real.log 2 + 9 * Real.log 3 + 5 * Real.log 5) / 30

theorem A30_ge : (91 : ℝ) / 100 ≤ A30 := by
  have h2 := Real.log_two_gt_d9
  have h3 := Real.log_three_gt_d9
  have h5 := Real.log_five_gt_d9
  unfold A30
  norm_num at h2 h3 h5 ⊢
  linarith

theorem A30_le : A30 ≤ (95 : ℝ) / 100 := by
  have h2 := Real.log_two_lt_d9
  have h3 := Real.log_three_lt_d9
  have h5 := Real.log_five_lt_d9
  unfold A30
  norm_num at h2 h3 h5 ⊢
  linarith

theorem log_thirty_le : Real.log 30 ≤ 3.5 := by
  have h2 := Real.log_two_lt_d9
  have h3 := Real.log_three_lt_d9
  have h5 := Real.log_five_lt_d9
  have e : Real.log 30 = Real.log 2 + Real.log 3 + Real.log 5 := by
    rw [show (30 : ℝ) = 2 * 3 * 5 by norm_num, Real.log_mul (by norm_num) (by norm_num),
      Real.log_mul (by norm_num) (by norm_num)]
  rw [e]
  norm_num at h2 h3 h5 ⊢
  linarith

theorem psiN_thirty_le : psiN 30 ≤ 100 := by
  refine le_trans (psiN_le_log_factorial 30) ?_
  have h := log_factorial_le 30 (by norm_num)
  have hl := log_thirty_le
  push_cast at h
  norm_num at h hl ⊢
  linarith

theorem b30_bounds (m : ℕ) (hm : 1 ≤ m) :
    30 * A30 * m - 3 * Real.log (30 * m) - 3 ≤ b30 m ∧
      b30 m ≤ 30 * A30 * m + 2 * Real.log (30 * m) + 2 := by
  have hm0 : (m : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hl3 : 0 < Real.log 3 := Real.log_pos (by norm_num)
  have hl5 : 0 < Real.log 5 := Real.log_pos (by norm_num)
  have e15 : Real.log (15 * (m : ℝ)) = Real.log 3 + Real.log 5 + Real.log m := by
    rw [Real.log_mul (by norm_num) hm0, show (15 : ℝ) = 3 * 5 by norm_num,
      Real.log_mul (by norm_num) (by norm_num)]
  have e10 : Real.log (10 * (m : ℝ)) = Real.log 2 + Real.log 5 + Real.log m := by
    rw [Real.log_mul (by norm_num) hm0, show (10 : ℝ) = 2 * 5 by norm_num,
      Real.log_mul (by norm_num) (by norm_num)]
  have e6 : Real.log (6 * (m : ℝ)) = Real.log 2 + Real.log 3 + Real.log m := by
    rw [Real.log_mul (by norm_num) hm0, show (6 : ℝ) = 2 * 3 by norm_num,
      Real.log_mul (by norm_num) (by norm_num)]
  have e30 : Real.log (30 * (m : ℝ)) = Real.log 2 + Real.log 3 + Real.log 5 + Real.log m := by
    rw [Real.log_mul (by norm_num) hm0, show (30 : ℝ) = 2 * 3 * 5 by norm_num,
      Real.log_mul (by norm_num) (by norm_num), Real.log_mul (by norm_num) (by norm_num)]
  have g30 := log_factorial_ge (n := 30 * m) (by omega)
  have g15 := log_factorial_ge (n := 15 * m) (by omega)
  have g10 := log_factorial_ge (n := 10 * m) (by omega)
  have g6 := log_factorial_ge (n := 6 * m) (by omega)
  have g1 := log_factorial_ge (n := m) (by omega)
  have u30 := log_factorial_le (30 * m) (by omega)
  have u15 := log_factorial_le (15 * m) (by omega)
  have u10 := log_factorial_le (10 * m) (by omega)
  have u6 := log_factorial_le (6 * m) (by omega)
  have u1 := log_factorial_le m hm
  push_cast at g30 g15 g10 g6 u30 u15 u10 u6
  rw [e30] at g30 u30
  rw [e15] at g15 u15
  rw [e10] at g10 u10
  rw [e6] at g6 u6
  unfold b30 A30
  rw [e30]
  constructor <;> nlinarith
end Cheb30
end Gap
end Sext6
end LRSpectrumFull
