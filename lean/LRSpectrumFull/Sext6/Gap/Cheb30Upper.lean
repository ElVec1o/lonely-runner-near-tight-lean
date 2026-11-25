import LRSpectrumFull.Sext6.Gap.Cheb30Stirling

/-!
# Chebyshev's 30-combination: the telescoped upper bound  [2026-11-25]

For `m ≥ 1`:
  `psiN (30m) ≤ 36 A30 m + (36 A30 + 2 log (30m) + 2) * clog₆ m + 100`.
Strong induction on `m`, step `m ↦ (m+5)/6`, using `psiN(30m) - psiN(5m) ≤ b30 m ≤ 30 A30 m + 2 log(30m) + 2`.
No `sorry`, no `axiom`.

Convention: No speed vector is involved in this module (number theory or real analysis); `N` denotes a natural number, the size of the ambient interval `[1,N]`.
Hypotheses: those of the individual statements (numerical bounds, structural conditions and, where named in the list above, window predicates such as `PrimeWin`, `CopWin`, `PrimeWindow7`, which later modules discharge for explicit ranges). The unproved predicates `DusartPi`, `LRCHyp`, `CopWinHyp` are not hypotheses of any statement in this module.
Axiom audit: covered by `Cheb30Axioms` (first); every later audit module imports this module (`#print axioms`; declarations not printed there are bricks of printed ones, so their axioms are bounded by the printed lines).
-/

open scoped Nat
open Finset

namespace LRSpectrumFull
namespace Sext6
namespace Gap
namespace Cheb30

theorem psiN_upper : ∀ m : ℕ, 1 ≤ m →
    psiN (30 * m) ≤ 36 * A30 * m +
      (36 * A30 + 2 * Real.log (30 * m) + 2) * (Nat.clog 6 m : ℝ) + 100 := by
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    intro hm
    have hA0 : 0 ≤ A30 := by linarith [A30_ge]
    rcases Nat.lt_or_ge m 2 with h1 | h2
    · have hm1 : m = 1 := by omega
      subst hm1
      have := psiN_thirty_le
      simp only [Nat.clog_one_right, Nat.cast_zero, mul_zero, mul_one]
      norm_num at this ⊢
      linarith
    · set m' := (m + 5) / 6 with hm'
      have hm'1 : 1 ≤ m' := by omega
      have hm'lt : m' < m := by omega
      have hrec := ih m' hm'lt hm'1
      have hcl : Nat.clog 6 m = Nat.clog 6 m' + 1 := by
        rw [Nat.clog_of_two_le (by norm_num) h2]
        have : (m + 6 - 1) / 6 = m' := by omega
        rw [this]
      have hb := (b30_bounds m hm).2
      have hs := psiN_sub_le_b30 m
      have hmono : psiN (5 * m) ≤ psiN (30 * m') := psiN_mono (by omega)
      have h6 : (6 : ℝ) * m' ≤ m + 5 := by
        have : 6 * m' ≤ m + 5 := by omega
        exact_mod_cast this
      have hlog : Real.log (30 * (m' : ℝ)) ≤ Real.log (30 * (m : ℝ)) := by
        apply Real.log_le_log
        · have : (0 : ℝ) < m' := by exact_mod_cast hm'1
          positivity
        · have : (m' : ℝ) ≤ m := by exact_mod_cast hm'lt.le
          linarith
      have hC' : (0 : ℝ) ≤ (Nat.clog 6 m' : ℝ) := Nat.cast_nonneg _
      have hAm : A30 * (6 * (m' : ℝ)) ≤ A30 * (m + 5) := mul_le_mul_of_nonneg_left h6 hA0
      have hcC : (36 * A30 + 2 * Real.log (30 * (m' : ℝ)) + 2) * (Nat.clog 6 m' : ℝ) ≤
          (36 * A30 + 2 * Real.log (30 * (m : ℝ)) + 2) * (Nat.clog 6 m' : ℝ) :=
        mul_le_mul_of_nonneg_right (by linarith) hC'
      rw [hcl]
      push_cast
      push_cast at hrec
      nlinarith [hrec, hb, hs, hmono, hAm, hcC]

end Cheb30
end Gap
end Sext6
end LRSpectrumFull
