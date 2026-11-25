import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Algebra.BigOperators.Intervals

/-!
# Chebyshev's 30-combination, finite-sum core  [2026-11-25]

`psiN n = ∑_{d ≤ n} Λ d`.  `Lf n = ∑_{d ≤ n} Λ d ⌊n/d⌋ = log n!` (Legendre, by induction on `n`).
`b30 m = log (30m)! - log (15m)! - log (10m)! - log (6m)! + log m!` is a finite sum of `Λ d` times the
Chebyshev coefficient `f30c (30m/d) ∈ {0,1}`, equal to `1` when `30m/d ∈ [1,5]`.  Hence

  `psiN (30m) - psiN (5m) ≤ b30 m ≤ psiN (30m)`.

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

/-- `ψ(n) = ∑_{d ≤ n} Λ d`. -/
noncomputable def psiN (n : ℕ) : ℝ := ∑ d ∈ Ioc 0 n, Λ d

theorem psiN_nonneg (n : ℕ) : 0 ≤ psiN n :=
  Finset.sum_nonneg (fun _ _ => ArithmeticFunction.vonMangoldt_nonneg)

theorem psiN_mono {m n : ℕ} (h : m ≤ n) : psiN m ≤ psiN n :=
  Finset.sum_le_sum_of_subset_of_nonneg (Finset.Ioc_subset_Ioc_right h)
    (fun _ _ _ => ArithmeticFunction.vonMangoldt_nonneg)

theorem psiN_sub {m n : ℕ} (h : m ≤ n) : psiN n - psiN m = ∑ d ∈ Ioc m n, Λ d := by
  unfold psiN
  rw [← Finset.sum_Ioc_consecutive _ (Nat.zero_le m) h]
  ring

/-- `∑_{d ≤ N, d ∣ N} Λ d = log N`. -/
theorem sum_dvd_Lambda (N : ℕ) (hN : 0 < N) :
    ∑ d ∈ Ioc 0 N, (if d ∣ N then Λ d else 0) = Real.log (N : ℝ) := by
  rw [← ArithmeticFunction.vonMangoldt_sum, ← Finset.sum_filter]
  apply Finset.sum_congr _ (fun _ _ => rfl)
  ext d
  simp only [Finset.mem_filter, Finset.mem_Ioc, Nat.mem_divisors]
  constructor
  · rintro ⟨_, hd⟩
    exact ⟨hd, hN.ne'⟩
  · rintro ⟨hd, -⟩
    exact ⟨⟨Nat.pos_of_dvd_of_pos hd hN, Nat.le_of_dvd hN hd⟩, hd⟩

/-- `Lf n = ∑_{d ≤ n} Λ d ⌊n/d⌋`. -/
noncomputable def Lf (n : ℕ) : ℝ := ∑ d ∈ Ioc 0 n, Λ d * ((n / d : ℕ) : ℝ)

theorem Lf_succ (n : ℕ) : Lf (n + 1) = Lf n + Real.log ((n + 1 : ℕ) : ℝ) := by
  have h1 : ∀ d ∈ Ioc 0 (n + 1), Λ d * (((n + 1) / d : ℕ) : ℝ) =
      Λ d * ((n / d : ℕ) : ℝ) + (if d ∣ n + 1 then Λ d else 0) := by
    intro d _
    by_cases h : d ∣ n + 1
    · rw [Nat.succ_div_of_dvd h]
      simp [h]
      ring
    · rw [Nat.succ_div_of_not_dvd h]
      simp [h]
  unfold Lf
  rw [Finset.sum_congr rfl h1, Finset.sum_add_distrib, sum_dvd_Lambda (n + 1) (Nat.succ_pos n),
    Finset.sum_Ioc_succ_top (Nat.zero_le n), Nat.div_eq_of_lt (Nat.lt_succ_self n)]
  simp

/-- Legendre: `log n! = ∑_{d ≤ n} Λ d ⌊n/d⌋`. -/
theorem log_factorial_eq (n : ℕ) : Real.log ((n ! : ℕ) : ℝ) = Lf n := by
  induction n with
  | zero => simp [Lf]
  | succ n ih =>
    rw [Lf_succ, ← ih, Nat.factorial_succ, Nat.cast_mul,
      Real.log_mul (Nat.cast_ne_zero.mpr n.succ_ne_zero)
        (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero n))]
    ring

theorem Lf_ext {n N : ℕ} (h : n ≤ N) : Lf n = ∑ d ∈ Ioc 0 N, Λ d * ((n / d : ℕ) : ℝ) := by
  unfold Lf
  apply Finset.sum_subset (Finset.Ioc_subset_Ioc_right h)
  intro d hd hnd
  simp only [Finset.mem_Ioc, not_and, not_le] at hd hnd
  have : n < d := hnd hd.1
  simp [Nat.div_eq_of_lt this]

/-- The Chebyshev coefficient `q + ⌊q/30⌋ - ⌊q/2⌋ - ⌊q/3⌋ - ⌊q/5⌋`. -/
noncomputable def f30c (q : ℕ) : ℝ :=
  ((q + q / 30 : ℕ) : ℝ) - ((q / 2 + q / 3 + q / 5 : ℕ) : ℝ)

theorem f30c_nonneg (q : ℕ) : 0 ≤ f30c q := by
  have h : q / 2 + q / 3 + q / 5 ≤ q + q / 30 := by omega
  have h' : ((q / 2 + q / 3 + q / 5 : ℕ) : ℝ) ≤ ((q + q / 30 : ℕ) : ℝ) := by exact_mod_cast h
  unfold f30c
  linarith

theorem f30c_le_one (q : ℕ) : f30c q ≤ 1 := by
  have h : q + q / 30 ≤ q / 2 + q / 3 + q / 5 + 1 := by omega
  have h' : ((q + q / 30 : ℕ) : ℝ) ≤ ((q / 2 + q / 3 + q / 5 + 1 : ℕ) : ℝ) := by exact_mod_cast h
  unfold f30c
  push_cast at h' ⊢
  linarith

theorem f30c_eq_one (q : ℕ) (h1 : 1 ≤ q) (h6 : q < 6) : f30c q = 1 := by
  have h : q + q / 30 = q / 2 + q / 3 + q / 5 + 1 := by omega
  have h' : ((q + q / 30 : ℕ) : ℝ) = ((q / 2 + q / 3 + q / 5 + 1 : ℕ) : ℝ) := by exact_mod_cast h
  unfold f30c
  push_cast at h' ⊢
  linarith

/-- `b30 m = log (30m)! - log (15m)! - log (10m)! - log (6m)! + log m!`. -/
noncomputable def b30 (m : ℕ) : ℝ :=
  Real.log (((30 * m)! : ℕ) : ℝ) - Real.log (((15 * m)! : ℕ) : ℝ) -
    Real.log (((10 * m)! : ℕ) : ℝ) - Real.log (((6 * m)! : ℕ) : ℝ) + Real.log ((m ! : ℕ) : ℝ)

theorem div_scale (a d k : ℕ) (hk : 0 < k) : (a * k) / d / k = a / d := by
  rw [Nat.div_div_eq_div_mul, mul_comm d k, mul_comm a k, Nat.mul_div_mul_left _ _ hk]

theorem b30_eq (m : ℕ) : b30 m = ∑ d ∈ Ioc 0 (30 * m), Λ d * f30c (30 * m / d) := by
  have h2 : ∀ d, 30 * m / d / 2 = 15 * m / d := fun d => by
    rw [show 30 * m = 15 * m * 2 by ring]; exact div_scale _ _ _ (by norm_num)
  have h3 : ∀ d, 30 * m / d / 3 = 10 * m / d := fun d => by
    rw [show 30 * m = 10 * m * 3 by ring]; exact div_scale _ _ _ (by norm_num)
  have h5 : ∀ d, 30 * m / d / 5 = 6 * m / d := fun d => by
    rw [show 30 * m = 6 * m * 5 by ring]; exact div_scale _ _ _ (by norm_num)
  have h30 : ∀ d, 30 * m / d / 30 = m / d := fun d => by
    rw [show 30 * m = m * 30 by ring]; exact div_scale _ _ _ (by norm_num)
  have key : ∀ d ∈ Ioc 0 (30 * m), Λ d * f30c (30 * m / d) =
      Λ d * ((30 * m / d : ℕ) : ℝ) - Λ d * ((15 * m / d : ℕ) : ℝ) - Λ d * ((10 * m / d : ℕ) : ℝ)
        - Λ d * ((6 * m / d : ℕ) : ℝ) + Λ d * ((m / d : ℕ) : ℝ) := by
    intro d _
    unfold f30c
    rw [h30 d, h2 d, h3 d, h5 d]
    push_cast
    ring
  unfold b30
  rw [log_factorial_eq, log_factorial_eq, log_factorial_eq, log_factorial_eq, log_factorial_eq,
    Lf_ext (by omega : 15 * m ≤ 30 * m), Lf_ext (by omega : 10 * m ≤ 30 * m),
    Lf_ext (by omega : 6 * m ≤ 30 * m), Lf_ext (by omega : m ≤ 30 * m)]
  unfold Lf
  rw [Finset.sum_congr rfl key]
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib]

/-- Upper side of the sandwich. -/
theorem b30_le_psiN (m : ℕ) : b30 m ≤ psiN (30 * m) := by
  rw [b30_eq]
  unfold psiN
  apply Finset.sum_le_sum
  intro d _
  exact mul_le_of_le_one_right ArithmeticFunction.vonMangoldt_nonneg (f30c_le_one _)

/-- Lower side of the sandwich. -/
theorem psiN_sub_le_b30 (m : ℕ) : psiN (30 * m) - psiN (5 * m) ≤ b30 m := by
  rw [psiN_sub (by omega : 5 * m ≤ 30 * m), b30_eq]
  have hsub : ∑ d ∈ Ioc (5 * m) (30 * m), Λ d * f30c (30 * m / d) ≤
      ∑ d ∈ Ioc 0 (30 * m), Λ d * f30c (30 * m / d) :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.Ioc_subset_Ioc_left (Nat.zero_le _))
      (fun d _ _ => mul_nonneg ArithmeticFunction.vonMangoldt_nonneg (f30c_nonneg _))
  refine le_trans (le_of_eq ?_) hsub
  apply Finset.sum_congr rfl
  intro d hd
  rw [Finset.mem_Ioc] at hd
  have hd0 : 0 < d := by omega
  have hq1 : 1 ≤ 30 * m / d := Nat.div_pos hd.2 hd0
  have hq6 : 30 * m / d < 6 := by
    rw [Nat.div_lt_iff_lt_mul hd0]; omega
  rw [f30c_eq_one _ hq1 hq6, mul_one]

end Cheb30
end Gap
end Sext6
end LRSpectrumFull
