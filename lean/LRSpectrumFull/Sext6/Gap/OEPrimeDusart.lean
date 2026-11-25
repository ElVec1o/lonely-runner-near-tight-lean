import LRSpectrumFull.Sext6.Gap.OEPrimeCore
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Algebra.Order.Floor.Semifield

/-!
# Theorem OE-low, prime window for `N > 10^5` from Dusart's explicit bounds  [2026-11-24]

`DusartPi` is the (only) imported statement: Dusart, "Estimates of some functions over primes without R.H.",
arXiv:1002.0442v1, Theorem 6.9, inequality (6.5), with `π(x) = π(⌊x⌋)`:

  `x ≥ 599  ⟹  x/ln x (1 + 1/ln x) ≤ π(x)`,     `x > 1  ⟹  π(x) ≤ x/ln x (1 + 1.2762/ln x)`.

It is a HYPOTHESIS predicate (a `def` of type `Prop`), not an axiom; no theorem here asserts it.

From `DusartPi` we prove `PrimeWindow7 N` for every `N ≥ 10^5` (closed form, no scan):
with `L = ln(3N/2)`, `ln(2N) ≤ L + 1/3`, the difference `π(2N) - π(N + N/2)` is at least `3N/(10 L) ≥ 7.2`
because `L ≥ 11` (from `e < 2.7182818286`) and `24 L ≤ N` (from `ln y ≤ 2 √y`).

* `g_mono`, `key_real`, `log_ge_11`, `log_le_lin` : the real-analysis steps.
* `primeWindow7_of_dusart` : `DusartPi → 10^5 ≤ N → PrimeWindow7 N`.
No `sorry`, no `axiom`.

Convention: No speed vector is involved in this module (number theory or real analysis); `N` denotes a natural number, the size of the ambient interval `[1,N]`.
Hypotheses: `DusartPi` (Dusart's explicit prime-counting bounds, an imported statement carried as a `Prop` hypothesis, never an axiom) is a hypothesis only of the declarations whose statements mention it; the unconditional, `_small`, `_upto` and table statements do not use it.
Axiom audit: covered by `Axioms6` (first); every later audit module imports this module (`#print axioms`; declarations not printed there are bricks of printed ones, so their axioms are bounded by the printed lines).
-/

namespace LRSpectrumFull
namespace Sext6
namespace Gap

/-- Dusart (arXiv 1002.0442v1, Thm 6.9, (6.5)), as a hypothesis predicate; `1.2762 = 6381/5000`. -/
def DusartPi : Prop :=
  (∀ x : ℝ, 599 ≤ x →
      x / Real.log x * (1 + 1 / Real.log x) ≤ (Nat.primeCounting ⌊x⌋₊ : ℝ)) ∧
  (∀ x : ℝ, 1 < x →
      (Nat.primeCounting ⌊x⌋₊ : ℝ) ≤ x / Real.log x * (1 + (6381 / 5000) / Real.log x))

theorem g_mono {M M' : ℝ} (h0 : 0 < M) (h1 : M ≤ M') :
    (M' + 1) / M' ^ 2 ≤ (M + 1) / M ^ 2 := by
  have h0' : 0 < M' := lt_of_lt_of_le h0 h1
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  nlinarith [mul_nonneg (mul_nonneg h0.le h0'.le) (sub_nonneg.2 h1),
    mul_nonneg (add_pos h0 h0').le (sub_nonneg.2 h1)]

theorem key_real {N L M : ℝ} (hN : 100000 ≤ N) (hL : 11 ≤ L) (hLN : 24 * L ≤ N)
    (hM1 : L ≤ M) (hM2 : M ≤ L + 1 / 3) :
    7 ≤ 2 * N / M * (1 + 1 / M) - 3 * N / 2 / L * (1 + (6381 / 5000) / L) := by
  have hL0 : 0 < L := by linarith
  have hM0 : 0 < M := by linarith
  have hN0 : 0 < N := by linarith
  have hu : L + 1 / 3 ≠ 0 := by positivity
  have hv : 3 * L + 1 ≠ 0 := by positivity
  have e1 : 2 * N / M * (1 + 1 / M) = 2 * N * ((M + 1) / M ^ 2) := by
    field_simp
  have e2 : 3 * N / 2 / L * (1 + (6381 / 5000) / L)
      = 3 * N / 2 * ((L + 6381 / 5000) / L ^ 2) := by
    field_simp
  have h2 : (L + 4 / 3) / (L + 1 / 3) ^ 2 ≤ (M + 1) / M ^ 2 := by
    have h := g_mono hM0 hM2
    have e : L + 1 / 3 + 1 = L + 4 / 3 := by ring
    rwa [e] at h
  have hs : 0 ≤ L - 11 := by linarith
  have hpoly : 0 ≤ 18000 * L ^ 3 - 40287 * L ^ 2 - 132858 * L - 19143 := by
    have e : 18000 * L ^ 3 - 40287 * L ^ 2 - 132858 * L - 19143
        = 18000 * (L - 11) ^ 3 + 553713 * (L - 11) ^ 2 + 5514828 * (L - 11) + 17602692 := by ring
    rw [e]
    have h3 := pow_nonneg hs 3
    have h2' := pow_nonneg hs 2
    linarith
  have hE : 3 / (10 * L) ≤
      2 * ((L + 4 / 3) / (L + 1 / 3) ^ 2) - 3 / 2 * ((L + 6381 / 5000) / L ^ 2) := by
    rw [← sub_nonneg]
    have e : 2 * ((L + 4 / 3) / (L + 1 / 3) ^ 2) - 3 / 2 * ((L + 6381 / 5000) / L ^ 2)
        - 3 / (10 * L)
        = (18000 * L ^ 3 - 40287 * L ^ 2 - 132858 * L - 19143)
          / (10000 * L ^ 2 * (3 * L + 1) ^ 2) := by
      field_simp
      ring
    rw [e]
    exact div_nonneg hpoly (by positivity)
  have h7 : 7 ≤ 3 * N / (10 * L) := by
    rw [le_div_iff₀ (by positivity)]
    linarith
  rw [e1, e2]
  have h5 : 2 * N * ((L + 4 / 3) / (L + 1 / 3) ^ 2) ≤ 2 * N * ((M + 1) / M ^ 2) :=
    mul_le_mul_of_nonneg_left h2 (by positivity)
  have h6 : N * (3 / (10 * L)) ≤
      N * (2 * ((L + 4 / 3) / (L + 1 / 3) ^ 2) - 3 / 2 * ((L + 6381 / 5000) / L ^ 2)) :=
    mul_le_mul_of_nonneg_left hE hN0.le
  have e3 : N * (3 / (10 * L)) = 3 * N / (10 * L) := by ring
  nlinarith [h5, h6, h7, e3]

theorem log_ge_11 {y : ℝ} (hy : 150000 ≤ y) : 11 ≤ Real.log y := by
  have hy0 : 0 < y := by linarith
  rw [Real.le_log_iff_exp_le hy0]
  have h1 : Real.exp 1 < 2.7182818286 := Real.exp_one_lt_d9
  have h2 : Real.exp 11 = Real.exp 1 ^ 11 := by
    have := Real.exp_nat_mul 1 11
    simpa using this
  rw [h2]
  have h3 : Real.exp 1 ^ 11 ≤ (2.7182818286 : ℝ) ^ 11 :=
    pow_le_pow_left₀ (Real.exp_pos 1).le h1.le 11
  have h4 : (2.7182818286 : ℝ) ^ 11 ≤ 150000 := by norm_num
  linarith

theorem log_le_lin {y : ℝ} (hy : 5184 ≤ y) : 24 * Real.log y ≤ 2 * y / 3 := by
  have hy0 : 0 < y := by linarith
  have hs0 : 0 < Real.sqrt y := Real.sqrt_pos.2 hy0
  have hss : Real.sqrt y ^ 2 = y := Real.sq_sqrt hy0.le
  have hlog : Real.log (Real.sqrt y) = Real.log y / 2 := Real.log_sqrt hy0.le
  have hle : Real.log (Real.sqrt y) ≤ Real.sqrt y - 1 := Real.log_le_sub_one_of_pos hs0
  have hs72 : 72 ≤ Real.sqrt y := by
    by_contra h
    push Not at h
    nlinarith
  nlinarith

theorem primeWindow7_of_dusart (hD : DusartPi) {N : ℕ} (hN : 100000 ≤ N) : PrimeWindow7 N := by
  apply window_mono
  obtain ⟨hlow, hup⟩ := hD
  have hNR : (100000 : ℝ) ≤ N := by exact_mod_cast hN
  have hx1 : (599 : ℝ) ≤ 2 * N := by linarith
  have hlo := hlow (2 * N) hx1
  have hf1 : ⌊(2 * (N : ℝ))⌋₊ = 2 * N := by
    have : (2 * (N : ℝ)) = ((2 * N : ℕ) : ℝ) := by push_cast; ring
    rw [this, Nat.floor_natCast]
  rw [hf1] at hlo
  have hx2 : (1 : ℝ) < 3 * N / 2 := by linarith
  have hu := hup (3 * N / 2) hx2
  have hf2 : ⌊(3 * (N : ℝ) / 2)⌋₊ = N + N / 2 := by
    have : (3 * (N : ℝ) / 2) = ((3 * N : ℕ) : ℝ) / ((2 : ℕ) : ℝ) := by push_cast; ring
    rw [this, Nat.floor_div_eq_div]
    omega
  rw [hf2] at hu
  have hy : (150000 : ℝ) ≤ 3 * N / 2 := by linarith
  have hL11 : 11 ≤ Real.log (3 * (N : ℝ) / 2) := log_ge_11 hy
  have hLN : 24 * Real.log (3 * (N : ℝ) / 2) ≤ N := by
    have := log_le_lin (by linarith : (5184 : ℝ) ≤ 3 * (N : ℝ) / 2)
    linarith
  have hc0 : 0 ≤ Real.log (4 / 3) := Real.log_nonneg (by norm_num)
  have hc1 : Real.log (4 / 3) ≤ 1 / 3 := by
    have := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 4 / 3)
    linarith
  have hM : Real.log (2 * (N : ℝ)) = Real.log (3 * (N : ℝ) / 2) + Real.log (4 / 3) := by
    rw [← Real.log_mul (by positivity) (by norm_num)]
    congr 1
    ring
  have hkey := key_real (N := (N : ℝ)) (L := Real.log (3 * (N : ℝ) / 2))
    (M := Real.log (2 * (N : ℝ))) hNR hL11 hLN (by linarith) (by linarith)
  have hcount := card_primes_Icc (m := N + N / 2) (n := 2 * N) (by omega)
  have e3 : N + N / 2 + 1 = N + 1 + N / 2 := by omega
  rw [e3] at hcount
  have hreal : ((Nat.primeCounting (N + N / 2) : ℕ) : ℝ) + 7 ≤
      ((Nat.primeCounting (2 * N) : ℕ) : ℝ) := by linarith
  have hnat : Nat.primeCounting (N + N / 2) + 7 ≤ Nat.primeCounting (2 * N) := by
    exact_mod_cast hreal
  omega

end Gap
end Sext6
end LRSpectrumFull
