import LRSpectrumFull.Sext6.Gap.RobustCorA
import LRSpectrumFull.Sext6.Gap.OEPrimeDusart

/-!
# `PrimeWin k N r` for every `k` from Dusart's explicit bounds  [2026-11-25]

Hypothesis predicate `DusartPi` (as in `OEPrimeDusart.lean`; imported statement, not an axiom).
For `T : ℕ` and `N ≥ 10^5` with `67 T² ≤ N` we prove
`T ≤ #(primes in [N+1+N/2, 2N])`: with `L = ln(3N/2)`, `π(2N) - π(N+N/2) ≥ 3N/(10 L)` and `10 T L ≤ 3 N`
because `ln y ≤ 2 √y` and `√(3N/2) ≥ 10 T`.  Taking `T = 3k(k+1)+1`:

  `N_D(k) = max (10^5, 67 (3k(k+1)+1)^2)`   (so `N_D(2) = 10^5`, `N_D(3) = 10^5`, `N_D(4) = 249307`).

This is quartic in `k` (not the `k² ln k` shape of the sieve+Rosser-Schoenfeld route in the accompanying notes).
* `key_realT`, `log_le_two_sqrt` : real-analysis steps.
* `window_T_of_dusart`           : `DusartPi → 10^5 ≤ N → 67 T² ≤ N → T ≤ #primes in [N+1+N/2, 2N]`.
* `primeWin_of_dusart`           : `DusartPi → 10^5 ≤ N → 67 T_k² ≤ N → ∀ r, 2r ≤ N → PrimeWin k N r`.
No `sorry`, no `axiom`.

Convention: `N` is a natural number (the size of the ambient interval `[1,N]`); `v : Fin (n+1) → ℤ` is an arbitrary finite family of speeds (repetitions allowed) and `n` is not linked to `N`; `k` counts the entries `> N`. Speeds are the moving runners; the runner at rest is not counted, so a vector of `N` speeds means `N + 1` runners and the Lonely Runner value is `1/(N+1)`.
Hypotheses: `DusartPi` (Dusart's explicit prime-counting bounds, an imported statement carried as a `Prop` hypothesis, never an axiom) is a hypothesis only of the declarations whose statements mention it; the unconditional, `_small`, `_upto` and table statements do not use it.
Axiom audit: covered by `Axioms9` (first); every later audit module imports this module (`#print axioms`; declarations not printed there are bricks of printed ones, so their axioms are bounded by the printed lines).
-/

namespace LRSpectrumFull
namespace Sext6
namespace Gap

theorem key_realT {N L M T : ℝ} (hN : 100000 ≤ N) (hL : 11 ≤ L) (hT : T * (10 * L) ≤ 3 * N)
    (hM1 : L ≤ M) (hM2 : M ≤ L + 1 / 3) :
    T ≤ 2 * N / M * (1 + 1 / M) - 3 * N / 2 / L * (1 + (6381 / 5000) / L) := by
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
  have h7 : T ≤ 3 * N / (10 * L) := by
    rw [le_div_iff₀ (by positivity)]
    exact hT
  rw [e1, e2]
  have h5 : 2 * N * ((L + 4 / 3) / (L + 1 / 3) ^ 2) ≤ 2 * N * ((M + 1) / M ^ 2) :=
    mul_le_mul_of_nonneg_left h2 (by positivity)
  have h6 : N * (3 / (10 * L)) ≤
      N * (2 * ((L + 4 / 3) / (L + 1 / 3) ^ 2) - 3 / 2 * ((L + 6381 / 5000) / L ^ 2)) :=
    mul_le_mul_of_nonneg_left hE hN0.le
  have e3 : N * (3 / (10 * L)) = 3 * N / (10 * L) := by ring
  nlinarith [h5, h6, h7, e3]

theorem log_le_two_sqrt {y : ℝ} (hy : 0 < y) : Real.log y ≤ 2 * Real.sqrt y := by
  have hs0 : 0 < Real.sqrt y := Real.sqrt_pos.2 hy
  have hlog : Real.log (Real.sqrt y) = Real.log y / 2 := Real.log_sqrt hy.le
  have hle : Real.log (Real.sqrt y) ≤ Real.sqrt y - 1 := Real.log_le_sub_one_of_pos hs0
  linarith

theorem window_T_of_dusart (hD : DusartPi) {T N : ℕ} (hN : 100000 ≤ N) (hT : 67 * T ^ 2 ≤ N) :
    T ≤ ((Finset.Icc (N + 1 + N / 2) (2 * N)).filter Nat.Prime).card := by
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
  have hTR : (67 : ℝ) * (T : ℝ) ^ 2 ≤ N := by exact_mod_cast hT
  have hT0 : (0 : ℝ) ≤ T := Nat.cast_nonneg T
  have hTL : (T : ℝ) * (10 * Real.log (3 * (N : ℝ) / 2)) ≤ 3 * N := by
    have hy0 : (0 : ℝ) < 3 * N / 2 := by linarith
    have hlg := log_le_two_sqrt hy0
    have hsq : Real.sqrt (3 * (N : ℝ) / 2) ^ 2 = 3 * N / 2 := Real.sq_sqrt hy0.le
    have hs10 : 10 * (T : ℝ) ≤ Real.sqrt (3 * (N : ℝ) / 2) := by
      apply Real.le_sqrt_of_sq_le
      nlinarith
    have hs0 : 0 ≤ Real.sqrt (3 * (N : ℝ) / 2) := Real.sqrt_nonneg _
    have hA := mul_le_mul_of_nonneg_left hlg (by linarith : (0 : ℝ) ≤ 10 * (T : ℝ))
    have hB := mul_le_mul_of_nonneg_right hs10 hs0
    nlinarith [hA, hB, hsq]
  have hc0 : 0 ≤ Real.log (4 / 3) := Real.log_nonneg (by norm_num)
  have hc1 : Real.log (4 / 3) ≤ 1 / 3 := by
    have := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 4 / 3)
    linarith
  have hM : Real.log (2 * (N : ℝ)) = Real.log (3 * (N : ℝ) / 2) + Real.log (4 / 3) := by
    rw [← Real.log_mul (by positivity) (by norm_num)]
    congr 1
    ring
  have hkey := key_realT (N := (N : ℝ)) (L := Real.log (3 * (N : ℝ) / 2))
    (M := Real.log (2 * (N : ℝ))) (T := (T : ℝ)) hNR hL11 hTL (by linarith) (by linarith)
  have hcount := card_primes_Icc (m := N + N / 2) (n := 2 * N) (by omega)
  have e3 : N + N / 2 + 1 = N + 1 + N / 2 := by omega
  rw [e3] at hcount
  have hreal : ((Nat.primeCounting (N + N / 2) : ℕ) : ℝ) + (T : ℝ) ≤
      ((Nat.primeCounting (2 * N) : ℕ) : ℝ) := by linarith
  have hnat : Nat.primeCounting (N + N / 2) + T ≤ Nat.primeCounting (2 * N) := by
    exact_mod_cast hreal
  omega

/-- `PrimeWin k N r` for every `r` with `2 r ≤ N`, from `DusartPi`, once `N ≥ 10^5` and
`67 (3k(k+1)+1)^2 ≤ N`. -/
theorem primeWin_of_dusart (hD : DusartPi) {k N : ℕ} (hN : 100000 ≤ N)
    (hk : 67 * (3 * k * (k + 1) + 1) ^ 2 ≤ N) :
    ∀ r : ℕ, 2 * r ≤ N → PrimeWin k N r :=
  primeWin_of_window (by omega) (window_T_of_dusart hD hN hk)

end Gap
end Sext6
end LRSpectrumFull
