import LRSpectrumFull.Sext6.Gap.RobustCorW
import LRSpectrumFull.Sext6.Gap.RobustKBlk4p0
import LRSpectrumFull.Sext6.Gap.RobustKBlk5p0
import LRSpectrumFull.Sext6.Gap.RobustKBlk6p0
import LRSpectrumFull.Sext6.Gap.RobustKBlk7p0
import LRSpectrumFull.Sext6.Gap.RobustKBlk8p0
import LRSpectrumFull.Sext6.Gap.RobustKBlk9p0
import LRSpectrumFull.Sext6.Gap.RobustKBlk10p0
import LRSpectrumFull.Sext6.Gap.RobustKBlk11p0
import LRSpectrumFull.Sext6.Gap.RobustKBlk12p0

/-!
# PrimeWin for k = 1..12 at EVERY N >= N*(k), from DusartPi alone  [2026-11-25]

`Nstar k` is the exact sieve threshold (last N with pi(2N) - pi(N + N/2) < 3k(k+1)+1, plus one; the accompanying notes section 6,
recomputed by the accompanying sieve tool).  For `Nstar k <= N` the window of `PrimeWin k N r` holds for every `r` with `2 r <= N`:
* k = 1: `primeWindow7_small` (N <= 10^5) and `primeWindow7_of_dusart`;
* k = 2, 3: `primeWin2_all`, `primeWin3_all` (RobustCorW);
* k = 4..12: generated kernel-checked blocks `RobustKBlk{k}p0` for `Nstar k <= N <= N1_k` (UNCONDITIONAL, theorem
  `primeWin{k}_mid`), and for `N >= N1_k` the sharpened discharge `primeWin_of_dusart2` (RobustKGen), with
  `N1_k` found by the tangent bound `ln y <= m - 1 + y/E`, `E <= e^m`.
Consequences: `ML_ge_S_table` (Theorem S, vector form) and `cor_a_table` (Corollary S'(a)) for `1 <= k <= 12`,
`Nstar k <= N`, hypothesis `DusartPi` only.  Unconditional (no `DusartPi`) for k = 4,5,6 on `Nstar k <= N <= N1_k`.
No `sorry`, no `axiom`.

Convention: `N` is a natural number (the size of the ambient interval `[1,N]`); `v : Fin (n+1) → ℤ` is an arbitrary finite family of speeds (repetitions allowed) and `n` is not linked to `N`; `k` counts the entries `> N`. Speeds are the moving runners; the runner at rest is not counted, so a vector of `N` speeds means `N + 1` runners and the Lonely Runner value is `1/(N+1)`.
Hypotheses: `DusartPi` (Dusart's explicit prime-counting bounds, an imported statement carried as a `Prop` hypothesis, never an axiom) is a hypothesis only of the declarations whose statements mention it; the unconditional, `_small`, `_upto` and table statements do not use it.
Axiom audit: covered by `Axioms10` (first); every later audit module imports this module (`#print axioms`; declarations not printed there are bricks of printed ones, so their axioms are bounded by the printed lines).
-/

namespace LRSpectrumFull
namespace Sext6
namespace Gap

/-- Same as `primeWin_of_dusart2`, with the count `T` given as a numeral. -/
theorem primeWin_of_dusart2' (hD : DusartPi) {k N T : ℕ} (hTk : 3 * k * (k + 1) + 1 = T)
    (hN : 732 ≤ N) (hT : (T : ℝ) * (8 * Real.log (3 * (N : ℝ) / 2)) ≤ 3 * N) :
    ∀ r : ℕ, 2 * r ≤ N → PrimeWin k N r := by
  subst hTk
  exact primeWin_of_dusart2 hD hN hT

theorem primeWin1_all (hD : DusartPi) {N : ℕ} (h : 79 ≤ N) :
    ∀ r : ℕ, 2 * r ≤ N → PrimeWin 1 N r := by
  intro r hr
  have hW : PrimeWindow7 N := by
    by_cases hb : N ≤ 100000
    · exact primeWindow7_small h hb
    · exact primeWindow7_of_dusart hD (by omega)
  exact primeWin_of_window (k := 1) (by omega) (hW (N / 2) (by omega)) r hr

theorem primeWin4_hi (hD : DusartPi) {N : ℕ} (hN : 1243 ≤ N) :
    ∀ r : ℕ, 2 * r ≤ N → PrimeWin 4 N r :=
  primeWin_of_dusart2' hD (T := 61) (by norm_num) (by omega)
    (disch_nat (T := 61) (m1 := 7) (E := 2980) (by norm_num) (by norm_num) (by omega) (by omega))

theorem primeWin4_all (hD : DusartPi) {N : ℕ} (hN : 895 ≤ N) :
    ∀ r : ℕ, 2 * r ≤ N → PrimeWin 4 N r := by
  by_cases h : N ≤ 1243
  · exact primeWin4_mid hN h
  · exact primeWin4_hi hD (by omega)

theorem primeWin5_hi (hD : DusartPi) {N : ℕ} (hN : 1938 ≤ N) :
    ∀ r : ℕ, 2 * r ≤ N → PrimeWin 5 N r :=
  primeWin_of_dusart2' hD (T := 91) (by norm_num) (by omega)
    (disch_nat (T := 91) (m1 := 7) (E := 2980) (by norm_num) (by norm_num) (by omega) (by omega))

theorem primeWin5_all (hD : DusartPi) {N : ℕ} (hN : 1410 ≤ N) :
    ∀ r : ℕ, 2 * r ≤ N → PrimeWin 5 N r := by
  by_cases h : N ≤ 1938
  · exact primeWin5_mid hN h
  · exact primeWin5_hi hD (by omega)

theorem primeWin6_hi (hD : DusartPi) {N : ℕ} (hN : 2860 ≤ N) :
    ∀ r : ℕ, 2 * r ≤ N → PrimeWin 6 N r :=
  primeWin_of_dusart2' hD (T := 127) (by norm_num) (by omega)
    (disch_nat (T := 127) (m1 := 7) (E := 2980) (by norm_num) (by norm_num) (by omega) (by omega))

theorem primeWin6_all (hD : DusartPi) {N : ℕ} (hN : 2067 ≤ N) :
    ∀ r : ℕ, 2 * r ≤ N → PrimeWin 6 N r := by
  by_cases h : N ≤ 2860
  · exact primeWin6_mid hN h
  · exact primeWin6_hi hD (by omega)

theorem primeWin7_hi (hD : DusartPi) {N : ℕ} (hN : 3936 ≤ N) :
    ∀ r : ℕ, 2 * r ≤ N → PrimeWin 7 N r :=
  primeWin_of_dusart2' hD (T := 169) (by norm_num) (by omega)
    (disch_nat (T := 169) (m1 := 8) (E := 8103) (by norm_num) (by norm_num) (by omega) (by omega))

theorem primeWin7_all (hD : DusartPi) {N : ℕ} (hN : 2920 ≤ N) :
    ∀ r : ℕ, 2 * r ≤ N → PrimeWin 7 N r := by
  by_cases h : N ≤ 3936
  · exact primeWin7_mid hN h
  · exact primeWin7_hi hD (by omega)

theorem primeWin8_hi (hD : DusartPi) {N : ℕ} (hN : 5187 ≤ N) :
    ∀ r : ℕ, 2 * r ≤ N → PrimeWin 8 N r :=
  primeWin_of_dusart2' hD (T := 217) (by norm_num) (by omega)
    (disch_nat (T := 217) (m1 := 8) (E := 8103) (by norm_num) (by norm_num) (by omega) (by omega))

theorem primeWin8_all (hD : DusartPi) {N : ℕ} (hN : 3937 ≤ N) :
    ∀ r : ℕ, 2 * r ≤ N → PrimeWin 8 N r := by
  by_cases h : N ≤ 5187
  · exact primeWin8_mid hN h
  · exact primeWin8_hi hD (by omega)

theorem primeWin9_hi (hD : DusartPi) {N : ℕ} (hN : 6677 ≤ N) :
    ∀ r : ℕ, 2 * r ≤ N → PrimeWin 9 N r :=
  primeWin_of_dusart2' hD (T := 271) (by norm_num) (by omega)
    (disch_nat (T := 271) (m1 := 8) (E := 8103) (by norm_num) (by norm_num) (by omega) (by omega))

theorem primeWin9_all (hD : DusartPi) {N : ℕ} (hN : 4891 ≤ N) :
    ∀ r : ℕ, 2 * r ≤ N → PrimeWin 9 N r := by
  by_cases h : N ≤ 6677
  · exact primeWin9_mid hN h
  · exact primeWin9_hi hD (by omega)

theorem primeWin10_hi (hD : DusartPi) {N : ℕ} (hN : 8443 ≤ N) :
    ∀ r : ℕ, 2 * r ≤ N → PrimeWin 10 N r :=
  primeWin_of_dusart2' hD (T := 331) (by norm_num) (by omega)
    (disch_nat (T := 331) (m1 := 8) (E := 8103) (by norm_num) (by norm_num) (by omega) (by omega))

theorem primeWin10_all (hD : DusartPi) {N : ℕ} (hN : 6240 ≤ N) :
    ∀ r : ℕ, 2 * r ≤ N → PrimeWin 10 N r := by
  by_cases h : N ≤ 8443
  · exact primeWin10_mid hN h
  · exact primeWin10_hi hD (by omega)

theorem primeWin11_hi (hD : DusartPi) {N : ℕ} (hN : 10271 ≤ N) :
    ∀ r : ℕ, 2 * r ≤ N → PrimeWin 11 N r :=
  primeWin_of_dusart2' hD (T := 397) (by norm_num) (by omega)
    (disch_nat (T := 397) (m1 := 9) (E := 22026) (by norm_num) (by norm_num) (by omega) (by omega))

theorem primeWin11_all (hD : DusartPi) {N : ℕ} (hN : 7570 ≤ N) :
    ∀ r : ℕ, 2 * r ≤ N → PrimeWin 11 N r := by
  by_cases h : N ≤ 10271
  · exact primeWin11_mid hN h
  · exact primeWin11_hi hD (by omega)

theorem primeWin12_hi (hD : DusartPi) {N : ℕ} (hN : 12306 ≤ N) :
    ∀ r : ℕ, 2 * r ≤ N → PrimeWin 12 N r :=
  primeWin_of_dusart2' hD (T := 469) (by norm_num) (by omega)
    (disch_nat (T := 469) (m1 := 9) (E := 22026) (by norm_num) (by norm_num) (by omega) (by omega))

theorem primeWin12_all (hD : DusartPi) {N : ℕ} (hN : 9060 ≤ N) :
    ∀ r : ℕ, 2 * r ≤ N → PrimeWin 12 N r := by
  by_cases h : N ≤ 12306
  · exact primeWin12_mid hN h
  · exact primeWin12_hi hD (by omega)

/-- The sieve thresholds `N*(k)`. -/
def Nstar : ℕ → ℕ
  | 1 => 79
  | 2 => 222
  | 3 => 517
  | 4 => 895
  | 5 => 1410
  | 6 => 2067
  | 7 => 2920
  | 8 => 3937
  | 9 => 4891
  | 10 => 6240
  | 11 => 7570
  | 12 => 9060
  | _ => 0

/-- **`PrimeWin k N r` for `1 ≤ k ≤ 12`, every `N ≥ N*(k)`, every `r` with `2 r ≤ N`: hypothesis `DusartPi` only.** -/
theorem primeWin_table (hD : DusartPi) {k N : ℕ} (hk1 : 1 ≤ k) (hk2 : k ≤ 12)
    (hN : Nstar k ≤ N) : ∀ r : ℕ, 2 * r ≤ N → PrimeWin k N r := by
  interval_cases k
  · have h : 79 ≤ N := by simpa [Nstar] using hN
    exact primeWin1_all hD h
  · have h : 222 ≤ N := by simpa [Nstar] using hN
    exact primeWin2_all hD h
  · have h : 517 ≤ N := by simpa [Nstar] using hN
    exact primeWin3_all hD h
  · have h : 895 ≤ N := by simpa [Nstar] using hN
    exact primeWin4_all hD h
  · have h : 1410 ≤ N := by simpa [Nstar] using hN
    exact primeWin5_all hD h
  · have h : 2067 ≤ N := by simpa [Nstar] using hN
    exact primeWin6_all hD h
  · have h : 2920 ≤ N := by simpa [Nstar] using hN
    exact primeWin7_all hD h
  · have h : 3937 ≤ N := by simpa [Nstar] using hN
    exact primeWin8_all hD h
  · have h : 4891 ≤ N := by simpa [Nstar] using hN
    exact primeWin9_all hD h
  · have h : 6240 ≤ N := by simpa [Nstar] using hN
    exact primeWin10_all hD h
  · have h : 7570 ≤ N := by simpa [Nstar] using hN
    exact primeWin11_all hD h
  · have h : 9060 ≤ N := by simpa [Nstar] using hN
    exact primeWin12_all hD h

/-- **Theorem S** (vector form), `1 ≤ k ≤ 12`, `N ≥ N*(k)`, `1 ≤ r`, `2 r ≤ N`; hypothesis `DusartPi` only. -/
theorem ML_ge_S_table (hD : DusartPi) {n k N r : ℕ} (hk1 : 1 ≤ k) (hk2 : k ≤ 12)
    (hN : Nstar k ≤ N) (hr1 : 1 ≤ r) (hr : 2 * r ≤ N) (v : Fin (n + 1) → ℤ)
    (hv : ∀ i, (1 ≤ v i ∧ v i ≤ (N : ℤ) ∧ v i ≠ (r : ℤ)) ∨ (N : ℤ) < v i)
    (hcard : (Finset.univ.filter (fun i : Fin (n + 1) => (N : ℤ) < v i)).card ≤ k) :
    1 / (N : ℝ) ≤ ML v :=
  ML_ge_robust hk1 hr1 (primeWin_le (primeWin_table hD hk1 hk2 hN r hr))
    (primeWin_table hD hk1 hk2 hN r hr) v hv hcard

/-- **Corollary S'(a)**, `1 ≤ k ≤ 12`, `N ≥ N*(k)`; hypothesis `DusartPi` only. -/
theorem cor_a_table (hD : DusartPi) {n k N : ℕ} (hk1 : 1 ≤ k) (hk2 : k ≤ 12) (hN : Nstar k ≤ N)
    (v : Fin (n + 1) → ℤ) (hpos : ∀ i, 1 ≤ v i)
    (hcard : (Finset.univ.filter (fun i : Fin (n + 1) => (N : ℤ) < v i)).card ≤ k)
    (hML : ML v < 1 / (N : ℝ)) :
    ∀ r : ℕ, 1 ≤ r → 2 * r ≤ N → ∃ i, v i = (r : ℤ) :=
  cor_a hk1 (fun r _ hr => primeWin_table hD hk1 hk2 hN r hr) v hpos hcard hML

/-- Theorem S, vector form, `k = 4`, UNCONDITIONAL for `895 ≤ N ≤ 1243`. -/
theorem ML_ge_k4_mid {n N r : ℕ} (hN : 895 ≤ N) (hNb : N ≤ 1243) (hr1 : 1 ≤ r) (hr : 2 * r ≤ N)
    (v : Fin (n + 1) → ℤ)
    (hv : ∀ i, (1 ≤ v i ∧ v i ≤ (N : ℤ) ∧ v i ≠ (r : ℤ)) ∨ (N : ℤ) < v i)
    (hcard : (Finset.univ.filter (fun i : Fin (n + 1) => (N : ℤ) < v i)).card ≤ 4) :
    1 / (N : ℝ) ≤ ML v :=
  ML_ge_robust (by norm_num) hr1 (primeWin_le (primeWin4_mid hN hNb r hr)) (primeWin4_mid hN hNb r hr)
    v hv hcard

/-- Theorem S, vector form, `k = 5`, UNCONDITIONAL for `1410 ≤ N ≤ 1938`. -/
theorem ML_ge_k5_mid {n N r : ℕ} (hN : 1410 ≤ N) (hNb : N ≤ 1938) (hr1 : 1 ≤ r) (hr : 2 * r ≤ N)
    (v : Fin (n + 1) → ℤ)
    (hv : ∀ i, (1 ≤ v i ∧ v i ≤ (N : ℤ) ∧ v i ≠ (r : ℤ)) ∨ (N : ℤ) < v i)
    (hcard : (Finset.univ.filter (fun i : Fin (n + 1) => (N : ℤ) < v i)).card ≤ 5) :
    1 / (N : ℝ) ≤ ML v :=
  ML_ge_robust (by norm_num) hr1 (primeWin_le (primeWin5_mid hN hNb r hr)) (primeWin5_mid hN hNb r hr)
    v hv hcard

/-- Theorem S, vector form, `k = 6`, UNCONDITIONAL for `2067 ≤ N ≤ 2860`. -/
theorem ML_ge_k6_mid {n N r : ℕ} (hN : 2067 ≤ N) (hNb : N ≤ 2860) (hr1 : 1 ≤ r) (hr : 2 * r ≤ N)
    (v : Fin (n + 1) → ℤ)
    (hv : ∀ i, (1 ≤ v i ∧ v i ≤ (N : ℤ) ∧ v i ≠ (r : ℤ)) ∨ (N : ℤ) < v i)
    (hcard : (Finset.univ.filter (fun i : Fin (n + 1) => (N : ℤ) < v i)).card ≤ 6) :
    1 / (N : ℝ) ≤ ML v :=
  ML_ge_robust (by norm_num) hr1 (primeWin_le (primeWin6_mid hN hNb r hr)) (primeWin6_mid hN hNb r hr)
    v hv hcard

end Gap
end Sext6
end LRSpectrumFull
