import LRSpectrumFull.Sext6.Gap.FinalCore

/-!
# Theorem S via Chebyshev, hypothesis-free from the TRUE Chebyshev threshold  [2026-11-25]

`FinalCore` proves Theorem S hypothesis-free for `k ≤ 12` at `N ≥ N*(k)` and for every `k` at `N ≥ NCheb k =
max 10^5 (67 T²)`.  Here the Chebyshev route is used directly (`copWinT_of_cheb`): the hypothesis of
`Cheb30.copWinC_of_cheb`,

  `ChebCond T N :  6 l (T + 3 l + 60) + 1200 ≤ N`,   `l = Nat.log 2 N + 2`,   `T = 3 k (k+1) + 1`,

is the ONLY condition, for every `k ≥ 1`.

* `ChebCond`, `copWin_cheb`, `theoremS_cheb`, `cor_a_cheb` : every `k ≥ 1`, hypothesis `ChebCond T N` (decidable).
* `copWin_pow`   : `chebG T J ≤ 2^J` and `2^J ≤ N` suffice (explicit witness `J`).
* `MCheb k`      : the EXACT point from which `ChebCond` holds for all larger `N` (`1 ≤ k ≤ 30`), and
  `copWin_cheb_table`, `theoremS_cheb_table`, `cor_a_cheb_table` : `1 ≤ k ≤ 30`, `MCheb k ≤ N`.
* `mcheb_le_ncheb` : `MCheb k ≤ NCheb k` for `1 ≤ k ≤ 30` (stated as `k < 31 → 1 ≤ k → ...`).
No `sorry`, no `axiom`.

Convention: `N` is a natural number (the size of the ambient interval `[1,N]`); `v : Fin (n+1) → ℤ` is an arbitrary finite family of speeds (repetitions allowed) and `n` is not linked to `N`; `k` counts the entries `> N`. Speeds are the moving runners; the runner at rest is not counted, so a vector of `N` speeds means `N + 1` runners and the Lonely Runner value is `1/(N+1)`.
Hypotheses: those of the individual statements (numerical bounds, structural conditions and, where named in the list above, window predicates such as `PrimeWin`, `CopWin`, `PrimeWindow7`, which later modules discharge for explicit ranges). The unproved predicates `DusartPi`, `LRCHyp`, `CopWinHyp` are not hypotheses of any statement in this module.
Axiom audit: covered by `Axioms17` (also reached through the imports of `Axioms18`) (`#print axioms`; declarations not printed there are bricks of printed ones, so their axioms are bounded by the printed lines).
-/

namespace LRSpectrumFull
namespace Sext6
namespace Gap

/-- The Chebyshev hypothesis of `Cheb30.copWinC_of_cheb`. -/
def ChebCond (T N : ℕ) : Prop :=
  6 * (Nat.log 2 N + 2) * (T + 3 * (Nat.log 2 N + 2) + 60) + 1200 ≤ N

instance (T N : ℕ) : Decidable (ChebCond T N) := by unfold ChebCond; infer_instance

theorem copWin_cheb {k N r : ℕ} (h : ChebCond (3 * k * (k + 1) + 1) N)
    (hr1 : 1 ≤ r) (hr : 2 * r ≤ N) : CopWin k N r :=
  copWinT_of_cheb _ N h hr1 hr

/-- **Theorem S, hypothesis-free, every `k ≥ 1`, hypothesis only `ChebCond`.** -/
theorem theoremS_cheb {n k N r : ℕ} (hk : 1 ≤ k) (hN : ChebCond (3 * k * (k + 1) + 1) N)
    (hr1 : 1 ≤ r) (hr : 2 * r ≤ N) (v : Fin (n + 1) → ℤ)
    (hv : ∀ i, (1 ≤ v i ∧ v i ≤ (N : ℤ) ∧ v i ≠ (r : ℤ)) ∨ (N : ℤ) < v i)
    (hcard : (Finset.univ.filter (fun i : Fin (n + 1) => (N : ℤ) < v i)).card ≤ k) :
    1 / (N : ℝ) ≤ ML v :=
  ML_ge_robust_cop hk hr1 (copWin_le (copWin_cheb hN hr1 hr)) (copWin_cheb hN hr1 hr) v hv hcard

/-- **Corollary S'(a), hypothesis-free, every `k ≥ 1`, hypothesis only `ChebCond`.** -/
theorem cor_a_cheb {n k N : ℕ} (hk : 1 ≤ k) (hN : ChebCond (3 * k * (k + 1) + 1) N)
    (v : Fin (n + 1) → ℤ) (hpos : ∀ i, 1 ≤ v i)
    (hcard : (Finset.univ.filter (fun i : Fin (n + 1) => (N : ℤ) < v i)).card ≤ k)
    (hML : ML v < 1 / (N : ℝ)) :
    ∀ r : ℕ, 1 ≤ r → 2 * r ≤ N → ∃ i, v i = (r : ℤ) :=
  cor_a_cop hk (fun _ hr1 hr2 => copWin_cheb hN hr1 hr2) v hpos hcard hML

/-- An explicit power-of-two witness: `chebG T J ≤ 2^J` and `2^J ≤ N`. -/
theorem chebCond_pow {T J N : ℕ} (hJ : chebG T J ≤ 2 ^ J) (hN : 2 ^ J ≤ N) : ChebCond T N :=
  cheb_hyp_ge T (2 ^ J) J hJ (Nat.one_le_two_pow)
    (fun j hj => Or.inl (Nat.pow_le_pow_right (by norm_num) hj)) hN

theorem copWin_pow {k N r J : ℕ} (hJ : chebG (3 * k * (k + 1) + 1) J ≤ 2 ^ J) (hN : 2 ^ J ≤ N)
    (hr1 : 1 ≤ r) (hr : 2 * r ≤ N) : CopWin k N r :=
  copWin_cheb (chebCond_pow hJ hN) hr1 hr

/-! ### The exact thresholds, `1 ≤ k ≤ 30` -/

/-- `MCheb k` is the least `M` such that `ChebCond (3k(k+1)+1) N` holds for EVERY `N ≥ M` (computed by exact brute
force over `N ≤ 2^23` in the accompanying sieve tool, certified below by `cheb_hyp_ge` through `decide +kernel`). -/
def MCheb : ℕ → ℕ
  | 1 => 11280
  | 2 => 12360
  | 3 => 13980
  | 4 => 17424
  | 5 => 20304
  | 6 => 23760
  | 7 => 27792
  | 8 => 34656
  | 9 => 40164
  | 10 => 46284
  | 11 => 53016
  | 12 => 60360
  | 13 => 72588
  | 14 => 81660
  | 15 => 91380
  | 16 => 101748
  | 17 => 112764
  | 18 => 131616
  | 19 => 144612
  | 20 => 158292
  | 21 => 172656
  | 22 => 187704
  | 23 => 203436
  | 24 => 219852
  | 25 => 236952
  | 26 => 268440
  | 27 => 287880
  | 28 => 308040
  | 29 => 328920
  | 30 => 350520
  | _ => 0

theorem copWin_cheb_table {k N r : ℕ} (hk1 : 1 ≤ k) (hk2 : k ≤ 30) (hN : MCheb k ≤ N)
    (hr1 : 1 ≤ r) (hr : 2 * r ≤ N) : CopWin k N r := by
  interval_cases k
  · have h : 11280 ≤ N := by simpa [MCheb] using hN
    exact copWin_hi (M := 11280) (J := 14) (by decide +kernel) (by norm_num) (by decide +kernel) h hr1 hr
  · have h : 12360 ≤ N := by simpa [MCheb] using hN
    exact copWin_hi (M := 12360) (J := 14) (by decide +kernel) (by norm_num) (by decide +kernel) h hr1 hr
  · have h : 13980 ≤ N := by simpa [MCheb] using hN
    exact copWin_hi (M := 13980) (J := 14) (by decide +kernel) (by norm_num) (by decide +kernel) h hr1 hr
  · have h : 17424 ≤ N := by simpa [MCheb] using hN
    exact copWin_hi (M := 17424) (J := 15) (by decide +kernel) (by norm_num) (by decide +kernel) h hr1 hr
  · have h : 20304 ≤ N := by simpa [MCheb] using hN
    exact copWin_hi (M := 20304) (J := 15) (by decide +kernel) (by norm_num) (by decide +kernel) h hr1 hr
  · have h : 23760 ≤ N := by simpa [MCheb] using hN
    exact copWin_hi (M := 23760) (J := 15) (by decide +kernel) (by norm_num) (by decide +kernel) h hr1 hr
  · have h : 27792 ≤ N := by simpa [MCheb] using hN
    exact copWin_hi (M := 27792) (J := 15) (by decide +kernel) (by norm_num) (by decide +kernel) h hr1 hr
  · have h : 34656 ≤ N := by simpa [MCheb] using hN
    exact copWin_hi (M := 34656) (J := 16) (by decide +kernel) (by norm_num) (by decide +kernel) h hr1 hr
  · have h : 40164 ≤ N := by simpa [MCheb] using hN
    exact copWin_hi (M := 40164) (J := 16) (by decide +kernel) (by norm_num) (by decide +kernel) h hr1 hr
  · have h : 46284 ≤ N := by simpa [MCheb] using hN
    exact copWin_hi (M := 46284) (J := 16) (by decide +kernel) (by norm_num) (by decide +kernel) h hr1 hr
  · have h : 53016 ≤ N := by simpa [MCheb] using hN
    exact copWin_hi (M := 53016) (J := 16) (by decide +kernel) (by norm_num) (by decide +kernel) h hr1 hr
  · have h : 60360 ≤ N := by simpa [MCheb] using hN
    exact copWin_hi (M := 60360) (J := 16) (by decide +kernel) (by norm_num) (by decide +kernel) h hr1 hr
  · have h : 72588 ≤ N := by simpa [MCheb] using hN
    exact copWin_hi (M := 72588) (J := 17) (by decide +kernel) (by norm_num) (by decide +kernel) h hr1 hr
  · have h : 81660 ≤ N := by simpa [MCheb] using hN
    exact copWin_hi (M := 81660) (J := 17) (by decide +kernel) (by norm_num) (by decide +kernel) h hr1 hr
  · have h : 91380 ≤ N := by simpa [MCheb] using hN
    exact copWin_hi (M := 91380) (J := 17) (by decide +kernel) (by norm_num) (by decide +kernel) h hr1 hr
  · have h : 101748 ≤ N := by simpa [MCheb] using hN
    exact copWin_hi (M := 101748) (J := 17) (by decide +kernel) (by norm_num) (by decide +kernel) h hr1 hr
  · have h : 112764 ≤ N := by simpa [MCheb] using hN
    exact copWin_hi (M := 112764) (J := 17) (by decide +kernel) (by norm_num) (by decide +kernel) h hr1 hr
  · have h : 131616 ≤ N := by simpa [MCheb] using hN
    exact copWin_hi (M := 131616) (J := 18) (by decide +kernel) (by norm_num) (by decide +kernel) h hr1 hr
  · have h : 144612 ≤ N := by simpa [MCheb] using hN
    exact copWin_hi (M := 144612) (J := 18) (by decide +kernel) (by norm_num) (by decide +kernel) h hr1 hr
  · have h : 158292 ≤ N := by simpa [MCheb] using hN
    exact copWin_hi (M := 158292) (J := 18) (by decide +kernel) (by norm_num) (by decide +kernel) h hr1 hr
  · have h : 172656 ≤ N := by simpa [MCheb] using hN
    exact copWin_hi (M := 172656) (J := 18) (by decide +kernel) (by norm_num) (by decide +kernel) h hr1 hr
  · have h : 187704 ≤ N := by simpa [MCheb] using hN
    exact copWin_hi (M := 187704) (J := 18) (by decide +kernel) (by norm_num) (by decide +kernel) h hr1 hr
  · have h : 203436 ≤ N := by simpa [MCheb] using hN
    exact copWin_hi (M := 203436) (J := 18) (by decide +kernel) (by norm_num) (by decide +kernel) h hr1 hr
  · have h : 219852 ≤ N := by simpa [MCheb] using hN
    exact copWin_hi (M := 219852) (J := 18) (by decide +kernel) (by norm_num) (by decide +kernel) h hr1 hr
  · have h : 236952 ≤ N := by simpa [MCheb] using hN
    exact copWin_hi (M := 236952) (J := 18) (by decide +kernel) (by norm_num) (by decide +kernel) h hr1 hr
  · have h : 268440 ≤ N := by simpa [MCheb] using hN
    exact copWin_hi (M := 268440) (J := 19) (by decide +kernel) (by norm_num) (by decide +kernel) h hr1 hr
  · have h : 287880 ≤ N := by simpa [MCheb] using hN
    exact copWin_hi (M := 287880) (J := 19) (by decide +kernel) (by norm_num) (by decide +kernel) h hr1 hr
  · have h : 308040 ≤ N := by simpa [MCheb] using hN
    exact copWin_hi (M := 308040) (J := 19) (by decide +kernel) (by norm_num) (by decide +kernel) h hr1 hr
  · have h : 328920 ≤ N := by simpa [MCheb] using hN
    exact copWin_hi (M := 328920) (J := 19) (by decide +kernel) (by norm_num) (by decide +kernel) h hr1 hr
  · have h : 350520 ≤ N := by simpa [MCheb] using hN
    exact copWin_hi (M := 350520) (J := 19) (by decide +kernel) (by norm_num) (by decide +kernel) h hr1 hr

/-- **Theorem S, no hypothesis, `1 ≤ k ≤ 30`, all `N ≥ MCheb k`** (the true Chebyshev threshold). -/
theorem theoremS_cheb_table {n k N r : ℕ} (hk1 : 1 ≤ k) (hk2 : k ≤ 30) (hN : MCheb k ≤ N)
    (hr1 : 1 ≤ r) (hr : 2 * r ≤ N) (v : Fin (n + 1) → ℤ)
    (hv : ∀ i, (1 ≤ v i ∧ v i ≤ (N : ℤ) ∧ v i ≠ (r : ℤ)) ∨ (N : ℤ) < v i)
    (hcard : (Finset.univ.filter (fun i : Fin (n + 1) => (N : ℤ) < v i)).card ≤ k) :
    1 / (N : ℝ) ≤ ML v :=
  ML_ge_robust_cop hk1 hr1 (copWin_le (copWin_cheb_table hk1 hk2 hN hr1 hr))
    (copWin_cheb_table hk1 hk2 hN hr1 hr) v hv hcard

/-- **Corollary S'(a), no hypothesis, `1 ≤ k ≤ 30`, all `N ≥ MCheb k`.** -/
theorem cor_a_cheb_table {n k N : ℕ} (hk1 : 1 ≤ k) (hk2 : k ≤ 30) (hN : MCheb k ≤ N)
    (v : Fin (n + 1) → ℤ) (hpos : ∀ i, 1 ≤ v i)
    (hcard : (Finset.univ.filter (fun i : Fin (n + 1) => (N : ℤ) < v i)).card ≤ k)
    (hML : ML v < 1 / (N : ℝ)) :
    ∀ r : ℕ, 1 ≤ r → 2 * r ≤ N → ∃ i, v i = (r : ℤ) :=
  cor_a_cop hk1 (fun _ hr1 hr2 => copWin_cheb_table hk1 hk2 hN hr1 hr2) v hpos hcard hML

/-- The true Chebyshev threshold is below the old `NCheb k = max 10^5 (67 T²)` for `1 ≤ k ≤ 30`. -/
theorem mcheb_le_ncheb : ∀ k : ℕ, k < 31 → 1 ≤ k → MCheb k ≤ NCheb k := by
  decide +kernel

end Gap
end Sext6
end LRSpectrumFull
