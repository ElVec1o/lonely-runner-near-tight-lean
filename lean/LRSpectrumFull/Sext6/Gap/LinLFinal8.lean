import LRSpectrumFull.Sext6.Gap.LinLCount8
import LRSpectrumFull.Sext6.Gap.LinLFinal

/-!
# Theorem L (linear robustness), module 7: the final statements, constant 8  [2026-11-25]

`|F| ≥ 8k+1` pairwise coprime moduli suffice (Stage B: lattice identity, `LinLLattice`, `LinLCount8`).

* `ML_ge_robust_lin8`  : speed-vector form, hypothesis `CopWinT (8k+1) N r`.
* `theoremS_linear`    : hypothesis-free from `ChebCond (8k+1) N` (decidable), every `k ≥ 1`.
* `cor_a_linear`       : Corollary S'(a) in the same range.
* `theoremS_linear_big`: `N ≥ max 10^5 (67 (8k+1)^2)`, no `ChebCond`.
* `MChebLin`, `chebCond_lin8_table`, `theoremS_linear_table` : the exact thresholds `ChebCond (8k+1) N` for all
  `N ≥ MChebLin k`, `1 ≤ k ≤ 40` (certified by `cheb_hyp_ge` and `decide +kernel`).
* `mchebLin_le_mcheb` : `MChebLin k ≤ MCheb k` for `2 ≤ k ≤ 30` (the old `3k(k+1)+1` thresholds).
No `sorry`, no `axiom`.

Convention: `N` is a natural number (the size of the ambient interval `[1,N]`); `v : Fin (n+1) → ℤ` is an arbitrary
finite family of speeds (repetitions allowed); `k` counts the entries `> N`.
Hypotheses: `ChebCond` is a decidable numerical condition; `CopWinT` appears only in `ML_ge_robust_lin8`.
Axiom audit: `Axioms26`.
-/

namespace LRSpectrumFull
namespace Sext6
namespace Gap

/-- **Theorem L (Stage B), speed-vector form.** `CopWinT (8k+1) N r` pairwise coprime moduli in
`[N+1+r, 2N-1]`, each coprime to `r`; entries in `[1,N] \ {r}` or `> N`, at most `k` of the latter:
`1/N ≤ ML v`. -/
theorem ML_ge_robust_lin8 {n k N r : ℕ} (hk : 1 ≤ k) (hr1 : 1 ≤ r) (hr2 : r + 2 ≤ N)
    (hP : CopWinT (8 * k + 1) N r) (v : Fin (n + 1) → ℤ)
    (hv : ∀ i, (1 ≤ v i ∧ v i ≤ (N : ℤ) ∧ v i ≠ (r : ℤ)) ∨ (N : ℤ) < v i)
    (hcard : (Finset.univ.filter (fun i : Fin (n + 1) => (N : ℤ) < v i)).card ≤ k) :
    1 / (N : ℝ) ≤ ML v :=
  ML_ge_robust_linC (by norm_num) (LinL.smallTot_8 N r) hk hr1 hr2 hP v hv hcard

/-- **Theorem S, linear form (the new theorem).**  Every `k ≥ 1`; hypothesis only `ChebCond (8k+1) N`. -/
theorem theoremS_linear {n k N r : ℕ} (hk : 1 ≤ k) (hN : ChebCond (8 * k + 1) N) (hr1 : 1 ≤ r)
    (hr : 2 * r ≤ N) (v : Fin (n + 1) → ℤ)
    (hv : ∀ i, (1 ≤ v i ∧ v i ≤ (N : ℤ) ∧ v i ≠ (r : ℤ)) ∨ (N : ℤ) < v i)
    (hcard : (Finset.univ.filter (fun i : Fin (n + 1) => (N : ℤ) < v i)).card ≤ k) :
    1 / (N : ℝ) ≤ ML v :=
  theoremS_linC (by norm_num) (LinL.smallTot_8 N r) hk hN hr1 hr v hv hcard

/-- **Corollary S'(a), linear form.** -/
theorem cor_a_linear {n k N : ℕ} (hk : 1 ≤ k) (hN : ChebCond (8 * k + 1) N)
    (v : Fin (n + 1) → ℤ) (hpos : ∀ i, 1 ≤ v i)
    (hcard : (Finset.univ.filter (fun i : Fin (n + 1) => (N : ℤ) < v i)).card ≤ k)
    (hML : ML v < 1 / (N : ℝ)) :
    ∀ r : ℕ, 1 ≤ r → 2 * r ≤ N → ∃ i, v i = (r : ℤ) :=
  cor_a_linC (by norm_num) (fun r => LinL.smallTot_8 N r) hk hN v hpos hcard hML

/-- Without `ChebCond`: `N ≥ 10^5` and `67 (8k+1)^2 ≤ N`. -/
theorem theoremS_linear_big {n k N r : ℕ} (hk : 1 ≤ k) (hN1 : 100000 ≤ N)
    (hN2 : 67 * (8 * k + 1) ^ 2 ≤ N) (hr1 : 1 ≤ r)
    (hr : 2 * r ≤ N) (v : Fin (n + 1) → ℤ)
    (hv : ∀ i, (1 ≤ v i ∧ v i ≤ (N : ℤ) ∧ v i ≠ (r : ℤ)) ∨ (N : ℤ) < v i)
    (hcard : (Finset.univ.filter (fun i : Fin (n + 1) => (N : ℤ) < v i)).card ≤ k) :
    1 / (N : ℝ) ≤ ML v := by
  have hP : CopWinT (8 * k + 1) N r := copWinT_of_cheb_N _ N hN1 hN2 hr1 hr
  exact ML_ge_robust_lin8 hk hr1 (copWinT_le (by omega) hP) hP v hv hcard

/-- `MChebLin k`: the least `M` with `ChebCond (8k+1) N` for every `N ≥ M` (`1 ≤ k ≤ 40`; computed by exact
enumeration over the powers of two, certified by `cheb_hyp_ge`). -/
def MChebLin : ℕ → ℕ
  | 1 => 11460
  | 2 => 12180
  | 3 => 12900
  | 4 => 13620
  | 5 => 14340
  | 6 => 15060
  | 7 => 17040
  | 8 => 17808
  | 9 => 18576
  | 10 => 19344
  | 11 => 20112
  | 12 => 20880
  | 13 => 21648
  | 14 => 22416
  | 15 => 23184
  | 16 => 23952
  | 17 => 24720
  | 18 => 25488
  | 19 => 26256
  | 20 => 27024
  | 21 => 27792
  | 22 => 28560
  | 23 => 29328
  | 24 => 30096
  | 25 => 33024
  | 26 => 33840
  | 27 => 34656
  | 28 => 35472
  | 29 => 36288
  | 30 => 37104
  | 31 => 37920
  | 32 => 38736
  | 33 => 39552
  | 34 => 40368
  | 35 => 41184
  | 36 => 42000
  | 37 => 42816
  | 38 => 43632
  | 39 => 44448
  | 40 => 45264
  | _ => 0

theorem chebCond_lin8_table {k N : ℕ} (hk1 : 1 ≤ k) (hk2 : k ≤ 40) (hN : MChebLin k ≤ N) :
    ChebCond (8 * k + 1) N := by
  interval_cases k
  · have h : 11460 ≤ N := by simpa [MChebLin] using hN
    exact cheb_hyp_ge (8 * 1 + 1) 11460 14 (by decide +kernel) (by norm_num) (by decide +kernel) h
  · have h : 12180 ≤ N := by simpa [MChebLin] using hN
    exact cheb_hyp_ge (8 * 2 + 1) 12180 14 (by decide +kernel) (by norm_num) (by decide +kernel) h
  · have h : 12900 ≤ N := by simpa [MChebLin] using hN
    exact cheb_hyp_ge (8 * 3 + 1) 12900 14 (by decide +kernel) (by norm_num) (by decide +kernel) h
  · have h : 13620 ≤ N := by simpa [MChebLin] using hN
    exact cheb_hyp_ge (8 * 4 + 1) 13620 14 (by decide +kernel) (by norm_num) (by decide +kernel) h
  · have h : 14340 ≤ N := by simpa [MChebLin] using hN
    exact cheb_hyp_ge (8 * 5 + 1) 14340 14 (by decide +kernel) (by norm_num) (by decide +kernel) h
  · have h : 15060 ≤ N := by simpa [MChebLin] using hN
    exact cheb_hyp_ge (8 * 6 + 1) 15060 14 (by decide +kernel) (by norm_num) (by decide +kernel) h
  · have h : 17040 ≤ N := by simpa [MChebLin] using hN
    exact cheb_hyp_ge (8 * 7 + 1) 17040 15 (by decide +kernel) (by norm_num) (by decide +kernel) h
  · have h : 17808 ≤ N := by simpa [MChebLin] using hN
    exact cheb_hyp_ge (8 * 8 + 1) 17808 15 (by decide +kernel) (by norm_num) (by decide +kernel) h
  · have h : 18576 ≤ N := by simpa [MChebLin] using hN
    exact cheb_hyp_ge (8 * 9 + 1) 18576 15 (by decide +kernel) (by norm_num) (by decide +kernel) h
  · have h : 19344 ≤ N := by simpa [MChebLin] using hN
    exact cheb_hyp_ge (8 * 10 + 1) 19344 15 (by decide +kernel) (by norm_num) (by decide +kernel) h
  · have h : 20112 ≤ N := by simpa [MChebLin] using hN
    exact cheb_hyp_ge (8 * 11 + 1) 20112 15 (by decide +kernel) (by norm_num) (by decide +kernel) h
  · have h : 20880 ≤ N := by simpa [MChebLin] using hN
    exact cheb_hyp_ge (8 * 12 + 1) 20880 15 (by decide +kernel) (by norm_num) (by decide +kernel) h
  · have h : 21648 ≤ N := by simpa [MChebLin] using hN
    exact cheb_hyp_ge (8 * 13 + 1) 21648 15 (by decide +kernel) (by norm_num) (by decide +kernel) h
  · have h : 22416 ≤ N := by simpa [MChebLin] using hN
    exact cheb_hyp_ge (8 * 14 + 1) 22416 15 (by decide +kernel) (by norm_num) (by decide +kernel) h
  · have h : 23184 ≤ N := by simpa [MChebLin] using hN
    exact cheb_hyp_ge (8 * 15 + 1) 23184 15 (by decide +kernel) (by norm_num) (by decide +kernel) h
  · have h : 23952 ≤ N := by simpa [MChebLin] using hN
    exact cheb_hyp_ge (8 * 16 + 1) 23952 15 (by decide +kernel) (by norm_num) (by decide +kernel) h
  · have h : 24720 ≤ N := by simpa [MChebLin] using hN
    exact cheb_hyp_ge (8 * 17 + 1) 24720 15 (by decide +kernel) (by norm_num) (by decide +kernel) h
  · have h : 25488 ≤ N := by simpa [MChebLin] using hN
    exact cheb_hyp_ge (8 * 18 + 1) 25488 15 (by decide +kernel) (by norm_num) (by decide +kernel) h
  · have h : 26256 ≤ N := by simpa [MChebLin] using hN
    exact cheb_hyp_ge (8 * 19 + 1) 26256 15 (by decide +kernel) (by norm_num) (by decide +kernel) h
  · have h : 27024 ≤ N := by simpa [MChebLin] using hN
    exact cheb_hyp_ge (8 * 20 + 1) 27024 15 (by decide +kernel) (by norm_num) (by decide +kernel) h
  · have h : 27792 ≤ N := by simpa [MChebLin] using hN
    exact cheb_hyp_ge (8 * 21 + 1) 27792 15 (by decide +kernel) (by norm_num) (by decide +kernel) h
  · have h : 28560 ≤ N := by simpa [MChebLin] using hN
    exact cheb_hyp_ge (8 * 22 + 1) 28560 15 (by decide +kernel) (by norm_num) (by decide +kernel) h
  · have h : 29328 ≤ N := by simpa [MChebLin] using hN
    exact cheb_hyp_ge (8 * 23 + 1) 29328 15 (by decide +kernel) (by norm_num) (by decide +kernel) h
  · have h : 30096 ≤ N := by simpa [MChebLin] using hN
    exact cheb_hyp_ge (8 * 24 + 1) 30096 15 (by decide +kernel) (by norm_num) (by decide +kernel) h
  · have h : 33024 ≤ N := by simpa [MChebLin] using hN
    exact cheb_hyp_ge (8 * 25 + 1) 33024 16 (by decide +kernel) (by norm_num) (by decide +kernel) h
  · have h : 33840 ≤ N := by simpa [MChebLin] using hN
    exact cheb_hyp_ge (8 * 26 + 1) 33840 16 (by decide +kernel) (by norm_num) (by decide +kernel) h
  · have h : 34656 ≤ N := by simpa [MChebLin] using hN
    exact cheb_hyp_ge (8 * 27 + 1) 34656 16 (by decide +kernel) (by norm_num) (by decide +kernel) h
  · have h : 35472 ≤ N := by simpa [MChebLin] using hN
    exact cheb_hyp_ge (8 * 28 + 1) 35472 16 (by decide +kernel) (by norm_num) (by decide +kernel) h
  · have h : 36288 ≤ N := by simpa [MChebLin] using hN
    exact cheb_hyp_ge (8 * 29 + 1) 36288 16 (by decide +kernel) (by norm_num) (by decide +kernel) h
  · have h : 37104 ≤ N := by simpa [MChebLin] using hN
    exact cheb_hyp_ge (8 * 30 + 1) 37104 16 (by decide +kernel) (by norm_num) (by decide +kernel) h
  · have h : 37920 ≤ N := by simpa [MChebLin] using hN
    exact cheb_hyp_ge (8 * 31 + 1) 37920 16 (by decide +kernel) (by norm_num) (by decide +kernel) h
  · have h : 38736 ≤ N := by simpa [MChebLin] using hN
    exact cheb_hyp_ge (8 * 32 + 1) 38736 16 (by decide +kernel) (by norm_num) (by decide +kernel) h
  · have h : 39552 ≤ N := by simpa [MChebLin] using hN
    exact cheb_hyp_ge (8 * 33 + 1) 39552 16 (by decide +kernel) (by norm_num) (by decide +kernel) h
  · have h : 40368 ≤ N := by simpa [MChebLin] using hN
    exact cheb_hyp_ge (8 * 34 + 1) 40368 16 (by decide +kernel) (by norm_num) (by decide +kernel) h
  · have h : 41184 ≤ N := by simpa [MChebLin] using hN
    exact cheb_hyp_ge (8 * 35 + 1) 41184 16 (by decide +kernel) (by norm_num) (by decide +kernel) h
  · have h : 42000 ≤ N := by simpa [MChebLin] using hN
    exact cheb_hyp_ge (8 * 36 + 1) 42000 16 (by decide +kernel) (by norm_num) (by decide +kernel) h
  · have h : 42816 ≤ N := by simpa [MChebLin] using hN
    exact cheb_hyp_ge (8 * 37 + 1) 42816 16 (by decide +kernel) (by norm_num) (by decide +kernel) h
  · have h : 43632 ≤ N := by simpa [MChebLin] using hN
    exact cheb_hyp_ge (8 * 38 + 1) 43632 16 (by decide +kernel) (by norm_num) (by decide +kernel) h
  · have h : 44448 ≤ N := by simpa [MChebLin] using hN
    exact cheb_hyp_ge (8 * 39 + 1) 44448 16 (by decide +kernel) (by norm_num) (by decide +kernel) h
  · have h : 45264 ≤ N := by simpa [MChebLin] using hN
    exact cheb_hyp_ge (8 * 40 + 1) 45264 16 (by decide +kernel) (by norm_num) (by decide +kernel) h

/-- **Theorem S, linear form, explicit thresholds `1 ≤ k ≤ 40`.** -/
theorem theoremS_linear_table {n k N r : ℕ} (hk1 : 1 ≤ k) (hk2 : k ≤ 40) (hN : MChebLin k ≤ N)
    (hr1 : 1 ≤ r) (hr : 2 * r ≤ N) (v : Fin (n + 1) → ℤ)
    (hv : ∀ i, (1 ≤ v i ∧ v i ≤ (N : ℤ) ∧ v i ≠ (r : ℤ)) ∨ (N : ℤ) < v i)
    (hcard : (Finset.univ.filter (fun i : Fin (n + 1) => (N : ℤ) < v i)).card ≤ k) :
    1 / (N : ℝ) ≤ ML v :=
  theoremS_linear hk1 (chebCond_lin8_table hk1 hk2 hN) hr1 hr v hv hcard

/-- The linear thresholds are no larger than the old `3k(k+1)+1` thresholds for `2 ≤ k ≤ 30`
(strictly smaller from `k = 3`). -/
theorem mchebLin_le_mcheb : ∀ k < 31, 2 ≤ k → MChebLin k ≤ MCheb k := by
  decide +kernel

theorem mchebLin_lt_mcheb : ∀ k < 31, 3 ≤ k → MChebLin k < MCheb k := by
  decide +kernel

end Gap
end Sext6
end LRSpectrumFull
