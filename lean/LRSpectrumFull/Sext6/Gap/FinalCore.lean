import LRSpectrumFull.Sext6.Gap.CopWinFinal
import LRSpectrumFull.Sext6.Gap.Cheb30Final
import LRSpectrumFull.Sext6.Gap.RobustKAll
import LRSpectrumFull.Sext6.Gap.FinBlk4p0
import LRSpectrumFull.Sext6.Gap.FinBlk5p0
import LRSpectrumFull.Sext6.Gap.FinBlk6p0
import LRSpectrumFull.Sext6.Gap.FinBlk7p0
import LRSpectrumFull.Sext6.Gap.FinBlk8p0
import LRSpectrumFull.Sext6.Gap.FinBlk9p0
import LRSpectrumFull.Sext6.Gap.FinBlk10p0
import LRSpectrumFull.Sext6.Gap.FinBlk11p0
import LRSpectrumFull.Sext6.Gap.FinBlk12p0

/-!
# FinalCore: Theorem S / OE-low / Theorem W with NO `DusartPi`  [2026-11-25]

Everything here is hypothesis-free.  The window `CopWin k N r` (pairwise coprime numbers in `[N+1+r, 2N-1]`, each
coprime to `r`) is obtained from

* the sieve blocks (`RobustKBlk{k}p0`, `FinBlk{k}p0`, `primeWindow7_small`, `windowb{2,3}_small`), kernel-checked, for
  `N*(k) ≤ N ≤ M_k - 1`,
* Chebyshev's 30-combination (`Cheb30Final`) for `N ≥ M_k`, where `M_k` is the exact point from which the hypothesis
  `6 l (T + 3 l + 60) + 1200 ≤ N` (`l = Nat.log 2 N + 2`, `T = 3k(k+1)+1`) holds for every larger `N`.

`M_k` (k = 4..12): 17424, 20304, 23760, 27792, 34656, 40164, 46284, 53016, 60360.

* `copWinT_of_copWinC`, `copWinC_of_copWinT` : `Cheb30.CopWinC` and `CopWinT` are the same predicate.
* `CopWinHypC`, `copWinHypC`                 : the Chebyshev analogue of `CopWinHyp` (its own, larger, threshold), PROVED for every `T`.
  (The old `CopWinHyp T` has the smaller threshold `4 l (T+2l+50)+1100` and is not implied by Cheb30.)
* `cheb_hyp_ge`                               : exact-threshold lemma, any `T`, with a finite table.
* `copWin_table`      : `1 ≤ k ≤ 12`, `N*(k) ≤ N`  ⟹  `CopWin k N r`.
* `copWin_large`      : `N ≥ NCheb k = max 10^5 (67 T²)`, any `k ≥ 1`  ⟹  `CopWin k N r`.
* `ML_ge_S_unconditional`, `cor_a_unconditional`, `ML_ge_robust_unconditional`, `theoremS_unconditional`,
  `OE_low_unconditional`, `theoremW_unconditional`.
No `sorry`, no `axiom`.

Convention: `N` is a natural number (the size of the ambient interval `[1,N]`); `v : Fin (n+1) → ℤ` is an arbitrary finite family of speeds (repetitions allowed) and `n` is not linked to `N`; `k` counts the entries `> N`. Speeds are the moving runners; the runner at rest is not counted, so a vector of `N` speeds means `N + 1` runners and the Lonely Runner value is `1/(N+1)`.
Hypotheses: No hypothesis predicate (`DusartPi`, `CopWinHyp`) occurs in the unconditional statements; the remaining hypotheses are numerical (`N*(k) ≤ N`, `N ≥ NCheb k`, `1 ≤ r`, `2 r ≤ N`).
Axiom audit: covered by `Axioms12` (also reached through the imports of `Axioms17`, `Axioms16`, `Axioms18`) (`#print axioms`; declarations not printed there are bricks of printed ones, so their axioms are bounded by the printed lines).
-/

namespace LRSpectrumFull
namespace Sext6
namespace Gap

/-! ### 1. `CopWinC` is `CopWinT` -/

theorem copWinT_of_copWinC {T N r : ℕ} (h : Cheb30.CopWinC T N r) : CopWinT T N r := by
  obtain ⟨S, hc, hp, hcop⟩ := h
  refine ⟨S, hc, ?_, hcop⟩
  intro D hD
  obtain ⟨h1, h2, h3⟩ := hp D hD
  exact ⟨h1, by omega, h3⟩

theorem copWinC_of_copWinT {T N r : ℕ} (h : CopWinT T N r) : Cheb30.CopWinC T N r := by
  obtain ⟨S, hc, hp, hcop⟩ := h
  refine ⟨S, hc, ?_, hcop⟩
  intro D hD
  obtain ⟨h1, h2, h3⟩ := hp D hD
  exact ⟨h1, by omega, h3⟩

theorem copWinC_iff (T N r : ℕ) : Cheb30.CopWinC T N r ↔ CopWinT T N r :=
  ⟨copWinT_of_copWinC, copWinC_of_copWinT⟩

theorem copWinT_of_cheb_N (T N : ℕ) (hN : 100000 ≤ N) (hT : 67 * T ^ 2 ≤ N) {r : ℕ}
    (hr : 1 ≤ r) (hrN : 2 * r ≤ N) : CopWinT T N r :=
  copWinT_of_copWinC (Cheb30.copWinC_of_cheb_N T N hN hT r hr hrN)

theorem copWinT_of_cheb (T N : ℕ)
    (hN : 6 * (Nat.log 2 N + 2) * (T + 3 * (Nat.log 2 N + 2) + 60) + 1200 ≤ N) {r : ℕ}
    (hr : 1 ≤ r) (hrN : 2 * r ≤ N) : CopWinT T N r :=
  copWinT_of_copWinC (Cheb30.copWinC_of_cheb T N hN r hr hrN)

/-- The Chebyshev analogue of `CopWinHyp` (the hypothesis predicate of the drop-in theorems), with its own threshold. -/
def CopWinHypC (T : ℕ) : Prop :=
  ∀ N r : ℕ, 1 ≤ r →
    6 * (Nat.log 2 N + 2) * (T + 3 * (Nat.log 2 N + 2) + 60) + 1200 ≤ N →
    2 * r ≤ N → CopWinT T N r

/-- `CopWinHypC T` holds for EVERY `T`: no hypothesis. -/
theorem copWinHypC (T : ℕ) : CopWinHypC T :=
  fun _ _ hr hN hrN => copWinT_of_cheb T _ hN hr hrN

/-! ### 2. Exact threshold lemma -/

/-- The Chebyshev hypothesis value at `Nat.log 2 N = j`. -/
def chebG (T j : ℕ) : ℕ := 6 * (j + 2) * (T + 3 * (j + 2) + 60) + 1200

theorem chebG_succ (T j : ℕ) : chebG T (j + 1) ≤ 2 * chebG T j := by
  unfold chebG
  nlinarith [Nat.zero_le (j * T), Nat.zero_le (j * j), Nat.zero_le j, Nat.zero_le T]

theorem chebG_le_pow (T J : ℕ) (h : chebG T J ≤ 2 ^ J) : ∀ j, J ≤ j → chebG T j ≤ 2 ^ j := by
  intro j hj
  induction j, hj using Nat.le_induction with
  | base => exact h
  | succ j hj ih =>
    calc chebG T (j + 1) ≤ 2 * chebG T j := chebG_succ T j
      _ ≤ 2 * 2 ^ j := Nat.mul_le_mul_left 2 ih
      _ = 2 ^ (j + 1) := by ring

/-- If `chebG T J ≤ 2^J` and for every `j < J` either `2^(j+1) ≤ M` or `chebG T j ≤ M`, then the Chebyshev
hypothesis holds for every `N ≥ M`. -/
theorem cheb_hyp_ge (T M J : ℕ) (hJ : chebG T J ≤ 2 ^ J) (hM : 1 ≤ M)
    (htab : ∀ j < J, 2 ^ (j + 1) ≤ M ∨ chebG T j ≤ M) {N : ℕ} (hN : M ≤ N) :
    6 * (Nat.log 2 N + 2) * (T + 3 * (Nat.log 2 N + 2) + 60) + 1200 ≤ N := by
  have hN0 : N ≠ 0 := by omega
  have hpow : 2 ^ Nat.log 2 N ≤ N := Nat.pow_log_le_self 2 hN0
  have hlt : N < 2 ^ (Nat.log 2 N + 1) := Nat.lt_pow_succ_log_self (by norm_num) N
  show chebG T (Nat.log 2 N) ≤ N
  by_cases hj : J ≤ Nat.log 2 N
  · exact (chebG_le_pow T J hJ _ hj).trans hpow
  · rcases htab _ (not_le.mp hj) with h | h
    · exact absurd (hlt.trans_le (h.trans hN)) (lt_irrefl N)
    · exact h.trans hN

theorem copWin_hi {k N r M J : ℕ} (hJ : chebG (3 * k * (k + 1) + 1) J ≤ 2 ^ J) (hM : 1 ≤ M)
    (htab : ∀ j < J, 2 ^ (j + 1) ≤ M ∨ chebG (3 * k * (k + 1) + 1) j ≤ M) (hN : M ≤ N)
    (hr1 : 1 ≤ r) (hr : 2 * r ≤ N) : CopWin k N r :=
  copWinT_of_cheb _ N (cheb_hyp_ge _ M J hJ hM htab hN) hr1 hr

/-! ### 3. The table `1 ≤ k ≤ 12`, `N ≥ N*(k)` -/

theorem copWin_table {k N r : ℕ} (hk1 : 1 ≤ k) (hk2 : k ≤ 12) (hN : Nstar k ≤ N)
    (hr1 : 1 ≤ r) (hr : 2 * r ≤ N) : CopWin k N r := by
  interval_cases k
  · have h : 79 ≤ N := by simpa [Nstar] using hN
    by_cases hb : N ≤ 100000
    · exact copWin_of_primeWin hr1
        (primeWin_of_window (k := 1) (by omega) ((primeWindow7_small h hb) (N / 2) (by omega)) r hr)
    · exact copWinT_of_cheb_N 7 N (by omega) (by norm_num; omega) hr1 hr
  · have h : 222 ≤ N := by simpa [Nstar] using hN
    by_cases hb : N ≤ 100000
    · exact copWin_of_primeWin hr1 (primeWin2_small h hb r hr)
    · exact copWinT_of_cheb_N 19 N (by omega) (by norm_num; omega) hr1 hr
  · have h : 517 ≤ N := by simpa [Nstar] using hN
    by_cases hb : N ≤ 100000
    · exact copWin_of_primeWin hr1 (primeWin3_small h hb r hr)
    · exact copWinT_of_cheb_N 37 N (by omega) (by norm_num; omega) hr1 hr
  · have h : 895 ≤ N := by simpa [Nstar] using hN
    by_cases h1 : N ≤ 1243
    · exact copWin_of_primeWin hr1 (primeWin4_mid h h1 r hr)
    by_cases h2 : N ≤ 17423
    · exact copWin_of_primeWin hr1 (primeWinF4_mid (by omega) h2 r hr)
    · exact copWin_hi (M := 17424) (J := 15) (by decide +kernel) (by norm_num) (by decide +kernel)
        (by omega) hr1 hr
  · have h : 1410 ≤ N := by simpa [Nstar] using hN
    by_cases h1 : N ≤ 1938
    · exact copWin_of_primeWin hr1 (primeWin5_mid h h1 r hr)
    by_cases h2 : N ≤ 20303
    · exact copWin_of_primeWin hr1 (primeWinF5_mid (by omega) h2 r hr)
    · exact copWin_hi (M := 20304) (J := 15) (by decide +kernel) (by norm_num) (by decide +kernel)
        (by omega) hr1 hr
  · have h : 2067 ≤ N := by simpa [Nstar] using hN
    by_cases h1 : N ≤ 2860
    · exact copWin_of_primeWin hr1 (primeWin6_mid h h1 r hr)
    by_cases h2 : N ≤ 23759
    · exact copWin_of_primeWin hr1 (primeWinF6_mid (by omega) h2 r hr)
    · exact copWin_hi (M := 23760) (J := 15) (by decide +kernel) (by norm_num) (by decide +kernel)
        (by omega) hr1 hr
  · have h : 2920 ≤ N := by simpa [Nstar] using hN
    by_cases h1 : N ≤ 3936
    · exact copWin_of_primeWin hr1 (primeWin7_mid h h1 r hr)
    by_cases h2 : N ≤ 27791
    · exact copWin_of_primeWin hr1 (primeWinF7_mid (by omega) h2 r hr)
    · exact copWin_hi (M := 27792) (J := 15) (by decide +kernel) (by norm_num) (by decide +kernel)
        (by omega) hr1 hr
  · have h : 3937 ≤ N := by simpa [Nstar] using hN
    by_cases h1 : N ≤ 5187
    · exact copWin_of_primeWin hr1 (primeWin8_mid h h1 r hr)
    by_cases h2 : N ≤ 34655
    · exact copWin_of_primeWin hr1 (primeWinF8_mid (by omega) h2 r hr)
    · exact copWin_hi (M := 34656) (J := 16) (by decide +kernel) (by norm_num) (by decide +kernel)
        (by omega) hr1 hr
  · have h : 4891 ≤ N := by simpa [Nstar] using hN
    by_cases h1 : N ≤ 6677
    · exact copWin_of_primeWin hr1 (primeWin9_mid h h1 r hr)
    by_cases h2 : N ≤ 40163
    · exact copWin_of_primeWin hr1 (primeWinF9_mid (by omega) h2 r hr)
    · exact copWin_hi (M := 40164) (J := 16) (by decide +kernel) (by norm_num) (by decide +kernel)
        (by omega) hr1 hr
  · have h : 6240 ≤ N := by simpa [Nstar] using hN
    by_cases h1 : N ≤ 8443
    · exact copWin_of_primeWin hr1 (primeWin10_mid h h1 r hr)
    by_cases h2 : N ≤ 46283
    · exact copWin_of_primeWin hr1 (primeWinF10_mid (by omega) h2 r hr)
    · exact copWin_hi (M := 46284) (J := 16) (by decide +kernel) (by norm_num) (by decide +kernel)
        (by omega) hr1 hr
  · have h : 7570 ≤ N := by simpa [Nstar] using hN
    by_cases h1 : N ≤ 10271
    · exact copWin_of_primeWin hr1 (primeWin11_mid h h1 r hr)
    by_cases h2 : N ≤ 53015
    · exact copWin_of_primeWin hr1 (primeWinF11_mid (by omega) h2 r hr)
    · exact copWin_hi (M := 53016) (J := 16) (by decide +kernel) (by norm_num) (by decide +kernel)
        (by omega) hr1 hr
  · have h : 9060 ≤ N := by simpa [Nstar] using hN
    by_cases h1 : N ≤ 12306
    · exact copWin_of_primeWin hr1 (primeWin12_mid h h1 r hr)
    by_cases h2 : N ≤ 60359
    · exact copWin_of_primeWin hr1 (primeWinF12_mid (by omega) h2 r hr)
    · exact copWin_hi (M := 60360) (J := 16) (by decide +kernel) (by norm_num) (by decide +kernel)
        (by omega) hr1 hr

/-! ### 4. Every `k ≥ 1`, large `N` -/

/-- The explicit hypothesis-free threshold for every `k ≥ 1`. -/
def NCheb (k : ℕ) : ℕ := max 100000 (67 * (3 * k * (k + 1) + 1) ^ 2)

theorem copWin_large {k N r : ℕ} (hN : NCheb k ≤ N) (hr1 : 1 ≤ r) (hr : 2 * r ≤ N) :
    CopWin k N r :=
  copWinT_of_cheb_N _ N (le_trans (le_max_left _ _) hN) (le_trans (le_max_right _ _) hN) hr1 hr

/-- **`CopWin k N r`, no hypothesis**: `1 ≤ k ≤ 12` and `N ≥ N*(k)`, or any `k ≥ 1` and `N ≥ NCheb k`. -/
theorem copWin_unconditional {k N r : ℕ} (hk : 1 ≤ k)
    (hN : (k ≤ 12 ∧ Nstar k ≤ N) ∨ NCheb k ≤ N) (hr1 : 1 ≤ r) (hr : 2 * r ≤ N) : CopWin k N r := by
  rcases hN with ⟨h12, hs⟩ | hc
  · exact copWin_table hk h12 hs hr1 hr
  · exact copWin_large hc hr1 hr

/-- **Theorem S (speed-vector form), no hypothesis**, `1 ≤ k ≤ 12`, `N ≥ N*(k)`. -/
theorem ML_ge_S_unconditional {n k N r : ℕ} (hk1 : 1 ≤ k) (hk2 : k ≤ 12) (hN : Nstar k ≤ N)
    (hr1 : 1 ≤ r) (hr : 2 * r ≤ N) (v : Fin (n + 1) → ℤ)
    (hv : ∀ i, (1 ≤ v i ∧ v i ≤ (N : ℤ) ∧ v i ≠ (r : ℤ)) ∨ (N : ℤ) < v i)
    (hcard : (Finset.univ.filter (fun i : Fin (n + 1) => (N : ℤ) < v i)).card ≤ k) :
    1 / (N : ℝ) ≤ ML v :=
  ML_ge_robust_cop hk1 hr1 (copWin_le (copWin_table hk1 hk2 hN hr1 hr))
    (copWin_table hk1 hk2 hN hr1 hr) v hv hcard

/-- **Corollary S'(a), no hypothesis**, `1 ≤ k ≤ 12`, `N ≥ N*(k)`. -/
theorem cor_a_unconditional {n k N : ℕ} (hk1 : 1 ≤ k) (hk2 : k ≤ 12) (hN : Nstar k ≤ N)
    (v : Fin (n + 1) → ℤ) (hpos : ∀ i, 1 ≤ v i)
    (hcard : (Finset.univ.filter (fun i : Fin (n + 1) => (N : ℤ) < v i)).card ≤ k)
    (hML : ML v < 1 / (N : ℝ)) :
    ∀ r : ℕ, 1 ≤ r → 2 * r ≤ N → ∃ i, v i = (r : ℤ) :=
  cor_a_cop hk1 (fun r hr1 hr2 => copWin_table hk1 hk2 hN hr1 hr2) v hpos hcard hML

/-- **Theorem S (speed-vector form), no hypothesis, every `k ≥ 1`**, `N ≥ NCheb k = max 10^5 (67 T²)`,
`T = 3k(k+1)+1`. -/
theorem ML_ge_robust_unconditional {n k N r : ℕ} (hk : 1 ≤ k) (hN : NCheb k ≤ N)
    (hr1 : 1 ≤ r) (hr : 2 * r ≤ N) (v : Fin (n + 1) → ℤ)
    (hv : ∀ i, (1 ≤ v i ∧ v i ≤ (N : ℤ) ∧ v i ≠ (r : ℤ)) ∨ (N : ℤ) < v i)
    (hcard : (Finset.univ.filter (fun i : Fin (n + 1) => (N : ℤ) < v i)).card ≤ k) :
    1 / (N : ℝ) ≤ ML v :=
  ML_ge_robust_cop hk hr1 (copWin_le (copWin_large hN hr1 hr)) (copWin_large hN hr1 hr) v hv hcard

/-- **Theorem S, no hypothesis, every `k ≥ 1`**: `N ≥ N*(k)` for `k ≤ 12`, `N ≥ NCheb k` for every `k`. -/
theorem theoremS_unconditional {n k N r : ℕ} (hk : 1 ≤ k)
    (hN : (k ≤ 12 ∧ Nstar k ≤ N) ∨ NCheb k ≤ N) (hr1 : 1 ≤ r) (hr : 2 * r ≤ N)
    (v : Fin (n + 1) → ℤ)
    (hv : ∀ i, (1 ≤ v i ∧ v i ≤ (N : ℤ) ∧ v i ≠ (r : ℤ)) ∨ (N : ℤ) < v i)
    (hcard : (Finset.univ.filter (fun i : Fin (n + 1) => (N : ℤ) < v i)).card ≤ k) :
    1 / (N : ℝ) ≤ ML v :=
  ML_ge_robust_cop hk hr1 (copWin_le (copWin_unconditional hk hN hr1 hr))
    (copWin_unconditional hk hN hr1 hr) v hv hcard

/-- **Corollary S'(a), no hypothesis, every `k ≥ 1`.** -/
theorem cor_a_robust_unconditional {n k N : ℕ} (hk : 1 ≤ k)
    (hN : (k ≤ 12 ∧ Nstar k ≤ N) ∨ NCheb k ≤ N)
    (v : Fin (n + 1) → ℤ) (hpos : ∀ i, 1 ≤ v i)
    (hcard : (Finset.univ.filter (fun i : Fin (n + 1) => (N : ℤ) < v i)).card ≤ k)
    (hML : ML v < 1 / (N : ℝ)) :
    ∀ r : ℕ, 1 ≤ r → 2 * r ≤ N → ∃ i, v i = (r : ℤ) :=
  cor_a_cop hk (fun r hr1 hr2 => copWin_unconditional hk hN hr1 hr2) v hpos hcard hML

/-! ### 5. OE-low and Theorem W, all `N` -/

theorem OE_low_of_copWin {k N r w : ℕ} (hk : k + 1 = N) (hr1 : 1 ≤ r) (hr : 2 * r ≤ N)
    (hw : N < w) (hP : CopWin 1 N r) : 1 / (N : ℝ) ≤ ML (wFam k r w) := by
  have hrN := copWin_le hP
  refine ML_ge_robust_cop (n := k) (k := 1) (N := N) (r := r) le_rfl hr1 hrN hP (wFam k r w) ?_ ?_
  · intro i
    have hi := i.isLt
    by_cases h : (i : ℕ) + 1 = r
    · right
      rw [wFam_at_r i h]
      exact_mod_cast hw
    · left
      rw [wFam_ne_r i h]
      refine ⟨by push_cast; omega, by push_cast; omega, ?_⟩
      intro he
      apply h
      exact_mod_cast he
  · have hrk : r - 1 < k + 1 := by omega
    have hsub : (Finset.univ.filter (fun i : Fin (k + 1) => (N : ℤ) < wFam k r w i)) ⊆
        {(⟨r - 1, hrk⟩ : Fin (k + 1))} := by
      intro i hi
      have hi' := (Finset.mem_filter.mp hi).2
      simp only [Finset.mem_singleton]
      by_contra hcon
      have a2 : (i : ℕ) + 1 ≠ r := fun h => hcon (Fin.ext (by show (i : ℕ) = r - 1; omega))
      have hlt := i.isLt
      rw [wFam_ne_r i a2] at hi'
      push_cast at hi'
      omega
    exact (Finset.card_le_card hsub).trans (by simp)

/-- **Theorem OE-low, ALL `N ≥ 14`, no hypothesis.** -/
theorem OE_low_unconditional {k N r w : ℕ} (hk : k + 1 = N) (hN : 14 ≤ N)
    (hr1 : 1 ≤ r) (hr : 2 * r ≤ N) (hw : N < w) : 1 / (N : ℝ) ≤ ML (wFam k r w) := by
  by_cases hb : N ≤ 100000
  · exact OE_low_upto hk hN hb hr1 hr hw
  · have hP : CopWin 1 N r := copWinT_of_cheb_N 7 N (by omega) (by norm_num; omega) hr1 hr
    exact OE_low_of_copWin hk hr1 hr hw hP

/-- **Theorem W (`k = 2`), ALL `N ≥ 222`, no hypothesis.** -/
theorem theoremW_unconditional {N r w1 w2 : ℕ} (hN : 222 ≤ N) (hr1 : 1 ≤ r)
    (hr : 2 * r ≤ N) (hw1 : N < w1) (hw2 : N < w2) :
    1 / (N : ℝ) ≤ ML (wFam2 N r w1 w2) := by
  by_cases hb : N ≤ 100000
  · exact theoremW_upto hN hb hr1 hr hw1 hw2
  · have hP : CopWin 2 N r := copWinT_of_cheb_N 19 N (by omega) (by norm_num; omega) hr1 hr
    exact ML_ge_wFam2_cop hr1 hP hw1 hw2

end Gap
end Sext6
end LRSpectrumFull
