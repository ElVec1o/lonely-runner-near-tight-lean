import LRSpectrumFull.Sext6.Gap.RobustCorB2
import LRSpectrumFull.Sext6.Gap.RobustCorB3
import LRSpectrumFull.Sext6.Gap.RobustCorD
import LRSpectrumFull.Sext6.Gap.OEPrimeBlocks

/-!
# Theorem W and unconditional instances of Theorem S / Corollary S'  [2026-11-25]

* `primeWin2_small`, `primeWin3_small` : `PrimeWin 2 N r` for `222 ≤ N ≤ 10^5` and `PrimeWin 3 N r` for
  `517 ≤ N ≤ 10^5`, every `r` with `2 r ≤ N`.  UNCONDITIONAL (36 resp. 32 kernel-checked prime blocks).
* `primeWin2_all`, `primeWin3_all` : all `N ≥ 222` resp. `N ≥ 517`, hypothesis `DusartPi` (used only for `N > 10^5`).
* `wFam2`            : the vector `([1,N] \ {r}) ∪ {w1, w2}` on `N + 1` entries.
* `ML_ge_wFam2`      : `PrimeWin 2 N r`, `w1, w2 > N` ⟹ `1/N ≤ ML (wFam2 N r w1 w2)`  (from `ML_ge_robust`).
* `theoremW_upto`    : **Theorem W**, `222 ≤ N ≤ 10^5`, `1 ≤ r`, `2 r ≤ N`: `1/N ≤ ML (wFam2 N r w1 w2)`. UNCONDITIONAL.
* `theoremW_all`     : the same for all `N ≥ 222`, hypothesis `DusartPi`.
* `ML_ge_k2_upto`, `ML_ge_k3_upto` : Theorem S in vector form for `k = 2` (`N ≥ 222`), `k = 3` (`N ≥ 517`),
  `N ≤ 10^5`, UNCONDITIONAL.
* `cor_a_k2_upto`, `cor_a_k3_upto` : Corollary S'(a) in the same ranges.
* `OE_low_via_robust`: consistency check, `k = 1`: the OE-low statement from `PrimeWindow7 N` re-derived from `ML_ge_robust`.
No `sorry`, no `axiom`.

Convention: `N` is a natural number (the size of the ambient interval `[1,N]`); `v : Fin (n+1) → ℤ` is an arbitrary finite family of speeds (repetitions allowed) and `n` is not linked to `N`; `k` counts the entries `> N`. Speeds are the moving runners; the runner at rest is not counted, so a vector of `N` speeds means `N + 1` runners and the Lonely Runner value is `1/(N+1)`.
Hypotheses: `DusartPi` (Dusart's explicit prime-counting bounds, an imported statement carried as a `Prop` hypothesis, never an axiom) is a hypothesis only of the declarations whose statements mention it; the unconditional, `_small`, `_upto` and table statements do not use it.
Axiom audit: covered by `Axioms9` (first); every later audit module imports this module (`#print axioms`; declarations not printed there are bricks of printed ones, so their axioms are bounded by the printed lines).
-/

namespace LRSpectrumFull
namespace Sext6
namespace Gap

theorem primeWin2_small {N : ℕ} (h1 : 222 ≤ N) (h2 : N ≤ 100000) :
    ∀ r : ℕ, 2 * r ≤ N → PrimeWin 2 N r := by
  have h := windowb2_small h1 h2
  exact primeWin_of_window (by omega) (by omega)

theorem primeWin3_small {N : ℕ} (h1 : 517 ≤ N) (h2 : N ≤ 100000) :
    ∀ r : ℕ, 2 * r ≤ N → PrimeWin 3 N r := by
  have h := windowb3_small h1 h2
  exact primeWin_of_window (by omega) (by omega)

theorem primeWin2_all (hD : DusartPi) {N : ℕ} (h1 : 222 ≤ N) :
    ∀ r : ℕ, 2 * r ≤ N → PrimeWin 2 N r := by
  by_cases h : N ≤ 100000
  · exact primeWin2_small h1 h
  · refine primeWin_of_dusart hD (by omega) ?_
    have : 67 * (3 * 2 * (2 + 1) + 1) ^ 2 = 24187 := by norm_num
    omega

theorem primeWin3_all (hD : DusartPi) {N : ℕ} (h1 : 517 ≤ N) :
    ∀ r : ℕ, 2 * r ≤ N → PrimeWin 3 N r := by
  by_cases h : N ≤ 100000
  · exact primeWin3_small h1 h
  · refine primeWin_of_dusart hD (by omega) ?_
    have : 67 * (3 * 3 * (3 + 1) + 1) ^ 2 = 91723 := by norm_num
    omega

/-- The vector `([1,N] \ {r}) ∪ {w1, w2}` on `N + 1` entries: index `i < N` carries `i + 1` except
index `r - 1`, which carries `w1`; index `N` carries `w2`. -/
def wFam2 (N r w1 w2 : ℕ) : Fin (N + 1) → ℤ := fun i =>
  if (i : ℕ) = N then (w2 : ℤ)
  else if (i : ℕ) + 1 = r then (w1 : ℤ) else (((i : ℕ) + 1 : ℕ) : ℤ)

theorem ML_ge_wFam2 {N r w1 w2 : ℕ} (hr1 : 1 ≤ r) (hP : PrimeWin 2 N r)
    (hw1 : N < w1) (hw2 : N < w2) : 1 / (N : ℝ) ≤ ML (wFam2 N r w1 w2) := by
  have hrN := primeWin_le hP
  refine ML_ge_robust (n := N) (k := 2) (N := N) (r := r) (by norm_num) hr1 hrN hP
    (wFam2 N r w1 w2) ?_ ?_
  · intro i
    have hi := i.isLt
    unfold wFam2
    by_cases h1 : (i : ℕ) = N
    · right
      rw [if_pos h1]
      exact_mod_cast hw2
    · rw [if_neg h1]
      by_cases h2 : (i : ℕ) + 1 = r
      · right
        rw [if_pos h2]
        exact_mod_cast hw1
      · left
        rw [if_neg h2]
        refine ⟨by push_cast; omega, by push_cast; omega, ?_⟩
        intro he
        apply h2
        exact_mod_cast he
  · have hrN1 : r - 1 < N + 1 := by omega
    have hsub : (Finset.univ.filter
        (fun i : Fin (N + 1) => (N : ℤ) < wFam2 N r w1 w2 i)) ⊆
        {(⟨N, by omega⟩ : Fin (N + 1)), (⟨r - 1, hrN1⟩ : Fin (N + 1))} := by
      intro i hi
      have hi' := (Finset.mem_filter.mp hi).2
      simp only [Finset.mem_insert, Finset.mem_singleton]
      by_contra hcon
      push Not at hcon
      have a1 : (i : ℕ) ≠ N := fun h => hcon.1 (Fin.ext h)
      have a2 : (i : ℕ) + 1 ≠ r := fun h => hcon.2 (Fin.ext (by show (i : ℕ) = r - 1; omega))
      have hlt := i.isLt
      unfold wFam2 at hi'
      rw [if_neg a1, if_neg a2] at hi'
      push_cast at hi'
      omega
    exact (Finset.card_le_card hsub).trans Finset.card_le_two

/-- **Theorem W** (`k = 2`), unconditional for `222 ≤ N ≤ 10^5`: deleting `r ≤ N/2` from `[N]` and adding two
speeds above `N` leaves `ML ≥ 1/N`. -/
theorem theoremW_upto {N r w1 w2 : ℕ} (hN : 222 ≤ N) (hNb : N ≤ 100000) (hr1 : 1 ≤ r)
    (hr : 2 * r ≤ N) (hw1 : N < w1) (hw2 : N < w2) :
    1 / (N : ℝ) ≤ ML (wFam2 N r w1 w2) :=
  ML_ge_wFam2 hr1 (primeWin2_small hN hNb r hr) hw1 hw2

/-- **Theorem W** (`k = 2`), all `N ≥ 222`, hypothesis `DusartPi` (needed only for `N > 10^5`). -/
theorem theoremW_all (hD : DusartPi) {N r w1 w2 : ℕ} (hN : 222 ≤ N) (hr1 : 1 ≤ r)
    (hr : 2 * r ≤ N) (hw1 : N < w1) (hw2 : N < w2) :
    1 / (N : ℝ) ≤ ML (wFam2 N r w1 w2) :=
  ML_ge_wFam2 hr1 (primeWin2_all hD hN r hr) hw1 hw2

/-- Theorem S, vector form, `k = 2`, unconditional for `222 ≤ N ≤ 10^5`. -/
theorem ML_ge_k2_upto {n N r : ℕ} (hN : 222 ≤ N) (hNb : N ≤ 100000) (hr1 : 1 ≤ r) (hr : 2 * r ≤ N)
    (v : Fin (n + 1) → ℤ)
    (hv : ∀ i, (1 ≤ v i ∧ v i ≤ (N : ℤ) ∧ v i ≠ (r : ℤ)) ∨ (N : ℤ) < v i)
    (hcard : (Finset.univ.filter (fun i : Fin (n + 1) => (N : ℤ) < v i)).card ≤ 2) :
    1 / (N : ℝ) ≤ ML v :=
  ML_ge_robust (by norm_num) hr1 (primeWin_le (primeWin2_small hN hNb r hr)) (primeWin2_small hN hNb r hr)
    v hv hcard

/-- Theorem S, vector form, `k = 3`, unconditional for `517 ≤ N ≤ 10^5`. -/
theorem ML_ge_k3_upto {n N r : ℕ} (hN : 517 ≤ N) (hNb : N ≤ 100000) (hr1 : 1 ≤ r) (hr : 2 * r ≤ N)
    (v : Fin (n + 1) → ℤ)
    (hv : ∀ i, (1 ≤ v i ∧ v i ≤ (N : ℤ) ∧ v i ≠ (r : ℤ)) ∨ (N : ℤ) < v i)
    (hcard : (Finset.univ.filter (fun i : Fin (n + 1) => (N : ℤ) < v i)).card ≤ 3) :
    1 / (N : ℝ) ≤ ML v :=
  ML_ge_robust (by norm_num) hr1 (primeWin_le (primeWin3_small hN hNb r hr)) (primeWin3_small hN hNb r hr)
    v hv hcard

/-- Corollary S'(a), `k = 2`, `222 ≤ N ≤ 10^5`. -/
theorem cor_a_k2_upto {n N : ℕ} (hN : 222 ≤ N) (hNb : N ≤ 100000)
    (v : Fin (n + 1) → ℤ) (hpos : ∀ i, 1 ≤ v i)
    (hcard : (Finset.univ.filter (fun i : Fin (n + 1) => (N : ℤ) < v i)).card ≤ 2)
    (hML : ML v < 1 / (N : ℝ)) :
    ∀ r : ℕ, 1 ≤ r → 2 * r ≤ N → ∃ i, v i = (r : ℤ) :=
  cor_a (by norm_num) (fun r _ hr => primeWin2_small hN hNb r hr) v hpos hcard hML

/-- Corollary S'(a), `k = 3`, `517 ≤ N ≤ 10^5`. -/
theorem cor_a_k3_upto {n N : ℕ} (hN : 517 ≤ N) (hNb : N ≤ 100000)
    (v : Fin (n + 1) → ℤ) (hpos : ∀ i, 1 ≤ v i)
    (hcard : (Finset.univ.filter (fun i : Fin (n + 1) => (N : ℤ) < v i)).card ≤ 3)
    (hML : ML v < 1 / (N : ℝ)) :
    ∀ r : ℕ, 1 ≤ r → 2 * r ≤ N → ∃ i, v i = (r : ℤ) :=
  cor_a (by norm_num) (fun r _ hr => primeWin3_small hN hNb r hr) v hpos hcard hML

/-- Consistency check (`k = 1`): the OE-low window statement re-derived from `ML_ge_robust`
(`3·1·2+1 = 7`).  Same statement as `OE_low_of_window`. -/
theorem OE_low_via_robust {k N r w : ℕ} (hk : k + 1 = N) (hW : PrimeWindow7 N) (hr1 : 1 ≤ r)
    (hr : 2 * r ≤ N) (hw : N < w) : 1 / (N : ℝ) ≤ ML (wFam k r w) := by
  have hP : PrimeWin 1 N r :=
    primeWin_of_window (k := 1) (by omega) (hW (N / 2) (by omega)) r hr
  have hrN := primeWin_le hP
  refine ML_ge_robust (n := k) (k := 1) (N := N) (r := r) le_rfl hr1 hrN hP (wFam k r w) ?_ ?_
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

end Gap
end Sext6
end LRSpectrumFull
