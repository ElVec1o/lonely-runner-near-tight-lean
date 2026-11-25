import LRSpectrumFull.Sext6.Gap.CopWinCore
import LRSpectrumFull.Sext6.Gap.RobustCorW
import LRSpectrumFull.Sext6.Gap.OEAll

/-!
# CopWin, step 4: the drop-in replacement for `DusartPi`  [2026-11-25]

`CopWinHyp T` is the target of the Chebyshev route (to be proved in the separate `Cheb30*.lean` files; NOT proved
here, it is a hypothesis predicate, never an axiom):

  for every `N`, `1 ≤ r`, `2 r ≤ N` with `4 l (T + 2 l + 50) + 1100 ≤ N`, `l = Nat.log 2 N + 2`,
  there are `T` pairwise coprime numbers in `[N+1+r, 2N-1]`, each coprime to `r`.

(`1 ≤ r` is part of the hypothesis: for `r = 0` the statement is false, only `1` is coprime to `0`.)

* `hyp_bound`            : `T ≤ 100`, `N ≥ 10^5` imply the numerical hypothesis of `CopWinHyp`.
* `ML_ge_robust_all_cop` : Theorem S (vector form), all `k ≥ 1`, all large `N`; hypothesis `CopWinHyp (3k(k+1)+1)` only.
* `cor_a_all_cop`        : Corollary S'(a) in the same range.
* `OE_low_all_cop`       : Theorem OE-low, all `N ≥ 14`; hypothesis `CopWinHyp 7` (used only for `N > 10^5`).
* `theoremW_all_cop`     : Theorem W, all `N ≥ 222`; hypothesis `CopWinHyp 19` (used only for `N > 10^5`).
For `N ≤ 10^5` the existing unconditional results are used.  No `sorry`, no `axiom`.

Convention: `N` is a natural number (the size of the ambient interval `[1,N]`); `v : Fin (n+1) → ℤ` is an arbitrary finite family of speeds (repetitions allowed) and `n` is not linked to `N`; `k` counts the entries `> N`. Speeds are the moving runners; the runner at rest is not counted, so a vector of `N` speeds means `N + 1` runners and the Lonely Runner value is `1/(N+1)`.
Hypotheses: `CopWinHyp T` is a `Prop` hypothesis predicate that is not proved in this module (the Chebyshev route proves its own variant `CopWinHypC` in `FinalCore`, with a larger threshold); `DusartPi` is mentioned only in the title and docstring.
Axiom audit: covered by `CopWinAxioms11` (first); every later audit module imports this module (`#print axioms`; declarations not printed there are bricks of printed ones, so their axioms are bounded by the printed lines).
-/

namespace LRSpectrumFull
namespace Sext6
namespace Gap

/-- The Chebyshev-route target: a coprime window of size `T` for every `r` once `N` is large enough. -/
def CopWinHyp (T : ℕ) : Prop :=
  ∀ N r : ℕ, 1 ≤ r →
    4 * (Nat.log 2 N + 2) * (T + 2 * (Nat.log 2 N + 2) + 50) + 1100 ≤ N →
    2 * r ≤ N → CopWinT T N r

theorem pow_ge_sq (L : ℕ) (h : 16 ≤ L) : 100 * (L + 2) ^ 2 ≤ 2 ^ L := by
  induction L, h using Nat.le_induction with
  | base => norm_num
  | succ L hL ih =>
    have h1 : 100 * (L + 1 + 2) ^ 2 ≤ 2 * (100 * (L + 2) ^ 2) := by nlinarith
    calc 100 * (L + 1 + 2) ^ 2 ≤ 2 * (100 * (L + 2) ^ 2) := h1
      _ ≤ 2 * 2 ^ L := Nat.mul_le_mul_left 2 ih
      _ = 2 ^ (L + 1) := by ring

/-- For `N ≥ 10^5` and `T ≤ 100` the numerical hypothesis of `CopWinHyp T` holds. -/
theorem hyp_bound {T N : ℕ} (hT : T ≤ 100) (hN : 100000 ≤ N) :
    4 * (Nat.log 2 N + 2) * (T + 2 * (Nat.log 2 N + 2) + 50) + 1100 ≤ N := by
  have hL16 : 16 ≤ Nat.log 2 N :=
    Nat.le_log_of_pow_le (by norm_num) (by norm_num; omega)
  have hpow : 2 ^ Nat.log 2 N ≤ N := Nat.pow_log_le_self 2 (by omega)
  have hsq := pow_ge_sq _ hL16
  generalize Nat.log 2 N = L at *
  have h1 : (L + 2) * T ≤ (L + 2) * 100 := Nat.mul_le_mul_left (L + 2) hT
  nlinarith [h1, hsq, hpow, hL16]

/-- **Theorem S (speed-vector form), all `N` large, hypothesis `CopWinHyp` only.** -/
theorem ML_ge_robust_all_cop {n k N r : ℕ} (hk : 1 ≤ k) (hC : CopWinHyp (3 * k * (k + 1) + 1))
    (hr1 : 1 ≤ r) (hr : 2 * r ≤ N)
    (hN : 4 * (Nat.log 2 N + 2) * ((3 * k * (k + 1) + 1) + 2 * (Nat.log 2 N + 2) + 50) + 1100 ≤ N)
    (v : Fin (n + 1) → ℤ)
    (hv : ∀ i, (1 ≤ v i ∧ v i ≤ (N : ℤ) ∧ v i ≠ (r : ℤ)) ∨ (N : ℤ) < v i)
    (hcard : (Finset.univ.filter (fun i : Fin (n + 1) => (N : ℤ) < v i)).card ≤ k) :
    1 / (N : ℝ) ≤ ML v := by
  have hP : CopWin k N r := hC N r hr1 hN hr
  exact ML_ge_robust_cop hk hr1 (copWin_le hP) hP v hv hcard

/-- **Corollary S'(a), all `N` large, hypothesis `CopWinHyp` only.** -/
theorem cor_a_all_cop {n k N : ℕ} (hk : 1 ≤ k) (hC : CopWinHyp (3 * k * (k + 1) + 1))
    (hN : 4 * (Nat.log 2 N + 2) * ((3 * k * (k + 1) + 1) + 2 * (Nat.log 2 N + 2) + 50) + 1100 ≤ N)
    (v : Fin (n + 1) → ℤ) (hpos : ∀ i, 1 ≤ v i)
    (hcard : (Finset.univ.filter (fun i : Fin (n + 1) => (N : ℤ) < v i)).card ≤ k)
    (hML : ML v < 1 / (N : ℝ)) :
    ∀ r : ℕ, 1 ≤ r → 2 * r ≤ N → ∃ i, v i = (r : ℤ) :=
  cor_a_cop hk (fun r hr1 hr2 => hC N r hr1 hN hr2) v hpos hcard hML

/-- **Theorem OE-low, all `N ≥ 14`**, hypothesis `CopWinHyp 7` (used only for `N > 10^5`). -/
theorem OE_low_all_cop (hC : CopWinHyp 7) {k N r w : ℕ} (hk : k + 1 = N) (hN : 14 ≤ N)
    (hr1 : 1 ≤ r) (hr : 2 * r ≤ N) (hw : N < w) : 1 / (N : ℝ) ≤ ML (wFam k r w) := by
  by_cases hb : N ≤ 100000
  · exact OE_low_upto hk hN hb hr1 hr hw
  · have hP7 : CopWinT 7 N r := hC N r hr1 (hyp_bound (by norm_num) (by omega)) hr
    have hP : CopWin 1 N r := copWinT_mono (by norm_num) hP7
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

theorem ML_ge_wFam2_cop {N r w1 w2 : ℕ} (hr1 : 1 ≤ r) (hP : CopWin 2 N r)
    (hw1 : N < w1) (hw2 : N < w2) : 1 / (N : ℝ) ≤ ML (wFam2 N r w1 w2) := by
  have hrN := copWin_le hP
  refine ML_ge_robust_cop (n := N) (k := 2) (N := N) (r := r) (by norm_num) hr1 hrN hP
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

/-- **Theorem W (`k = 2`), all `N ≥ 222`**, hypothesis `CopWinHyp 19` (used only for `N > 10^5`). -/
theorem theoremW_all_cop (hC : CopWinHyp 19) {N r w1 w2 : ℕ} (hN : 222 ≤ N) (hr1 : 1 ≤ r)
    (hr : 2 * r ≤ N) (hw1 : N < w1) (hw2 : N < w2) :
    1 / (N : ℝ) ≤ ML (wFam2 N r w1 w2) := by
  by_cases hb : N ≤ 100000
  · exact theoremW_upto hN hb hr1 hr hw1 hw2
  · have hP19 : CopWinT 19 N r := hC N r hr1 (hyp_bound (by norm_num) (by omega)) hr
    have hP : CopWin 2 N r := copWinT_mono (by norm_num) hP19
    exact ML_ge_wFam2_cop hr1 hP hw1 hw2

end Gap
end Sext6
end LRSpectrumFull
