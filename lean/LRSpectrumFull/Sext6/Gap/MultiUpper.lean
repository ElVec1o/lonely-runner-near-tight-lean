import LRSpectrumFull.Sext6.Gap.MultiCore
import LRSpectrumFull.Sext6.Gap.MultiBridge

/-!
# Multi-entry value theorem, upper bound (Dirichlet trapping and assembly)  [2026-11-24]

Let `R` be a finite set of integers, each `r ∈ R` with `N/2 < r ≤ N`, pairwise non-coprime,
`m r ≥ 2`, `β r` the least integer `≥ N+1-r` coprime to `r` (given through `Spec`).
Every speed vector `v` that contains `[1,N] \ R` and the integers `m r * r` (`r ∈ R`) has

  `ML v ≤ τ`   for every `τ ≥ max (1/(N+1)) (max_{r ∈ R} m r / (m r * r + β r))`.

the accompanying notes on the multi-entry value, Theorem M1.  No `sorry`, no `axiom`.

Convention: `N` is the size of the ambient interval `[1,N]`; the speed vector `v : Fin (k+1) → ℤ` is a finite family (repetitions allowed) and `k`, `N` are independent parameters of the generic statements. Speeds are the moving runners; the runner at rest is not counted, so a vector of `N` speeds means `N + 1` runners and the Lonely Runner value is `1/(N+1)`.
Hypotheses: those of the individual statements (numerical bounds, structural conditions and, where named in the list above, window predicates such as `PrimeWin`, `CopWin`, `PrimeWindow7`, which later modules discharge for explicit ranges). The unproved predicates `DusartPi`, `LRCHyp`, `CopWinHyp` are not hypotheses of any statement in this module.
Axiom audit: covered by `MultiAxioms` (also reached through the imports of `Axioms8`) (`#print axioms`; declarations not printed there are bricks of printed ones, so their axioms are bounded by the printed lines).
-/

namespace LRSpectrumFull
namespace Sext6
namespace Gap

theorem multi_ML_le {k N : ℕ} (hN : 2 ≤ N) (R : Finset ℕ) (m β : ℕ → ℕ)
    (hS : ∀ r ∈ R, Spec N r (m r) (β r))
    (hG : ∀ r ∈ R, ∀ r' ∈ R, r' ≠ r → ¬ Nat.Coprime r' r)
    (v : Fin (k + 1) → ℤ)
    (hret : ∀ x : ℕ, 1 ≤ x → x ≤ N → x ∉ R → ∃ i, v i = (x : ℤ))
    (hnew : ∀ r ∈ R, ∃ i, v i = ((m r * r : ℕ) : ℤ))
    (τ : ℝ) (h1 : 1 / ((N : ℝ) + 1) ≤ τ)
    (h2 : ∀ r ∈ R, (m r : ℝ) / ((m r * r + β r : ℕ) : ℝ) ≤ τ) :
    ML v ≤ τ := by
  have hRlt : ∀ r' ∈ R, N < 2 * r' := fun r' h => (hS r' h).hr1
  apply ML_le_of_cover
  intro t
  by_contra hcon
  push Not at hcon
  have hx : ∀ x : ℕ, 1 ≤ x → x ≤ N → x ∉ R → τ < nearestIntDist ((x : ℝ) * t) := by
    intro x hx1 hxN hxR
    obtain ⟨i, hi⟩ := hret x hx1 hxN hxR
    have := hcon i
    have e : ((v i : ℤ) : ℝ) = (x : ℝ) := by rw [hi]; norm_cast
    rwa [e] at this
  obtain ⟨j, q, hq0, hqN, hqd⟩ := Real.exists_int_int_abs_mul_sub_le t (n := N) (by omega)
  obtain ⟨qn, hqn⟩ : ∃ qn : ℕ, (qn : ℤ) = q := ⟨q.toNat, Int.toNat_of_nonneg (by omega)⟩
  have hqnR : (qn : ℝ) = (q : ℝ) := by exact_mod_cast hqn
  have hqnN : qn ≤ N := by
    have : (qn : ℤ) ≤ N := by rw [hqn]; exact_mod_cast hqN
    exact_mod_cast this
  have hqR : qn ∈ R := by
    by_contra hne
    have h3 := hx qn (by omega) hqnN hne
    rw [hqnR] at h3
    have h4 := nearestIntDist_le_dist ((q : ℝ) * t) j
    linarith
  have hSq := hS qn hqR
  have hGq := hG qn hqR
  have hq' : (q : ℝ) = qn := hqnR.symm
  rw [hq'] at hqd
  obtain ⟨hl, hu⟩ := abs_le.mp hqd
  obtain ⟨i, hi⟩ := hnew qn hqR
  have hm : τ < nearestIntDist (((m qn : ℝ) * qn) * t) := by
    have := hcon i
    have e : ((v i : ℤ) : ℝ) = (m qn : ℝ) * qn := by rw [hi]; push_cast; ring
    rwa [e] at this
  rcases le_or_gt 0 ((qn : ℝ) * t - j) with hη | hη
  · exact mcore_false R hRlt hGq hSq τ h1 (h2 qn hqR) t j ((qn : ℝ) * t - j) (by ring) hη hu hx hm
  · refine mcore_false R hRlt hGq hSq τ h1 (h2 qn hqR) (-t) (-j) (-((qn : ℝ) * t - j)) (by push_cast; ring)
      (by linarith) (by linarith) ?_ ?_
    · intro x hx1 hxN hxR
      have := hx x hx1 hxN hxR
      rwa [show (x : ℝ) * (-t) = -((x : ℝ) * t) by ring, nearestIntDist_neg]
    · rwa [show ((m qn : ℝ) * qn) * (-t) = -(((m qn : ℝ) * qn) * t) by ring, nearestIntDist_neg]

end Gap
end Sext6
end LRSpectrumFull
