import LRSpectrumFull.Sext6.Gap.UpperCore
import Mathlib.NumberTheory.DiophantineApproximation.Basic

/-!
# Theorem V, Lemma 4 (upper bound): Dirichlet trapping and assembly  [2026-11-24]

Convention: `N = k + 1` is the number of speeds of the vector `v : Fin (k+1) → ℤ`. Speeds are the moving runners; the runner at rest is not counted, so a vector of `N` speeds means `N + 1` runners and the Lonely Runner value is `1/(N+1)`.
Hypotheses: those of the individual statements (numerical bounds, structural conditions and, where named in the list above, window predicates such as `PrimeWin`, `CopWin`, `PrimeWindow7`, which later modules discharge for explicit ranges). The unproved predicates `DusartPi`, `LRCHyp`, `CopWinHyp` are not hypotheses of any statement in this module.
Axiom audit: covered by `Axioms` (first); every later audit module imports this module (`#print axioms`; declarations not printed there are bricks of printed ones, so their axioms are bounded by the printed lines).
-/

namespace LRSpectrumFull
namespace Sext6
namespace Gap

/-- Lemma 4: `ML ≤ τ` for every `τ ≥ max (1/(N+1)) (m/(m r + β))`. -/
theorem ML_le_tau {k N r m β : ℕ} (hk : k + 1 = N) (hS : Spec N r m β) (τ : ℝ)
    (h1 : 1 / ((N : ℝ) + 1) ≤ τ) (h2 : (m : ℝ) / ((m * r + β : ℕ) : ℝ) ≤ τ) :
    ML (vFam k r m) ≤ τ := by
  have hrr := hS.two_le_r
  have hr2 := hS.hr2
  apply ML_le_fam hk (by omega) hr2
  intro t
  by_contra hcon
  push Not at hcon
  obtain ⟨hx, hm⟩ := hcon
  obtain ⟨j, q, hq0, hqN, hqd⟩ := Real.exists_int_int_abs_mul_sub_le t (n := N) (by omega)
  obtain ⟨qn, hqn⟩ : ∃ qn : ℕ, (qn : ℤ) = q := ⟨q.toNat, Int.toNat_of_nonneg (by omega)⟩
  have hqnR : (qn : ℝ) = (q : ℝ) := by exact_mod_cast hqn
  have hqnN : qn ≤ N := by
    have : (qn : ℤ) ≤ N := by rw [hqn]; exact_mod_cast hqN
    exact_mod_cast this
  have hqr : qn = r := by
    by_contra hne
    have h3 := hx qn (by omega) hqnN hne
    rw [hqnR] at h3
    have h4 := nearestIntDist_le_dist ((q : ℝ) * t) j
    linarith
  have hqr' : (q : ℝ) = r := by rw [← hqnR]; exact_mod_cast hqr
  rw [hqr'] at hqd
  obtain ⟨hl, hu⟩ := abs_le.mp hqd
  rcases le_or_gt 0 ((r : ℝ) * t - j) with hη | hη
  · exact core_false hS τ h1 h2 t j ((r : ℝ) * t - j) (by ring) hη hu hx hm
  · refine core_false hS τ h1 h2 (-t) (-j) (-((r : ℝ) * t - j)) (by push_cast; ring) (by linarith)
      (by linarith) ?_ ?_
    · intro x hx1 hxN hxr
      have := hx x hx1 hxN hxr
      rwa [show (x : ℝ) * (-t) = -((x : ℝ) * t) by ring, nearestIntDist_neg]
    · rwa [show ((m : ℝ) * r) * (-t) = -(((m : ℝ) * r) * t) by ring, nearestIntDist_neg]

end Gap
end Sext6
end LRSpectrumFull
