import LRSpectrumFull.Sext6.Gap.UpperTrap

/-!
# Multi-entry value theorem: generic bounds for `ML` of an arbitrary speed vector  [2026-11-24]

Source: the accompanying notes on the multi-entry value.
* `ML_le_of_cover` : if at every time some speed is within `c` of an integer, `ML v ≤ c`.
* `ML_ge_of_far`   : if at one time every speed is at distance `≥ c`, `c ≤ ML v`.
No `sorry`, no `axiom`.

Convention: `N` is the size of the ambient interval `[1,N]`; the speed vector `v : Fin (k+1) → ℤ` is a finite family (repetitions allowed) and `k`, `N` are independent parameters of the generic statements. Speeds are the moving runners; the runner at rest is not counted, so a vector of `N` speeds means `N + 1` runners and the Lonely Runner value is `1/(N+1)`.
Hypotheses: those of the individual statements (numerical bounds, structural conditions and, where named in the list above, window predicates such as `PrimeWin`, `CopWin`, `PrimeWindow7`, which later modules discharge for explicit ranges). The unproved predicates `DusartPi`, `LRCHyp`, `CopWinHyp` are not hypotheses of any statement in this module.
Axiom audit: covered by `Axioms4` (first); every later audit module imports this module (`#print axioms`; declarations not printed there are bricks of printed ones, so their axioms are bounded by the printed lines).
-/

namespace LRSpectrumFull
namespace Sext6
namespace Gap

theorem ML_le_of_cover {k : ℕ} (v : Fin (k + 1) → ℤ) (c : ℝ)
    (h : ∀ t : ℝ, ∃ i, nearestIntDist ((v i : ℝ) * t) ≤ c) : ML v ≤ c := by
  unfold ML
  apply csSup_le (Set.range_nonempty _)
  rintro y ⟨t, rfl⟩
  obtain ⟨i, hi⟩ := h t
  exact (gap_le v t i).trans hi

theorem ML_ge_of_far {k : ℕ} (v : Fin (k + 1) → ℤ) (c t : ℝ)
    (h : ∀ i, c ≤ nearestIntDist ((v i : ℝ) * t)) : c ≤ ML v := by
  have hg : c ≤ gap v t := le_gap v t c h
  unfold ML
  exact hg.trans (le_csSup (bddAbove_range_gap _) ⟨t, rfl⟩)

end Gap
end Sext6
end LRSpectrumFull
