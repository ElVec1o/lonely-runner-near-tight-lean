import LRSpectrumFull.Sext6.Gap.Defs

/-!
# Theorem V: bridge from `ML` to statements about the naturals `1..N`  [2026-11-24]

* `nid_exists`   : `‖x‖` is attained as `|x - n|` for some integer `n`.
* `nid_ge_of_int`: a lower bound for all `|x - n|` is a lower bound for `‖x‖`.
* `ML_ge_fam`, `ML_le_fam`: lower / upper bounds for `ML (vFam k r m)` from the two descriptions
  "every speed is far at `t`" / "at every `t` some speed is near".

Convention: `N = k + 1` is the number of speeds of the vector `v : Fin (k+1) → ℤ`. Speeds are the moving runners; the runner at rest is not counted, so a vector of `N` speeds means `N + 1` runners and the Lonely Runner value is `1/(N+1)`.
Hypotheses: those of the individual statements (numerical bounds, structural conditions and, where named in the list above, window predicates such as `PrimeWin`, `CopWin`, `PrimeWindow7`, which later modules discharge for explicit ranges). The unproved predicates `DusartPi`, `LRCHyp`, `CopWinHyp` are not hypotheses of any statement in this module.
Axiom audit: covered by `Axioms` (first); every later audit module imports this module (`#print axioms`; declarations not printed there are bricks of printed ones, so their axioms are bounded by the printed lines).
-/

namespace LRSpectrumFull
namespace Sext6
namespace Gap

theorem nid_exists (x : ℝ) : ∃ n : ℤ, |x - n| = nearestIntDist x := by
  have hf0 := Int.fract_nonneg x
  have hf1 := Int.fract_lt_one x
  have hfl := Int.floor_add_fract x
  rcases le_total (Int.fract x) (1 - Int.fract x) with h | h
  · refine ⟨⌊x⌋, ?_⟩
    have : x - (⌊x⌋ : ℝ) = Int.fract x := by linarith
    rw [this, abs_of_nonneg hf0]
    unfold nearestIntDist
    exact (min_eq_left h).symm
  · refine ⟨⌊x⌋ + 1, ?_⟩
    have : x - (((⌊x⌋ + 1 : ℤ)) : ℝ) = Int.fract x - 1 := by push_cast; linarith
    rw [this, abs_of_nonpos (by linarith)]
    unfold nearestIntDist
    rw [min_eq_right h]
    ring

theorem nid_ge_of_int (x c : ℝ) (h : ∀ n : ℤ, c ≤ |x - n|) : c ≤ nearestIntDist x := by
  obtain ⟨n, hn⟩ := nid_exists x
  rw [← hn]
  exact h n

/-- Lower bound for `ML (vFam k r m)`: all `N = k+1` speeds are at distance `≥ c` at time `t`. -/
theorem ML_ge_fam {k N r m : ℕ} (hk : k + 1 = N) (hr1 : 1 ≤ r) (hr2 : r ≤ N) (c t : ℝ)
    (h1 : ∀ x : ℕ, 1 ≤ x → x ≤ N → x ≠ r → c ≤ nearestIntDist ((x : ℝ) * t))
    (h2 : c ≤ nearestIntDist (((m : ℝ) * r) * t)) : c ≤ ML (vFam k r m) := by
  have hg : c ≤ gap (vFam k r m) t := by
    apply le_gap
    intro i
    by_cases hi : (i : ℕ) + 1 = r
    · have hv : ((vFam k r m i : ℤ) : ℝ) = (m : ℝ) * r := by simp [vFam, hi]
      rw [hv]
      exact h2
    · have hv : ((vFam k r m i : ℤ) : ℝ) = (((i : ℕ) + 1 : ℕ) : ℝ) := by simp [vFam, hi]
      rw [hv]
      exact h1 _ (by omega) (by have := i.isLt; omega) hi
  unfold ML
  exact hg.trans (le_csSup (bddAbove_range_gap _) ⟨t, rfl⟩)

/-- Upper bound for `ML (vFam k r m)`: at every `t` some speed is at distance `≤ c`. -/
theorem ML_le_fam {k N r m : ℕ} (hk : k + 1 = N) (hr1 : 1 ≤ r) (hr2 : r ≤ N) (c : ℝ)
    (h : ∀ t : ℝ, (∃ x : ℕ, 1 ≤ x ∧ x ≤ N ∧ x ≠ r ∧ nearestIntDist ((x : ℝ) * t) ≤ c) ∨
      nearestIntDist (((m : ℝ) * r) * t) ≤ c) : ML (vFam k r m) ≤ c := by
  unfold ML
  apply csSup_le (Set.range_nonempty _)
  rintro y ⟨t, rfl⟩
  rcases h t with ⟨x, hx1, hxN, hxr, hle⟩ | hle
  · obtain ⟨i, hi'⟩ : ∃ i : Fin (k + 1), (i : ℕ) + 1 = x :=
      ⟨⟨x - 1, by omega⟩, by show x - 1 + 1 = x; omega⟩
    have hv : ((vFam k r m i : ℤ) : ℝ) = (x : ℝ) := by simp [vFam, hi', hxr]
    have := gap_le (vFam k r m) t i
    rw [hv] at this
    exact this.trans hle
  · obtain ⟨i, hi'⟩ : ∃ i : Fin (k + 1), (i : ℕ) + 1 = r :=
      ⟨⟨r - 1, by omega⟩, by show r - 1 + 1 = r; omega⟩
    have hv : ((vFam k r m i : ℤ) : ℝ) = (m : ℝ) * r := by simp [vFam, hi']
    have := gap_le (vFam k r m) t i
    rw [hv] at this
    exact this.trans hle

end Gap
end Sext6
end LRSpectrumFull
