import LRSpectrumFull.Sext6.Gap.KStarPeak

/-!
# Theorem K*, part 5: the upper bound (U)  [2026-11-25]

Source: the accompanying notes on Theorem K*, section 2 ("Proof of (U)").

`K_upper` : for positive integer speeds `v`, `L = ML v ∈ (0, 1/2]`, `vμ > 0`, with

* (V1) at every equality time `p` there are runners at `+L` and at `-L`, both of speed `≥ vμ`,
* (hL2) every local-maximum value of `gap v` below `L` is `≤ L2`,
* (hDw) `w p ∈ ℤ` at every equality time `p`,

one has `ML (v, w) ≤ max (w L / (w + vμ)) L2`.  No size condition on `w`.
`w_not_mem` : under (hDw), `w` is not a speed of `v`.
No `sorry`, no `axiom`.

Convention: `v : Fin (k+1) → ℤ` has `k + 1` speeds and `(v, w) = Fin.snoc v w` has `k + 2`; for the base `[N]` one has `N = k + 1`. Speeds are the moving runners; the runner at rest is not counted, so a vector of `N` speeds means `N + 1` runners and the Lonely Runner value is `1/(N+1)`.
Hypotheses: those of the individual statements (numerical bounds, structural conditions and, where named in the list above, window predicates such as `PrimeWin`, `CopWin`, `PrimeWindow7`, which later modules discharge for explicit ranges). The unproved predicates `DusartPi`, `LRCHyp`, `CopWinHyp` are not hypotheses of any statement in this module.
Axiom audit: covered by `Axioms15` (also reached through the imports of `Axioms19`, `Axioms20`) (`#print axioms`; declarations not printed there are bricks of printed ones, so their axioms are bounded by the printed lines).
-/

namespace LRSpectrumFull
namespace Sext6
namespace Gap

theorem K_upper {k : ℕ} (v : Fin (k + 1) → ℤ) (hv : ∀ i, 0 < v i) (w : ℤ) (hw : 0 < w)
    (L vμ L2 : ℝ) (hLML : L = ML v) (hL0 : 0 < L) (hL1 : L ≤ 1 / 2) (hvμ : 0 < vμ)
    (hV1 : ∀ p, gap v p = L →
      (∃ i : Fin (k + 1), ∃ n : ℤ, vμ ≤ (v i : ℝ) ∧ (v i : ℝ) * p = n + L) ∧
      (∃ j : Fin (k + 1), ∃ m : ℤ, vμ ≤ (v j : ℝ) ∧ (v j : ℝ) * p = m - L))
    (hL2 : ∀ p, IsLocalMax (gap v) p → gap v p < L → gap v p ≤ L2)
    (hDw : ∀ p, gap v p = L → ∃ z : ℤ, (w : ℝ) * p = z) :
    ML (Fin.snoc v w : Fin (k + 2) → ℤ) ≤ max ((w : ℝ) * L / ((w : ℝ) + vμ)) L2 := by
  have hw' : (0 : ℝ) < w := by exact_mod_cast hw
  have hK0 : 0 < (w : ℝ) * L / ((w : ℝ) + vμ) := div_pos (mul_pos hw' hL0) (by linarith)
  obtain ⟨c, hc⟩ : ∃ c : ℝ, c = max ((w : ℝ) * L / ((w : ℝ) + vμ)) L2 := ⟨_, rfl⟩
  have hKc : (w : ℝ) * L / ((w : ℝ) + vμ) ≤ c := by rw [hc]; exact le_max_left _ _
  have hL2c : L2 ≤ c := by rw [hc]; exact le_max_right _ _
  rw [← hc]
  refine ML_snoc_le_of_peak v w L vμ c hvμ hw hKc ?_
  intro t ht
  obtain ⟨p, hp, hbound⟩ := peak_free v hv L vμ L2 c hLML hL1 hvμ hV1 hL2
    (lt_of_lt_of_le hK0 hKc) hL2c t ht
  exact ⟨p, hDw p hp, hbound⟩

/-- Under `w p ∈ ℤ` at the equality times, `w` is not already a speed. -/
theorem w_not_mem {k : ℕ} (v : Fin (k + 1) → ℤ) (w : ℤ) (L : ℝ) (hLML : L = ML v)
    (hL0 : 0 < L) (hDw : ∀ p, gap v p = L → ∃ z : ℤ, (w : ℝ) * p = z) :
    ∀ i, v i ≠ w := by
  intro i hi
  obtain ⟨p, _, hp⟩ := exists_gap_eq_ML v
  have hp' : gap v p = L := hp.trans hLML.symm
  obtain ⟨z, hz⟩ := hDw p hp'
  have h1 := gap_le v p i
  rw [hi, hz, nearestIntDist_intCast] at h1
  linarith

end Gap
end Sext6
end LRSpectrumFull
