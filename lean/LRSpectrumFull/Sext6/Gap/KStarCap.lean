import LRSpectrumFull.Sext6.Gap.MultiBridge

/-!
# Theorem K* (feasibility probe), part 1: the pointwise cap and the peak assembly  [2026-11-25]

Source: the accompanying notes on Theorem K*, Lemma 3 (`cap_bound`) and the assembly of (U)
from a peak lemma (section 10, "How (U) assembles via ML_le_of_cover").

* `cap_bound_gen` : `e ≤ L - v |x|` implies `min e ‖w x‖ ≤ w L / (w + v)`.  Hypotheses: only `0 < v`, `0 < w`.
  (The draft's hypotheses `0 < L ≤ 1/2` are NOT needed: `‖w x‖ ≤ w |x|` holds for every `x`, so the split is
  `|x| ≤ L/(w+v)` versus `|x| > L/(w+v)`.)
* `cap_bound` : the statement exactly as in the accompanying notes section 10 (with the integrality of `w * t0`).
* `ML_snoc_le_of_peak` : the mechanism of (U): if every time `t` with `c < gap v t` has a peak `p` with `w p ∈ ℤ`
  and `gap v t ≤ L - vμ |t - p|`, and `w L / (w + vμ) ≤ c`, then `ML (v, w) ≤ c`.
No `sorry`, no `axiom`.

Convention: `v : Fin (k+1) → ℤ` has `k + 1` speeds and `(v, w) = Fin.snoc v w` has `k + 2`; for the base `[N]` one has `N = k + 1`. Speeds are the moving runners; the runner at rest is not counted, so a vector of `N` speeds means `N + 1` runners and the Lonely Runner value is `1/(N+1)`.
Hypotheses: those of the individual statements (numerical bounds, structural conditions and, where named in the list above, window predicates such as `PrimeWin`, `CopWin`, `PrimeWindow7`, which later modules discharge for explicit ranges). The unproved predicates `DusartPi`, `LRCHyp`, `CopWinHyp` are not hypotheses of any statement in this module.
Axiom audit: covered by `Axioms14` (also reached through the imports of `Axioms15`, `Axioms19`, `Axioms20`) (`#print axioms`; declarations not printed there are bricks of printed ones, so their axioms are bounded by the printed lines).
-/

namespace LRSpectrumFull
namespace Sext6
namespace Gap

/-- Lemma 3 (pointwise cap), minimal hypotheses. -/
theorem cap_bound_gen (L v w e x : ℝ) (hv : 0 < v) (hw : 0 < w)
    (he : e ≤ L - v * |x|) :
    min e (nearestIntDist (w * x)) ≤ w * L / (w + v) := by
  have hwv : 0 < w + v := by linarith
  have hq : L / (w + v) * (w + v) = L := div_mul_cancel₀ L hwv.ne'
  rw [mul_div_assoc]
  by_cases hx : |x| ≤ L / (w + v)
  · have h1 : nearestIntDist (w * x) ≤ |w * x| := by
      have := nearestIntDist_le_dist (w * x) 0
      simpa using this
    have h2 : |w * x| = w * |x| := by rw [abs_mul, abs_of_pos hw]
    have h3 : w * |x| ≤ w * (L / (w + v)) := mul_le_mul_of_nonneg_left hx hw.le
    calc min e (nearestIntDist (w * x)) ≤ nearestIntDist (w * x) := min_le_right _ _
      _ ≤ |w * x| := h1
      _ = w * |x| := h2
      _ ≤ w * (L / (w + v)) := h3
  · have hx' : L / (w + v) < |x| := not_le.mp hx
    have h4 : v * (L / (w + v)) < v * |x| := mul_lt_mul_of_pos_left hx' hv
    calc min e (nearestIntDist (w * x)) ≤ e := min_le_left _ _
      _ ≤ L - v * |x| := he
      _ ≤ w * (L / (w + v)) := by nlinarith [hq]

/-- Lemma 3 shifted to a time `t0` at which `w * t0` is an integer (no size hypotheses on `L`). -/
theorem cap_shift (L v w e t t0 : ℝ) (hv : 0 < v) (hw : 0 < w)
    (hw0 : ∃ z : ℤ, w * t0 = z) (he : e ≤ L - v * |t - t0|) :
    min e (nearestIntDist (w * t)) ≤ w * L / (w + v) := by
  obtain ⟨z, hz⟩ := hw0
  have hshift : nearestIntDist (w * t) = nearestIntDist (w * (t - t0)) := by
    have h : w * t = w * (t - t0) + (z : ℝ) := by rw [← hz]; ring
    rw [h, nearestIntDist_add_int]
  rw [hshift]
  exact cap_bound_gen L v w e (t - t0) hv hw he

/-- **`cap_bound`**, as stated in the accompanying notes section 10: `w t0 ∈ ℤ`, `e ≤ L - v |t - t0|` with `0 < L ≤ 1/2`,
`0 < v`, `0 < w` give `min e ‖w t‖ ≤ w L / (w + v)`. (`hL0`, `hL` are not used.) -/
theorem cap_bound (L v w e t t0 : ℝ) (_hL0 : 0 < L) (_hL : L ≤ 1 / 2) (hv : 0 < v) (hw : 0 < w)
    (hw0 : ∃ z : ℤ, w * t0 = z) (he : e ≤ L - v * |t - t0|) :
    min e (nearestIntDist (w * t)) ≤ w * L / (w + v) :=
  cap_shift L v w e t t0 hv hw hw0 he

/-- The mechanism of (U): adding the speed `w` (which is an integer at every peak) to `v` cuts every peak
of `gap v` down to `w L / (w + vμ)`.  The peak hypothesis `hpeak` is the content of Lemma 2'' of the accompanying notes. -/
theorem ML_snoc_le_of_peak {k : ℕ} (v : Fin (k + 1) → ℤ) (w : ℤ) (L vμ c : ℝ)
    (hv : 0 < vμ) (hw : 0 < w) (hK : (w : ℝ) * L / ((w : ℝ) + vμ) ≤ c)
    (hpeak : ∀ t : ℝ, c < gap v t →
      ∃ p : ℝ, (∃ z : ℤ, (w : ℝ) * p = z) ∧ gap v t ≤ L - vμ * |t - p|) :
    ML (Fin.snoc v w : Fin (k + 2) → ℤ) ≤ c := by
  apply ML_le_of_cover
  intro t
  by_contra hcon
  have hcon' : ∀ i : Fin (k + 2), c < nearestIntDist (((Fin.snoc v w : Fin (k + 2) → ℤ) i : ℝ) * t) := by
    intro i
    exact not_le.mp (fun h => hcon ⟨i, h⟩)
  have hg : c < gap v t := by
    unfold gap
    rw [Finset.lt_inf'_iff]
    intro i _
    have h := hcon' (Fin.castSucc i)
    simpa [Fin.snoc_castSucc] using h
  have hwt : c < nearestIntDist ((w : ℝ) * t) := by
    have h := hcon' (Fin.last (k + 1))
    simpa [Fin.snoc_last] using h
  obtain ⟨p, hp, he⟩ := hpeak t hg
  have hw' : (0 : ℝ) < (w : ℝ) := by exact_mod_cast hw
  have hcap := cap_shift L vμ (w : ℝ) (gap v t) t p hv hw' hp he
  have hlt : c < min (gap v t) (nearestIntDist ((w : ℝ) * t)) := lt_min hg hwt
  linarith

end Gap
end Sext6
end LRSpectrumFull
