import LRSpectrumFull.Sext6.Gap.KStarLocal

/-!
# Theorem INS, part 2: the offset cap lemma (`Hform`, `Hcap`)  [2026-11-25]

Source: the accompanying notes on single-speed insertion, sections 1, 2.2.

`Hform mu th rho lam w` is the closed form `H_p(w)` of the max-min of the tent
`mu - lam h` (`h ≥ 0`), `mu - rho |h|` (`h < 0`) against `‖th + w h‖`:
`mu` if `mu ≤ |th|`, else `max ((w mu + lam th)/(w + lam)) ((w mu - rho th)/(w + rho))`
(this one expression covers both signs of `th` of the review's case list; `Hform_review` records that).

* `Hform_reflect`, `Hform_le_mu`, `Hform_lt_mu` : elementary properties.
* `Hcap_right`, `Hcap_left` : the one-sided caps, pure real arithmetic (`cap_bound` with an offset `th`).
* `Hcap` : the cap at a time `t` for a peak `p` with `w p = th + z`, `z ∈ ℤ`.
Hypotheses: `0 < mu ≤ 1/2`, `0 < rho`, `0 < lam`, `0 < w`; no range hypothesis on `th`.
No `sorry`, no `axiom`.

Convention: `v : Fin (k+1) → ℤ` has `k + 1` speeds; `V = (v, w) = Fin.snoc v w` (integer `w`) has `N = k + 2` speeds (moving runners), i.e. `N + 1` runners counting the one at rest. The Lonely Runner value of `V` is `1/(N+1) = 1/(k+3)`; the threshold of D1, D2 is `1/N`.
Hypotheses: those of the individual statements (numerical bounds, structural conditions and, where named in the list above, window predicates such as `PrimeWin`, `CopWin`, `PrimeWindow7`, which later modules discharge for explicit ranges). The unproved predicates `DusartPi`, `LRCHyp`, `CopWinHyp` are not hypotheses of any statement in this module.
Axiom audit: covered by `Axioms20` (`#print axioms`; declarations not printed there are bricks of printed ones, so their axioms are bounded by the printed lines).
-/

namespace LRSpectrumFull
namespace Sext6
namespace Gap

/-- The closed form `H_p(w)`. -/
noncomputable def Hform (mu th rho lam w : ℝ) : ℝ :=
  if mu ≤ |th| then mu
  else max ((w * mu + lam * th) / (w + lam)) ((w * mu - rho * th) / (w + rho))

/-- The review's case list (`th ≥ 0`: `max (R, Lf)`; `th < 0`: `max ((w mu + rho a)/(w+rho), (w mu - lam a)/(w+lam))`,
`a = -th`) is the same expression. -/
theorem Hform_review (mu th rho lam w : ℝ) (h : |th| < mu) :
    (0 ≤ th → Hform mu th rho lam w =
      max ((w * mu + lam * th) / (w + lam)) ((w * mu - rho * th) / (w + rho))) ∧
    (th < 0 → Hform mu th rho lam w =
      max ((w * mu + rho * (-th)) / (w + rho)) ((w * mu - lam * (-th)) / (w + lam))) := by
  have hn : ¬ mu ≤ |th| := not_le.mpr h
  constructor
  · intro _
    unfold Hform
    rw [if_neg hn]
  · intro _
    unfold Hform
    rw [if_neg hn]
    rw [show (w * mu - rho * th) / (w + rho) = (w * mu + rho * (-th)) / (w + rho) by ring,
      show (w * mu + lam * th) / (w + lam) = (w * mu - lam * (-th)) / (w + lam) by ring, max_comm]

theorem Hform_reflect (mu th rho lam w : ℝ) :
    Hform mu th rho lam w = Hform mu (-th) lam rho w := by
  unfold Hform
  rw [abs_neg]
  split_ifs with h
  · rfl
  · rw [show (w * mu - rho * th) / (w + rho) = (w * mu + rho * (-th)) / (w + rho) by ring,
      show (w * mu + lam * th) / (w + lam) = (w * mu - lam * (-th)) / (w + lam) by ring, max_comm]

/-- `H_p(w) < mu` when `|th| < mu`. -/
theorem Hform_lt_mu (mu th rho lam w : ℝ) (hr : 0 < rho) (hl : 0 < lam) (hw : 0 < w)
    (hth : |th| < mu) : Hform mu th rho lam w < mu := by
  have hwl : 0 < w + lam := by linarith
  have hwr : 0 < w + rho := by linarith
  obtain ⟨h1, h2⟩ := abs_lt.mp hth
  unfold Hform
  rw [if_neg (not_le.mpr hth)]
  apply max_lt
  · rw [div_lt_iff₀ hwl]
    nlinarith [mul_pos hl (by linarith : 0 < mu - th)]
  · rw [div_lt_iff₀ hwr]
    nlinarith [mul_pos hr (by linarith : 0 < mu + th)]

/-- `H_p(w) ≤ mu` always (for `0 ≤ rho, lam`, `0 < w`). -/
theorem Hform_le_mu (mu th rho lam w : ℝ) (hr : 0 ≤ rho) (hl : 0 ≤ lam) (hw : 0 < w) :
    Hform mu th rho lam w ≤ mu := by
  have hwl : 0 < w + lam := by linarith
  have hwr : 0 < w + rho := by linarith
  by_cases hth : mu ≤ |th|
  · unfold Hform
    rw [if_pos hth]
  · push_neg at hth
    obtain ⟨h1, h2⟩ := abs_lt.mp hth
    unfold Hform
    rw [if_neg (not_le.mpr hth)]
    apply max_le
    · rw [div_le_iff₀ hwl]
      nlinarith [mul_nonneg hl (by linarith : 0 ≤ mu - th)]
    · rw [div_le_iff₀ hwr]
      nlinarith [mul_nonneg hr (by linarith : 0 ≤ mu + th)]

/-- **Offset cap, right side** (`h ≥ 0`). -/
theorem Hcap_right (mu th rho lam w h : ℝ) (hmu0 : 0 < mu) (hmu : mu ≤ 1 / 2) (hr : 0 < rho)
    (hl : 0 < lam) (hw : 0 < w) (hh : 0 ≤ h) :
    min (mu - lam * h) (nearestIntDist (th + w * h)) ≤ Hform mu th rho lam w := by
  have hwl : 0 < w + lam := by linarith
  have hwr : 0 < w + rho := by linarith
  by_cases hth : mu ≤ |th|
  · unfold Hform
    rw [if_pos hth]
    have := mul_nonneg hl.le hh
    exact (min_le_left _ _).trans (by linarith)
  · push_neg at hth
    obtain ⟨hth1, hth2⟩ := abs_lt.mp hth
    unfold Hform
    rw [if_neg (not_le.mpr hth)]
    obtain ⟨R, hR⟩ : ∃ R : ℝ, R = (w * mu + lam * th) / (w + lam) := ⟨_, rfl⟩
    obtain ⟨Lf, hLf⟩ : ∃ Lf : ℝ, Lf = (w * mu - rho * th) / (w + rho) := ⟨_, rfl⟩
    rw [← hR, ← hLf]
    have hRw : R * (w + lam) = w * mu + lam * th := by rw [hR]; field_simp
    by_cases hT : mu - lam * h ≤ R
    · exact (min_le_left _ _).trans (hT.trans (le_max_left _ _))
    · push_neg at hT
      have hx : th + w * h < R := by
        by_contra hcon
        push_neg at hcon
        have h1 : R * (w + lam) ≤ (th + w * h) * (w + lam) :=
          mul_le_mul_of_nonneg_right hcon hwl.le
        have h2 : R * (w + lam) < (mu - lam * h) * (w + lam) := mul_lt_mul_of_pos_right hT hwl
        obtain ⟨q, hq⟩ : ∃ q : ℝ, q = mu - th - h * (w + lam) := ⟨_, rfl⟩
        have hA : w * q ≤ 0 := by rw [hq]; nlinarith [h1, hRw]
        have hB : 0 < lam * q := by rw [hq]; nlinarith [h2, hRw]
        have hq1 : q ≤ 0 := by
          by_contra hc
          push_neg at hc
          have := mul_pos hw hc
          linarith
        have hq2 : 0 < q := by
          by_contra hc
          push_neg at hc
          have := mul_nonneg hl.le (neg_nonneg.mpr hc)
          nlinarith
        linarith
      have hRmu : R < mu := by
        by_contra hcon
        push_neg at hcon
        have h1 : mu * (w + lam) ≤ R * (w + lam) := mul_le_mul_of_nonneg_right hcon hwl.le
        nlinarith [mul_pos hl (by linarith : 0 < mu - th)]
      rcases le_or_gt 0 (th + w * h) with hx0 | hx0
      · have hxhalf : th + w * h ≤ 1 / 2 := by linarith
        rw [nid_of_le_half hx0 hxhalf]
        exact (min_le_right _ _).trans (hx.le.trans (le_max_left _ _))
      · have hwh0 : 0 ≤ w * h := mul_nonneg hw.le hh
        have hneg : nearestIntDist (th + w * h) = -(th + w * h) := by
          have := nid_of_le_half (x := -(th + w * h)) (by linarith) (by linarith)
          rw [nearestIntDist_neg] at this
          exact this
        have hL : -th ≤ Lf := by
          rw [hLf, le_div_iff₀ hwr]
          nlinarith [mul_pos hw (by linarith : 0 < mu + th)]
        rw [hneg]
        exact (min_le_right _ _).trans ((by linarith : -(th + w * h) ≤ Lf).trans (le_max_right _ _))

/-- **Offset cap, left side** (`h = -s ≤ 0`). -/
theorem Hcap_left (mu th rho lam w s : ℝ) (hmu0 : 0 < mu) (hmu : mu ≤ 1 / 2) (hr : 0 < rho)
    (hl : 0 < lam) (hw : 0 < w) (hs : 0 ≤ s) :
    min (mu - rho * s) (nearestIntDist (th - w * s)) ≤ Hform mu th rho lam w := by
  have h := Hcap_right mu (-th) lam rho w s hmu0 hmu hl hr hw hs
  rw [← Hform_reflect] at h
  have e : -(th - w * s) = -th + w * s := by ring
  rw [← e, nearestIntDist_neg] at h
  exact h

/-- **`Hcap`**: a peak `p` of height `mu` with tent slopes `lam` (right) and `rho` (left), and
`w p = th + z` with `z ∈ ℤ`.  If `e` lies under the tent at `t`, then `min e ‖w t‖ ≤ Hform`. -/
theorem Hcap (mu th rho lam w t p e : ℝ) (z : ℤ) (hmu0 : 0 < mu) (hmu : mu ≤ 1 / 2)
    (hr : 0 < rho) (hl : 0 < lam) (hw : 0 < w) (hz : w * p = th + z)
    (hR : p ≤ t → e ≤ mu - lam * (t - p)) (hL : t ≤ p → e ≤ mu - rho * (p - t)) :
    min e (nearestIntDist (w * t)) ≤ Hform mu th rho lam w := by
  rcases le_total p t with hpt | hpt
  · have h := Hcap_right mu th rho lam w (t - p) hmu0 hmu hr hl hw (by linarith)
    have e1 : w * t = (th + w * (t - p)) + z := by linarith
    rw [e1, nearestIntDist_add_int]
    exact (min_le_min (hR hpt) le_rfl).trans h
  · have h := Hcap_left mu th rho lam w (p - t) hmu0 hmu hr hl hw (by linarith)
    have e1 : w * t = (th - w * (p - t)) + z := by linarith
    rw [e1, nearestIntDist_add_int]
    exact (min_le_min (hL hpt) le_rfl).trans h

end Gap
end Sext6
end LRSpectrumFull
