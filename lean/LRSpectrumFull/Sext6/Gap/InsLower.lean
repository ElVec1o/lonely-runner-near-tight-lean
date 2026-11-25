import LRSpectrumFull.Sext6.Gap.InsUpper

/-!
# Theorem INS, part 4: the per-peak lower bound and (E)  [2026-11-25]

Source: the accompanying notes on single-speed insertion, section 3.

* `peak_right_lower`, `peak_left_lower` : crossing on the right (slope `sl` = largest speed at `-L`) /
  left (largest speed at `+L`) of a rational time `a/d` at which every old runner is `≥ L` away and
  `w (a/d) = th + z`:  `(w L + sl th)/(w + sl) ≤ ML (v, w)`, resp. `(w L + sl (-th))/(w + sl) ≤ ML (v, w)`.
* `peak_lower` : for a `PeakData` peak `p = a/d`, `mu = l/d < 1/2` and `(d - 1) M ≤ w`:
  `Hform mu th rho lam w ≤ ML (v, w)`.
* `ins_E_lower` : the same with `d` eliminated: `w ≥ 2 M (M - 1)` suffices (`d ≤ 2M - 1`).
* `ins_E` : (E).  If `ML v < 1/2`, `w ≥ 2 M (M - 1)`, `c` bounds `Hform` over all peaks higher than `c`
  (the hypothesis of (U)) and `c` is attained by a peak, then `ML (v, w) = c`.
Extra hypothesis kept visible: only peaks with `mu < 1/2` (i.e. `ML v < 1/2`) are treated.
No `sorry`, no `axiom`.

Convention: `v : Fin (k+1) → ℤ` has `k + 1` speeds; `V = (v, w) = Fin.snoc v w` (integer `w`) has `N = k + 2` speeds (moving runners), i.e. `N + 1` runners counting the one at rest. The Lonely Runner value of `V` is `1/(N+1) = 1/(k+3)`; the threshold of D1, D2 is `1/N`.
Hypotheses: those of the individual statements (numerical bounds, structural conditions and, where named in the list above, window predicates such as `PrimeWin`, `CopWin`, `PrimeWindow7`, which later modules discharge for explicit ranges). The unproved predicates `DusartPi`, `LRCHyp`, `CopWinHyp` are not hypotheses of any statement in this module.
Axiom audit: covered by `Axioms20` (`#print axioms`; declarations not printed there are bricks of printed ones, so their axioms are bounded by the printed lines).
-/

namespace LRSpectrumFull
namespace Sext6
namespace Gap

lemma nid_eq_abs' {x : ℝ} (hx : |x| ≤ 1 / 2) : nearestIntDist x = |x| := by
  rcases abs_cases x with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · have hx' : x ≤ 1 / 2 := by rw [h1] at hx; exact hx
    rw [h1]
    exact nid_of_le_half h2 hx'
  · have hx' : -x ≤ 1 / 2 := by rw [h1] at hx; exact hx
    have := nid_of_le_half (x := -x) (by linarith) hx'
    rw [nearestIntDist_neg] at this
    rw [h1]
    exact this

/-- Crossing to the right of `a/d`. -/
theorem peak_right_lower {k : ℕ} (v : Fin (k + 1) → ℤ) (hv : ∀ i, 0 < v i) (M : ℤ)
    (hM : ∀ i, v i ≤ M) (w : ℤ) (hw : 0 < w) (L sl : ℝ) (d : ℕ) (hd : 0 < d) (a l : ℤ)
    (th : ℝ) (z : ℤ) (hLl : L = (l : ℝ) / d) (hL0 : 0 < L) (hL1 : L < 1 / 2) (hsl : 0 < sl)
    (hfar : ∀ i, L ≤ nearestIntDist ((v i : ℝ) * ((a : ℝ) / d)))
    (hext : ∀ i (m : ℤ), (v i : ℝ) * ((a : ℝ) / d) = m - L → (v i : ℝ) ≤ sl)
    (hwt : (w : ℝ) * ((a : ℝ) / d) = th + z) (hthL : th ≤ L)
    (hsize : (M : ℝ) * d * (L - th) ≤ (w : ℝ) + sl) :
    ((w : ℝ) * L + sl * th) / ((w : ℝ) + sl) ≤ ML (Fin.snoc v w : Fin (k + 2) → ℤ) := by
  have hw' : (0 : ℝ) < (w : ℝ) := by exact_mod_cast hw
  have hdR : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd
  have hwsl : 0 < (w : ℝ) + sl := by linarith
  obtain ⟨K, hK⟩ : ∃ K : ℝ, K = ((w : ℝ) * L + sl * th) / ((w : ℝ) + sl) := ⟨_, rfl⟩
  have hKmul : K * ((w : ℝ) + sl) = (w : ℝ) * L + sl * th := by rw [hK]; field_simp
  rw [← hK]
  by_cases hK0 : K ≤ 0
  · exact hK0.trans (ML_nonneg _)
  push_neg at hK0
  obtain ⟨δ, hδ⟩ : ∃ δ : ℝ, δ = (L - th) / ((w : ℝ) + sl) := ⟨_, rfl⟩
  have hδmul : δ * ((w : ℝ) + sl) = L - th := by rw [hδ]; field_simp
  have hδ0 : 0 ≤ δ := by rw [hδ]; exact div_nonneg (by linarith) hwsl.le
  have hKδ : K = L - sl * δ := by
    have h0 : (K - (L - sl * δ)) * ((w : ℝ) + sl) = 0 := by
      linear_combination hKmul + sl * hδmul
    have := (mul_eq_zero.mp h0).resolve_right hwsl.ne'
    linarith
  have hvδ : sl * δ ≤ L := by linarith
  have hKL : K ≤ L := by nlinarith [mul_nonneg hsl.le hδ0]
  have hK1 : K ≤ 1 / 2 := by linarith
  have hMd : (M : ℝ) * δ * d ≤ 1 := by
    have h1 : (M : ℝ) * δ * d * ((w : ℝ) + sl) ≤ 1 * ((w : ℝ) + sl) := by
      have e : (M : ℝ) * δ * d * ((w : ℝ) + sl) = (M : ℝ) * d * (L - th) := by
        rw [← hδmul]; ring
      rw [e]; linarith
    exact le_of_mul_le_mul_right h1 hwsl
  apply ML_ge_of_far (Fin.snoc v w : Fin (k + 2) → ℤ) K (((a : ℝ) / d) + δ)
  intro i
  rcases Fin.eq_castSucc_or_eq_last i with ⟨j, rfl⟩ | rfl
  · rw [snoc_castSucc_eq]
    have hvM : (v j : ℝ) ≤ M := by exact_mod_cast hM j
    have hδd : (v j : ℝ) * δ * d ≤ 1 := by
      have h1 : (v j : ℝ) * δ ≤ M * δ := mul_le_mul_of_nonneg_right hvM hδ0
      have h2 : (v j : ℝ) * δ * d ≤ M * δ * d := mul_le_mul_of_nonneg_right h1 hdR.le
      linarith
    have hb := old_runner_bound d hd a l (v j) L sl δ hLl hL0 hL1 (hfar j) (hext j) (hv j) hδ0
      hδd hvδ hsl.le
    rw [hKδ]
    exact hb
  · rw [snoc_last_eq]
    have hzero : (K - th - (w : ℝ) * δ) * ((w : ℝ) + sl) = 0 := by
      linear_combination hKmul - (w : ℝ) * hδmul
    have h1 : K - th - (w : ℝ) * δ = 0 := (mul_eq_zero.mp hzero).resolve_right hwsl.ne'
    have e : (w : ℝ) * ((a : ℝ) / d + δ) = K + z := by
      have e1 : (w : ℝ) * ((a : ℝ) / d + δ) = (w : ℝ) * ((a : ℝ) / d) + (w : ℝ) * δ := by ring
      rw [e1, hwt]
      linarith
    rw [e, nearestIntDist_add_int, nid_of_le_half hK0.le hK1]

/-- Crossing to the left of `a/d` (mirror image `t ↦ -t`). -/
theorem peak_left_lower {k : ℕ} (v : Fin (k + 1) → ℤ) (hv : ∀ i, 0 < v i) (M : ℤ)
    (hM : ∀ i, v i ≤ M) (w : ℤ) (hw : 0 < w) (L sl : ℝ) (d : ℕ) (hd : 0 < d) (a l : ℤ)
    (th : ℝ) (z : ℤ) (hLl : L = (l : ℝ) / d) (hL0 : 0 < L) (hL1 : L < 1 / 2) (hsl : 0 < sl)
    (hfar : ∀ i, L ≤ nearestIntDist ((v i : ℝ) * ((a : ℝ) / d)))
    (hext : ∀ i (n : ℤ), (v i : ℝ) * ((a : ℝ) / d) = n + L → (v i : ℝ) ≤ sl)
    (hwt : (w : ℝ) * ((a : ℝ) / d) = th + z) (hthL : -th ≤ L)
    (hsize : (M : ℝ) * d * (L - (-th)) ≤ (w : ℝ) + sl) :
    ((w : ℝ) * L + sl * (-th)) / ((w : ℝ) + sl) ≤ ML (Fin.snoc v w : Fin (k + 2) → ℤ) := by
  have hneg : ((-a : ℤ) : ℝ) / d = -((a : ℝ) / d) := by rw [Int.cast_neg, neg_div]
  refine peak_right_lower v hv M hM w hw L sl d hd (-a) l (-th) (-z) hLl hL0 hL1 hsl ?_ ?_ ?_
    hthL hsize
  · intro i
    rw [hneg, mul_neg, nearestIntDist_neg]
    exact hfar i
  · intro i m hm
    rw [hneg] at hm
    exact hext i (-m) (by push_cast; linarith)
  · rw [hneg]
    push_cast
    linarith

lemma size_aux (M : ℤ) (hM0 : 0 ≤ M) (d : ℕ) (l : ℤ) (mu th : ℝ) (w : ℤ) (hd : 0 < d)
    (hmul : mu = (l : ℝ) / d) (hmu1 : mu < 1 / 2) (hth : |th| < mu)
    (hsize : ((d : ℝ) - 1) * M ≤ w) :
    (M : ℝ) * d * (mu - th) ≤ w := by
  have hdR : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd
  have hdmu : (d : ℝ) * mu = l := by rw [hmul]; field_simp
  have h2l : (2 : ℝ) * l ≤ d - 1 := by
    have h1 : (2 : ℝ) * l < d := by
      have : (d : ℝ) * mu < d * (1 / 2) := mul_lt_mul_of_pos_left hmu1 hdR
      linarith
    have h2 : (2 : ℤ) * l < d := by exact_mod_cast h1
    have h3 : (2 : ℤ) * l ≤ (d : ℤ) - 1 := by omega
    exact_mod_cast h3
  obtain ⟨h1, h2⟩ := abs_lt.mp hth
  have hMR : (0 : ℝ) ≤ (M : ℝ) := by exact_mod_cast hM0
  have h3 : (d : ℝ) * (mu - th) ≤ 2 * l := by
    nlinarith [mul_nonneg hdR.le (by linarith : 0 ≤ mu + th)]
  have h4 : (M : ℝ) * ((d : ℝ) * (mu - th)) ≤ (M : ℝ) * (2 * l) :=
    mul_le_mul_of_nonneg_left h3 hMR
  have h5 : (M : ℝ) * (2 * l) ≤ (M : ℝ) * ((d : ℝ) - 1) := mul_le_mul_of_nonneg_left h2l hMR
  nlinarith

/-- **Per-peak lower bound.** -/
theorem peak_lower {k : ℕ} (v : Fin (k + 1) → ℤ) (hv : ∀ i, 0 < v i) (M : ℤ)
    (hM : ∀ i, v i ≤ M) (w : ℤ) (hw : 0 < w) (p mu rho lam : ℝ)
    (hpeak : PeakData v p mu rho lam) (d : ℕ) (hd : 0 < d) (a l : ℤ)
    (hpa : p = (a : ℝ) / d) (hmul : mu = (l : ℝ) / d) (hmu1 : mu < 1 / 2)
    (hsize : ((d : ℝ) - 1) * M ≤ w) (th : ℝ) (z : ℤ) (hz : (w : ℝ) * p = th + z)
    (hth : |th| ≤ 1 / 2) :
    Hform mu th rho lam (w : ℝ) ≤ ML (Fin.snoc v w : Fin (k + 2) → ℤ) := by
  obtain ⟨hloc, hgp, hmu0, hmuh, ⟨i, hri, hip, hitop⟩, ⟨j, hlj, hjm, hjtop⟩⟩ := hpeak
  subst hpa
  have hM0 : 0 ≤ M := by have := hv 0; have := hM 0; omega
  have hfar : ∀ u, mu ≤ nearestIntDist ((v u : ℝ) * ((a : ℝ) / d)) := by
    intro u
    have := gap_le v ((a : ℝ) / d) u
    rw [hgp] at this
    exact this
  have hrho : 0 < rho := by rw [← hri]; exact_mod_cast hv i
  have hlam : 0 < lam := by rw [← hlj]; exact_mod_cast hv j
  have hextm : ∀ u (m : ℤ), (v u : ℝ) * ((a : ℝ) / d) = m - mu → (v u : ℝ) ≤ lam := by
    intro u m hm
    have := hjtop u ⟨m, hm⟩
    rw [← hlj]
    exact_mod_cast this
  have hextp : ∀ u (n : ℤ), (v u : ℝ) * ((a : ℝ) / d) = n + mu → (v u : ℝ) ≤ rho := by
    intro u n hn
    have := hitop u ⟨n, hn⟩
    rw [← hri]
    exact_mod_cast this
  by_cases hc : mu ≤ |th|
  · unfold Hform
    rw [if_pos hc]
    apply ML_ge_of_far (Fin.snoc v w : Fin (k + 2) → ℤ) mu ((a : ℝ) / d)
    intro u
    rcases Fin.eq_castSucc_or_eq_last u with ⟨j', rfl⟩ | rfl
    · rw [snoc_castSucc_eq]
      exact hfar j'
    · rw [snoc_last_eq, hz, nearestIntDist_add_int, nid_eq_abs' hth]
      exact hc
  · push_neg at hc
    unfold Hform
    rw [if_neg (not_le.mpr hc)]
    apply max_le
    · have hth1 : th ≤ mu := by have := le_abs_self th; linarith
      have hsz := size_aux M hM0 d l mu th w hd hmul hmu1 hc hsize
      have hb := peak_right_lower v hv M hM w hw mu lam d hd a l th z hmul hmu0 hmu1 hlam hfar
        hextm hz hth1 (by linarith)
      exact hb
    · have hth1 : -th ≤ mu := by have := neg_le_abs th; linarith
      have hc' : |-th| < mu := by rw [abs_neg]; exact hc
      have hsz := size_aux M hM0 d l mu (-th) w hd hmul hmu1 hc' hsize
      have hb := peak_left_lower v hv M hM w hw mu rho d hd a l th z hmul hmu0 hmu1 hrho hfar
        hextp hz hth1 (by linarith)
      have e : ((w : ℝ) * mu - rho * th) / ((w : ℝ) + rho) =
          ((w : ℝ) * mu + rho * (-th)) / ((w : ℝ) + rho) := by ring
      rw [e]
      exact hb

/-- **Per-peak lower bound for `w ≥ 2 M (M - 1)`** (`d ≤ 2M - 1` is derived). -/
theorem ins_E_lower {k : ℕ} (v : Fin (k + 1) → ℤ) (hv : ∀ i, 0 < v i) (M : ℤ)
    (hM : ∀ i, v i ≤ M) (w : ℤ) (hw : 2 * M * (M - 1) ≤ w) (hw0 : 0 < w) (p mu rho lam : ℝ)
    (hpeak : PeakData v p mu rho lam) (hmu1 : mu < 1 / 2) (th : ℝ) (z : ℤ)
    (hz : (w : ℝ) * p = th + z) (hth : |th| ≤ 1 / 2) :
    Hform mu th rho lam (w : ℝ) ≤ ML (Fin.snoc v w : Fin (k + 2) → ℤ) := by
  have hloc : IsLocalMax (gap v) p := hpeak.isLocalMax
  have hgp : gap v p = mu := hpeak.gap_eq
  have hmu0 : 0 < mu := hpeak.pos
  obtain ⟨a, d, hd, hdM, hpa, b, hb⟩ :=
    local_max_rational v hv M hM p hloc (by rw [hgp]; exact hmu0) (by rw [hgp]; exact hmu1)
  have hM0 : 0 ≤ M := by have := hv 0; have := hM 0; omega
  have hsize : ((d : ℝ) - 1) * M ≤ w := by
    have h1 : (d : ℝ) ≤ 2 * M - 1 := by exact_mod_cast hdM
    have h2 : (2 : ℝ) * M * (M - 1) ≤ w := by exact_mod_cast hw
    have hMR : (0 : ℝ) ≤ (M : ℝ) := by exact_mod_cast hM0
    nlinarith [mul_nonneg hMR (by linarith : (0 : ℝ) ≤ 2 * M - 1 - d)]
  exact peak_lower v hv M hM w hw0 p mu rho lam hpeak d hd a b hpa (by rw [← hgp]; exact hb)
    hmu1 hsize th z hz hth

/-- **(E).** -/
theorem ins_E {k : ℕ} (v : Fin (k + 1) → ℤ) (hv : ∀ i, 0 < v i) (M : ℤ) (hM : ∀ i, v i ≤ M)
    (hL1 : ML v < 1 / 2) (w : ℤ) (hw : 2 * M * (M - 1) ≤ w) (hw0 : 0 < w) (c : ℝ) (hc0 : 0 ≤ c)
    (hU : ∀ p mu rho lam : ℝ, PeakData v p mu rho lam → c < mu →
      ∀ (th : ℝ) (z : ℤ), (w : ℝ) * p = th + z → |th| ≤ 1 / 2 →
        Hform mu th rho lam (w : ℝ) ≤ c)
    (hatt : ∃ p mu rho lam th : ℝ, ∃ z : ℤ, PeakData v p mu rho lam ∧ (w : ℝ) * p = th + z ∧
      |th| ≤ 1 / 2 ∧ Hform mu th rho lam (w : ℝ) = c) :
    ML (Fin.snoc v w : Fin (k + 2) → ℤ) = c := by
  apply le_antisymm (ML_snoc_le_Hform v hv w hw0 c hc0 hU)
  obtain ⟨p, mu, rho, lam, th, z, hpeak, hz, hth, hH⟩ := hatt
  have hmuML : mu ≤ ML v := by
    rw [← hpeak.gap_eq]
    exact le_csSup (bddAbove_range_gap v) ⟨p, rfl⟩
  rw [← hH]
  exact ins_E_lower v hv M hM w hw hw0 p mu rho lam hpeak (lt_of_le_of_lt hmuML hL1) th z hz hth

end Gap
end Sext6
end LRSpectrumFull
