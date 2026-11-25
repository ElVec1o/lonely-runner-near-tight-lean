import LRSpectrumFull.Sext6.Gap.InsDescent
import LRSpectrumFull.Sext6.Gap.InsUpper
import LRSpectrumFull.Sext6.Gap.InsLower

/-!
# Theorem INS, part 6: D2 (the equivalence)  [2026-11-25]

Source: the accompanying notes on single-speed insertion, section 6.
Here `N = k + 2 = |V|` is the number of speeds (moving runners) of `V = (v, w)`; counting the runner at rest
there are `N + 1` runners, and the Lonely Runner value of `V` is `1/(N+1)`.

* `Hform_sep` : if `th` is `u (w + M)` away from `±mu` then `Hform ≤ mu - u`.
* `peak_unif` : under `ML v ≤ 1/N` and "`‖w p‖ < 1/N` whenever `gap v p = 1/N`", every peak of `v` has
  `Hform * N ≤ 1 - 1/((2M-1)(w+M))`: a uniform gap below `1/N` (this is the finiteness of the peak set,
  obtained from the rationality `p = a/d`, `mu = b/d`, `d ≤ 2M - 1` rather than by enumerating peaks).
* `descent_D2_backward` : `ML v ≤ 1/N` and the `‖w p‖ < 1/N` condition give `ML (v, w) < 1/N` (any `w > 0`).
* `descent_D2` : the equivalence, for `w ≥ (2M-1) M`, `M ≥ 2`, `k ≥ 1`.
No `sorry`, no `axiom`.

Convention: `v : Fin (k+1) → ℤ` has `k + 1` speeds; `V = (v, w) = Fin.snoc v w` (integer `w`) has `N = k + 2` speeds (moving runners), i.e. `N + 1` runners counting the one at rest. The Lonely Runner value of `V` is `1/(N+1) = 1/(k+3)`; the threshold of D1, D2 is `1/N`.
Hypotheses: those of the individual statements (numerical bounds, structural conditions and, where named in the list above, window predicates such as `PrimeWin`, `CopWin`, `PrimeWindow7`, which later modules discharge for explicit ranges). The unproved predicates `DusartPi`, `LRCHyp`, `CopWinHyp` are not hypotheses of any statement in this module.
Axiom audit: covered by `Axioms20` (`#print axioms`; declarations not printed there are bricks of printed ones, so their axioms are bounded by the printed lines).
-/

namespace LRSpectrumFull
namespace Sext6
namespace Gap

theorem Hform_sep (mu th rho lam w M u : ℝ) (hM1 : 1 ≤ M) (hr1 : 1 ≤ rho) (hl1 : 1 ≤ lam)
    (hw : 0 < w) (hth : |th| < mu) (hu0 : 0 ≤ u) (hu1 : u * (w + M) ≤ mu - th)
    (hu2 : u * (w + M) ≤ mu + th) : Hform mu th rho lam w ≤ mu - u := by
  have hwl : 0 < w + lam := by linarith
  have hwr : 0 < w + rho := by linarith
  unfold Hform
  rw [if_neg (not_le.mpr hth)]
  apply max_le
  · rw [div_le_iff₀ hwl]
    have h1 : lam * (u * (w + M)) ≤ lam * (mu - th) :=
      mul_le_mul_of_nonneg_left hu1 (by linarith)
    have h2 : 0 ≤ u * (lam * (w + M) - (w + lam)) :=
      mul_nonneg hu0 (by
        have e1 := mul_nonneg hw.le (sub_nonneg.2 hl1)
        have e2 := mul_nonneg (zero_le_one.trans hl1) (sub_nonneg.2 hM1)
        linarith)
    linarith
  · rw [div_le_iff₀ hwr]
    have h1 : rho * (u * (w + M)) ≤ rho * (mu + th) :=
      mul_le_mul_of_nonneg_left hu2 (by linarith)
    have h2 : 0 ≤ u * (rho * (w + M) - (w + rho)) :=
      mul_nonneg hu0 (by
        have e1 := mul_nonneg hw.le (sub_nonneg.2 hr1)
        have e2 := mul_nonneg (zero_le_one.trans hr1) (sub_nonneg.2 hM1)
        linarith)
    linarith

theorem peak_unif {k : ℕ} (v : Fin (k + 1) → ℤ) (hv : ∀ i, 0 < v i) (M : ℤ)
    (hM : ∀ i, v i ≤ M) (hk : 1 ≤ k) (w : ℤ) (hw : 0 < w)
    (hL : ML v ≤ 1 / ((k : ℝ) + 2))
    (hp : ∀ p : ℝ, gap v p = 1 / ((k : ℝ) + 2) →
      nearestIntDist ((w : ℝ) * p) < 1 / ((k : ℝ) + 2))
    (p mu rho lam : ℝ) (hpeak : PeakData v p mu rho lam) (th : ℝ) (z : ℤ)
    (hz : (w : ℝ) * p = th + z) (hth : |th| ≤ 1 / 2) :
    Hform mu th rho lam (w : ℝ) * ((k : ℝ) + 2) ≤
      1 - 1 / ((2 * (M : ℝ) - 1) * ((w : ℝ) + M)) := by
  have hN : (0 : ℝ) < (k : ℝ) + 2 := by positivity
  have hkR : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
  have hM1 : 1 ≤ M := by have := hv 0; have := hM 0; omega
  have hMR : (1 : ℝ) ≤ (M : ℝ) := by exact_mod_cast hM1
  have hwR : (0 : ℝ) < (w : ℝ) := by exact_mod_cast hw
  have hloc : IsLocalMax (gap v) p := hpeak.isLocalMax
  have hgp : gap v p = mu := hpeak.gap_eq
  have hmu0 : 0 < mu := hpeak.pos
  have hmuN : mu ≤ 1 / ((k : ℝ) + 2) := by
    rw [← hgp]
    exact (le_csSup (bddAbove_range_gap v) ⟨p, rfl⟩).trans hL
  have hmuhalf : mu < 1 / 2 := by
    have : 1 / ((k : ℝ) + 2) ≤ 1 / 3 := one_div_le_one_div_of_le (by norm_num) (by linarith)
    linarith
  have hrho1 : 1 ≤ rho := by
    obtain ⟨_, _, _, _, ⟨i, hri, _, _⟩, _⟩ := hpeak
    rw [← hri]
    have : (1 : ℤ) ≤ v i := hv i
    exact_mod_cast this
  have hlam1 : 1 ≤ lam := by
    obtain ⟨_, _, _, _, _, ⟨j, hlj, _, _⟩⟩ := hpeak
    rw [← hlj]
    have : (1 : ℤ) ≤ v j := hv j
    exact_mod_cast this
  obtain ⟨a, d, hd, hdM, hpa, b, hb⟩ :=
    local_max_rational v hv M hM p hloc (by rw [hgp]; exact hmu0) (by rw [hgp]; exact hmuhalf)
  have hmub : mu = (b : ℝ) / d := by rw [← hgp]; exact hb
  have hdR : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd
  have hdne : (d : ℝ) ≠ 0 := hdR.ne'
  have hdM' : (d : ℝ) ≤ 2 * M - 1 := by exact_mod_cast hdM
  have hmud : mu * d = b := by rw [hmub]; field_simp
  have hwM : (1 : ℝ) ≤ (w : ℝ) + M := by linarith
  obtain ⟨Z, hZ⟩ : ∃ Z : ℝ, Z = (2 * (M : ℝ) - 1) * ((w : ℝ) + M) := ⟨_, rfl⟩
  rw [← hZ]
  have hdZ : (d : ℝ) ≤ Z := by
    rw [hZ]
    nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ 2 * M - 1) (by linarith : (0 : ℝ) ≤ (w : ℝ) + M - 1)]
  have hZpos : 0 < Z := lt_of_lt_of_le hdR hdZ
  have hZd : 1 / Z ≤ 1 / (d : ℝ) := one_div_le_one_div_of_le hdR hdZ
  rcases hmuN.lt_or_eq with hA | hB
  · -- mu < 1/N
    have hHle : Hform mu th rho lam (w : ℝ) ≤ mu := Hform_le_mu mu th rho lam _ (by linarith)
      (by linarith) hwR
    have hbd : (b : ℝ) * ((k : ℝ) + 2) < d := by
      have h := hA
      rw [hmub, div_lt_div_iff₀ hdR hN] at h
      linarith
    have hint : b * ((k : ℤ) + 2) < d := by exact_mod_cast hbd
    have hint2 : b * ((k : ℤ) + 2) + 1 ≤ d := by linarith
    have hreal : (b : ℝ) * ((k : ℝ) + 2) + 1 ≤ d := by exact_mod_cast hint2
    have e : mu * ((k : ℝ) + 2) * d = b * ((k : ℝ) + 2) := by
      rw [mul_right_comm mu _ (d : ℝ), hmud]
    have h1 : 1 / (d : ℝ) ≤ 1 - mu * ((k : ℝ) + 2) := by
      rw [div_le_iff₀ hdR]
      nlinarith
    have h2 := mul_le_mul_of_nonneg_right hHle hN.le
    linarith
  · -- mu = 1/N
    have hgpv : gap v p = 1 / ((k : ℝ) + 2) := by rw [hgp, hB]
    have hnid := hp p hgpv
    have hthmu : |th| < mu := by
      rw [hz, nearestIntDist_add_int, nid_eq_abs' hth] at hnid
      rw [hB]
      exact hnid
    obtain ⟨hthl, hthr⟩ := abs_lt.mp hthmu
    have hwa : (w : ℝ) * ((a : ℝ) / d) = th + z := by rw [← hpa]; exact hz
    have hthd : th * d = (w : ℝ) * a - z * d := by
      have e1 : (w : ℝ) * ((a : ℝ) / d) * d = w * a := by field_simp
      linear_combination (-(d : ℝ)) * hwa + e1
    have hr1 : ((w : ℝ) * a - z * d) < b := by
      rw [← hthd, ← hmud]
      exact mul_lt_mul_of_pos_right hthr hdR
    have hr2 : -(b : ℝ) < (w : ℝ) * a - z * d := by
      have : -(mu * d) < th * d := by
        have := mul_lt_mul_of_pos_right hthl hdR
        linarith
      rw [hmud, hthd] at this
      exact this
    have hI1 : w * a - z * (d : ℤ) < b := by exact_mod_cast hr1
    have hI2 : -b < w * a - z * (d : ℤ) := by exact_mod_cast hr2
    have hI1' : w * a - z * (d : ℤ) + 1 ≤ b := by linarith
    have hI2' : -b + 1 ≤ w * a - z * (d : ℤ) := by linarith
    have hR1 : (w : ℝ) * a - z * d + 1 ≤ b := by exact_mod_cast hI1'
    have hR2 : -(b : ℝ) + 1 ≤ (w : ℝ) * a - z * d := by exact_mod_cast hI2'
    have hmth1 : 1 / (d : ℝ) ≤ mu - th := by
      rw [div_le_iff₀ hdR]
      have : (mu - th) * d = b - ((w : ℝ) * a - z * d) := by
        rw [sub_mul, hmud, hthd]
      rw [this]
      linarith
    have hmth2 : 1 / (d : ℝ) ≤ mu + th := by
      rw [div_le_iff₀ hdR]
      have : (mu + th) * d = b + ((w : ℝ) * a - z * d) := by
        rw [add_mul, hmud, hthd]
      rw [this]
      linarith
    have hwMne : (w : ℝ) + M ≠ 0 := (by linarith : (0 : ℝ) < (w : ℝ) + M).ne'
    have hdw : 0 < (d : ℝ) * ((w : ℝ) + M) := mul_pos hdR (by linarith)
    obtain ⟨u, hu⟩ : ∃ u : ℝ, u = 1 / ((d : ℝ) * ((w : ℝ) + M)) := ⟨_, rfl⟩
    have hu0 : 0 ≤ u := by rw [hu]; exact (one_div_pos.mpr hdw).le
    have huw : u * ((w : ℝ) + M) = 1 / d := by rw [hu]; field_simp
    have hH := Hform_sep mu th rho lam (w : ℝ) M u hMR hrho1 hlam1 hwR hthmu hu0
      (by rw [huw]; exact hmth1) (by rw [huw]; exact hmth2)
    have hmuN1 : mu * ((k : ℝ) + 2) = 1 := by rw [hB]; field_simp
    have h2 := mul_le_mul_of_nonneg_right hH hN.le
    have hdwZ : (d : ℝ) * ((w : ℝ) + M) ≤ Z := by
      rw [hZ]
      exact mul_le_mul_of_nonneg_right hdM' (by linarith)
    have huZ : 1 / Z ≤ u := by rw [hu]; exact one_div_le_one_div_of_le hdw hdwZ
    have huN : u ≤ u * ((k : ℝ) + 2) := by
      nlinarith [mul_nonneg hu0 (by linarith : (0 : ℝ) ≤ (k : ℝ) + 1)]
    linarith

theorem descent_D2_backward {k : ℕ} (v : Fin (k + 1) → ℤ) (hv : ∀ i, 0 < v i) (M : ℤ)
    (hM : ∀ i, v i ≤ M) (hk : 1 ≤ k) (w : ℤ) (hw : 0 < w)
    (hL : ML v ≤ 1 / ((k : ℝ) + 2))
    (hp : ∀ p : ℝ, gap v p = 1 / ((k : ℝ) + 2) →
      nearestIntDist ((w : ℝ) * p) < 1 / ((k : ℝ) + 2)) :
    ML (Fin.snoc v w : Fin (k + 2) → ℤ) < 1 / ((k : ℝ) + 2) := by
  have hN : (0 : ℝ) < (k : ℝ) + 2 := by positivity
  have hM1 : 1 ≤ M := by have := hv 0; have := hM 0; omega
  have hMR : (1 : ℝ) ≤ (M : ℝ) := by exact_mod_cast hM1
  have hwR : (0 : ℝ) < (w : ℝ) := by exact_mod_cast hw
  obtain ⟨Z, hZ⟩ : ∃ Z : ℝ, Z = (2 * (M : ℝ) - 1) * ((w : ℝ) + M) := ⟨_, rfl⟩
  have hZ1 : 1 ≤ Z := by
    rw [hZ]
    nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ 2 * M - 2) (by linarith : (0 : ℝ) ≤ (w : ℝ) + M)]
  have hZpos : 0 < Z := by linarith
  have hZinv : 0 < 1 / Z := one_div_pos.mpr hZpos
  have hZinv1 : 1 / Z ≤ 1 := (div_le_one hZpos).mpr hZ1
  obtain ⟨c, hc⟩ : ∃ c : ℝ, c = (1 - 1 / Z) / ((k : ℝ) + 2) := ⟨_, rfl⟩
  have hc0 : 0 ≤ c := by rw [hc]; exact div_nonneg (by linarith) hN.le
  have hU := ML_snoc_le_Hform v hv w hw c hc0 (by
    intro p mu rho lam hpeak _ th z hz hth
    rw [hc, le_div_iff₀ hN]
    have := peak_unif v hv M hM hk w hw hL hp p mu rho lam hpeak th z hz hth
    rw [hZ]
    exact this)
  have hcN : c * ((k : ℝ) + 2) = 1 - 1 / Z := by rw [hc]; exact div_mul_cancel₀ _ hN.ne'
  have hclt : c < 1 / ((k : ℝ) + 2) := by
    rw [lt_div_iff₀ hN, hcN]
    linarith
  exact lt_of_le_of_lt hU hclt

/-- **D2.**  For `w ≥ (2M - 1) M` (`M ≥ 2`, `k ≥ 1`):
`ML (v, w) < 1/N` iff `ML v ≤ 1/N` and `‖w p‖ < 1/N` at every `p` with `gap v p = 1/N`. -/
theorem descent_D2 {k : ℕ} (v : Fin (k + 1) → ℤ) (hv : ∀ i, 0 < v i) (M : ℤ)
    (hM : ∀ i, v i ≤ M) (hM2 : 2 ≤ M) (hk : 1 ≤ k) (w : ℤ) (hw : (2 * M - 1) * M ≤ w) :
    ML (Fin.snoc v w : Fin (k + 2) → ℤ) < 1 / ((k : ℝ) + 2) ↔
      (ML v ≤ 1 / ((k : ℝ) + 2) ∧
        ∀ p : ℝ, gap v p = 1 / ((k : ℝ) + 2) → nearestIntDist ((w : ℝ) * p) < 1 / ((k : ℝ) + 2)) := by
  constructor
  · intro h
    exact descent_D2_forward v hv M hM hM2 hk w hw h
  · rintro ⟨h1, h2⟩
    have hw0 : 0 < w := by
      nlinarith [mul_pos (by omega : (0 : ℤ) < 2 * M - 1) (by omega : (0 : ℤ) < M)]
    exact descent_D2_backward v hv M hM hk w hw0 h1 h2

end Gap
end Sext6
end LRSpectrumFull
