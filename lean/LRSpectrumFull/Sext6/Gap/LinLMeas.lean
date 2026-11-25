import LRSpectrumFull.Sext6.Gap.RobustMeasure
import LRSpectrumFull.Sext6.Gap.OELowCore

/-!
# Theorem L (linear robustness), module 1: measure bricks  [2026-11-25]

Source: the accompanying notes on Theorem L (Lemmas 3 and 6, and the generalised counting step).
Fixed window radius `lwd N = 1/((2N-1) N^2)` around each `a/D`.
`badMeas N w lo hi` is the Lebesgue measure (as a real) of `{t in [lo,hi] : ‖w t‖ < 1/N}`.

* `exists_good_point_gen` : if the bad measures of a finite set of speeds sum to less than `b - a`, some
                            `t in [a,b]` is good for all of them.
* `badMeas_osc`           : oscillating speeds (`2 w > (2N-1) N (N-2)`, `N ≥ 10`): `badMeas ≤ (7/N) (hi - lo)`.
* `arc_data`              : non-oscillating speeds meet the window in one arc; positive measure gives an
                            integer `e` with `D ∣ w - e r`, `|e| N^2 < D N + w`, measure `≤ 2/(N w)`.
Only `measure_mono`, `Real.volume_Ioo`, `Real.volume_Icc` and `measure_biUnion_finset_le` are used.
No `sorry`, no `axiom`.

Convention: `N` is a natural number (the size of the ambient interval `[1,N]`); speeds are natural numbers `w > N`.
Hypotheses: those of the individual statements.  No window predicate occurs in this module.
Axiom audit: `Axioms26`.
-/

namespace LRSpectrumFull
namespace Sext6
namespace Gap
namespace LinL

open MeasureTheory

/-- The fixed window radius. -/
noncomputable def lwd (N : ℕ) : ℝ := 1 / ((2 * (N : ℝ) - 1) * (N : ℝ) ^ 2)

theorem lwd_pos {N : ℕ} (hN : 1 ≤ N) : 0 < lwd N := by
  unfold lwd
  have h : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have h1 : (0 : ℝ) < 2 * N - 1 := by linarith
  have h2 : (0 : ℝ) < (N : ℝ) ^ 2 := by positivity
  exact one_div_pos.mpr (mul_pos h1 h2)

/-- Bad measure of speed `w` in `[lo, hi]`. -/
noncomputable def badMeas (N w : ℕ) (lo hi : ℝ) : ℝ :=
  (volume {t : ℝ | t ∈ Set.Icc lo hi ∧ nearestIntDist ((w : ℝ) * t) < 1 / (N : ℝ)}).toReal

theorem badMeas_nonneg (N w : ℕ) (lo hi : ℝ) : 0 ≤ badMeas N w lo hi := ENNReal.toReal_nonneg

theorem badMeas_le_len (N w : ℕ) {lo hi : ℝ} (h : lo ≤ hi) : badMeas N w lo hi ≤ hi - lo := by
  unfold badMeas
  have h1 : volume {t : ℝ | t ∈ Set.Icc lo hi ∧ nearestIntDist ((w : ℝ) * t) < 1 / (N : ℝ)} ≤
      volume (Set.Icc lo hi) := measure_mono (fun t ht => ht.1)
  rw [Real.volume_Icc] at h1
  exact ENNReal.toReal_le_of_le_ofReal (by linarith) h1

theorem badMeas_pos_nonempty {N w : ℕ} {lo hi : ℝ} (h : 0 < badMeas N w lo hi) :
    ∃ t : ℝ, t ∈ Set.Icc lo hi ∧ nearestIntDist ((w : ℝ) * t) < 1 / (N : ℝ) := by
  by_contra hne
  push Not at hne
  have h0 : {t : ℝ | t ∈ Set.Icc lo hi ∧ nearestIntDist ((w : ℝ) * t) < 1 / (N : ℝ)} = ∅ := by
    ext t
    simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
    exact fun ht => absurd ht.2 (not_lt.mpr (hne t ht.1))
  unfold badMeas at h
  rw [h0] at h
  simp at h

/-- **Generalised counting step.** -/
theorem exists_good_point_gen (a b : ℝ) (hab : a < b) (N : ℕ) (U : Finset ℕ)
    (hsum : ∑ u ∈ U, badMeas N u a b < b - a) :
    ∃ t ∈ Set.Icc a b, ∀ u ∈ U, 1 / (N : ℝ) ≤ nearestIntDist ((u : ℝ) * t) := by
  by_contra hcon
  push Not at hcon
  have hcover : Set.Icc a b ⊆ ⋃ u ∈ U,
      {t : ℝ | t ∈ Set.Icc a b ∧ nearestIntDist ((u : ℝ) * t) < 1 / (N : ℝ)} := by
    intro t ht
    obtain ⟨u, hu, hlt⟩ := hcon t ht
    simp only [Set.mem_iUnion]
    exact ⟨u, hu, ht, hlt⟩
  have h1 : volume (Set.Icc a b) ≤ ∑ u ∈ U,
      volume {t : ℝ | t ∈ Set.Icc a b ∧ nearestIntDist ((u : ℝ) * t) < 1 / (N : ℝ)} :=
    (measure_mono hcover).trans (measure_biUnion_finset_le U _)
  have hfin : ∀ u ∈ U, volume {t : ℝ | t ∈ Set.Icc a b ∧ nearestIntDist ((u : ℝ) * t) < 1 / (N : ℝ)}
      = ENNReal.ofReal (badMeas N u a b) := by
    intro u hu
    have hne : volume {t : ℝ | t ∈ Set.Icc a b ∧ nearestIntDist ((u : ℝ) * t) < 1 / (N : ℝ)} ≠ ⊤ := by
      refine ne_top_of_le_ne_top (b := volume (Set.Icc a b)) ?_ (measure_mono (fun t ht => ht.1))
      rw [Real.volume_Icc]; exact ENNReal.ofReal_ne_top
    unfold badMeas
    exact (ENNReal.ofReal_toReal hne).symm
  rw [Finset.sum_congr rfl hfin, Real.volume_Icc,
    ← ENNReal.ofReal_sum_of_nonneg (fun u _ => badMeas_nonneg N u a b)] at h1
  have hsnn : 0 ≤ ∑ u ∈ U, badMeas N u a b := Finset.sum_nonneg (fun u _ => badMeas_nonneg N u a b)
  have h4 := (ENNReal.ofReal_le_ofReal_iff hsnn).mp h1
  linarith

/-- **Lemma 6 (oscillating speeds).** -/
theorem badMeas_osc {N w : ℕ} (hN : 10 ≤ N)
    (hw : (2 * (N : ℝ) - 1) * N * (N - 2) < 2 * (w : ℝ)) {lo hi : ℝ} (hl : hi - lo = 2 * lwd N) :
    badMeas N w lo hi ≤ 7 / (N : ℝ) * (hi - lo) := by
  have hNR : (10 : ℝ) ≤ N := by exact_mod_cast hN
  have hNpos : (0 : ℝ) < N := by linarith
  have hw1 : 1 ≤ w := by
    by_contra h
    have h0 : w = 0 := by omega
    subst h0
    have : (0 : ℝ) < (2 * (N : ℝ) - 1) * N * (N - 2) := by
      have a1 : (0 : ℝ) < 2 * N - 1 := by linarith
      have a2 : (0 : ℝ) < N - 2 := by linarith
      positivity
    simp at hw
    linarith
  have hwR : (0 : ℝ) < w := by exact_mod_cast hw1
  have hd0 : 0 < lwd N := lwd_pos (by omega)
  have hle : lo ≤ hi := by linarith
  have h1 := measure_bad_le lo hi hle N w (by omega) hw1
  have hnn : 0 ≤ 2 * (hi - lo) / (N : ℝ) + 4 / ((N : ℝ) * w) := by
    have : 0 ≤ hi - lo := by linarith
    positivity
  have h2 : badMeas N w lo hi ≤ 2 * (hi - lo) / N + 4 / (N * w) :=
    ENNReal.toReal_le_of_le_ofReal hnn h1
  have hX : (0 : ℝ) < (2 * (N : ℝ) - 1) * (N : ℝ) ^ 2 := by
    have a1 : (0 : ℝ) < 2 * N - 1 := by linarith
    positivity
  have key : 4 ≤ 10 * lwd N * w := by
    have e : 10 * lwd N * (w : ℝ) = 10 * w / ((2 * (N : ℝ) - 1) * (N : ℝ) ^ 2) := by
      unfold lwd; ring
    rw [e, le_div_iff₀ hX]
    nlinarith [hw, hNR, mul_pos hNpos hNpos]
  have h3 : 4 / ((N : ℝ) * w) ≤ 5 * (hi - lo) / N := by
    rw [div_le_div_iff₀ (by positivity) hNpos]
    have : 5 * (hi - lo) = 10 * lwd N := by rw [hl]; ring
    rw [this]
    nlinarith [mul_le_mul_of_nonneg_left key hNpos.le]
  have e2 : 7 / (N : ℝ) * (hi - lo) = 2 * (hi - lo) / N + 5 * (hi - lo) / N := by ring
  rw [e2]
  linarith

/-- Subset of an arc. -/
theorem bad_subset_arc {N w : ℕ} (hN : 10 ≤ N) (hw1 : 1 ≤ w)
    (hsm : 2 * (w : ℝ) ≤ (2 * (N : ℝ) - 1) * N * (N - 2)) {lo hi : ℝ} (hl : hi - lo = 2 * lwd N)
    {t0 : ℝ} (ht0 : t0 ∈ Set.Icc lo hi) {c0 : ℤ} (hc0 : |(w : ℝ) * t0 - c0| < 1 / (N : ℝ)) :
    {t : ℝ | t ∈ Set.Icc lo hi ∧ nearestIntDist ((w : ℝ) * t) < 1 / (N : ℝ)} ⊆
      Set.Ioo (((c0 : ℝ) - 1 / (N : ℝ)) / w) (((c0 : ℝ) + 1 / (N : ℝ)) / w) := by
  intro t ht
  obtain ⟨htI, hlt⟩ := ht
  have hNR : (10 : ℝ) ≤ N := by exact_mod_cast hN
  have hNpos : (0 : ℝ) < N := by linarith
  have hwR : (0 : ℝ) < w := by exact_mod_cast hw1
  obtain ⟨c, hc⟩ := nearestIntDist_eq_abs ((w : ℝ) * t)
  rw [hc] at hlt
  have hX : (0 : ℝ) < (2 * (N : ℝ) - 1) * (N : ℝ) ^ 2 := by
    have a1 : (0 : ℝ) < 2 * N - 1 := by linarith
    positivity
  have hwd : (w : ℝ) * (hi - lo) ≤ 1 - 2 / N := by
    rw [hl]
    have e : (w : ℝ) * (2 * lwd N) = 2 * w / ((2 * (N : ℝ) - 1) * (N : ℝ) ^ 2) := by
      unfold lwd; ring
    rw [e, div_le_iff₀ hX]
    have e2 : (1 - 2 / (N : ℝ)) * ((2 * (N : ℝ) - 1) * (N : ℝ) ^ 2) =
        (2 * (N : ℝ) - 1) * N * (N - 2) := by
      first
        | (field_simp; done)
        | (field_simp; ring)
    rw [e2]
    exact hsm
  have hdt : |t - t0| ≤ hi - lo := by
    rw [abs_le]
    constructor <;> linarith [htI.1, htI.2, ht0.1, ht0.2]
  have hwt : |(w : ℝ) * t - (w : ℝ) * t0| ≤ w * (hi - lo) := by
    rw [← mul_sub, abs_mul, abs_of_pos hwR]
    exact mul_le_mul_of_nonneg_left hdt hwR.le
  have hcc : |((c : ℝ) - c0)| < 1 := by
    have h1 : |(c : ℝ) - c0| ≤ |(c : ℝ) - w * t| + |(w : ℝ) * t - w * t0| + |(w : ℝ) * t0 - c0| := by
      calc |(c : ℝ) - c0| = |((c : ℝ) - w * t) + ((w : ℝ) * t - w * t0) + ((w : ℝ) * t0 - c0)| := by ring_nf
        _ ≤ _ := by
          refine (abs_add_le _ _).trans ?_
          have := abs_add_le ((c : ℝ) - w * t) ((w : ℝ) * t - w * t0)
          linarith
    rw [abs_sub_comm (c : ℝ) ((w : ℝ) * t)] at h1
    have h2 : 2 / (N : ℝ) = 1 / N + 1 / N := by ring
    linarith
  have hcc' : |c - c0| < 1 := by
    have : |((c - c0 : ℤ) : ℝ)| < 1 := by push_cast; exact hcc
    exact_mod_cast this
  have hceq : c = c0 := by
    have := Int.abs_lt_one_iff.mp hcc'
    omega
  subst hceq
  obtain ⟨hl1, hl2⟩ := abs_lt.mp hlt
  constructor
  · rw [div_lt_iff₀ hwR]; linarith
  · rw [lt_div_iff₀ hwR]; linarith

/-- The overlap length of the interval `[s - ρ, s + ρ]` with `[-d, d]` (clamped at zero). -/
noncomputable def lam (ρ d s : ℝ) : ℝ := max 0 (min (s + ρ) d - max (s - ρ) (-d))

/-- **Lemma 3 (with arc position).** A non-oscillating speed meets a window in one arc. -/
theorem arc_data' {N r w D : ℕ} (a b : ℤ) (hab : a * (r : ℤ) + b * (D : ℤ) = 1)
    (hN : 10 ≤ N) (hD0 : 0 < D) (hD : D + 1 ≤ 2 * N) (hw : N < w)
    (hsm : 2 * (w : ℝ) ≤ (2 * (N : ℝ) - 1) * N * (N - 2))
    (hpos : 0 < badMeas N w ((a : ℝ) / D - lwd N) ((a : ℝ) / D + lwd N)) :
    ∃ e : ℤ, (D : ℤ) ∣ (w : ℤ) - e * r ∧ |e| * (N : ℤ) ^ 2 < D * N + w ∧
      badMeas N w ((a : ℝ) / D - lwd N) ((a : ℝ) / D + lwd N) ≤ 2 / ((N : ℝ) * w) ∧
      badMeas N w ((a : ℝ) / D - lwd N) ((a : ℝ) / D + lwd N) ≤
        lam (1 / ((N : ℝ) * w)) (lwd N) (-(e : ℝ) / ((w : ℝ) * D)) := by
  have hNR : (10 : ℝ) ≤ N := by exact_mod_cast hN
  have hNpos : (0 : ℝ) < N := by linarith
  have hw1 : 1 ≤ w := by omega
  have hwR : (0 : ℝ) < w := by exact_mod_cast hw1
  have hDR : (0 : ℝ) < D := by exact_mod_cast hD0
  have hd0 : 0 < lwd N := lwd_pos (by omega)
  have hl : ((a : ℝ) / D + lwd N) - ((a : ℝ) / D - lwd N) = 2 * lwd N := by ring
  obtain ⟨t0, ht0, hlt0⟩ := badMeas_pos_nonempty hpos
  obtain ⟨c0, hc0⟩ := nearestIntDist_eq_abs ((w : ℝ) * t0)
  rw [hc0] at hlt0
  have hsub := bad_subset_arc hN hw1 hsm hl ht0 hlt0
  refine ⟨a * w - c0 * D, ?_, ?_, ?_, ?_⟩
  · exact ⟨b * w + c0 * r, by linear_combination (-(w : ℤ)) * hab⟩
  · -- the size of `e`
    have hD1 : (D : ℝ) ≤ 2 * N - 1 := by
      have : (D : ℝ) + 1 ≤ 2 * N := by exact_mod_cast hD
      linarith
    have hu : |(w : ℝ) * t0 - c0| < 1 / N := hlt0
    have hv : |t0 - (a : ℝ) / D| ≤ lwd N := by
      rw [abs_le]; constructor <;> linarith [ht0.1, ht0.2]
    have hE : (((a * w - c0 * D : ℤ)) : ℝ) = -((D : ℝ) * (((c0 : ℝ) - w * t0) + w * (t0 - (a : ℝ) / D))) := by
      push_cast
      field_simp
      ring
    have h4 : |(((a * w - c0 * D : ℤ)) : ℝ)| < D / N + D * w * lwd N := by
      rw [hE, abs_neg, abs_mul, abs_of_pos hDR]
      have hs : |((c0 : ℝ) - w * t0) + w * (t0 - (a : ℝ) / D)| < 1 / N + w * lwd N := by
        refine lt_of_le_of_lt (abs_add_le _ _) ?_
        have e1 : |(c0 : ℝ) - w * t0| < 1 / N := by rw [abs_sub_comm]; exact hu
        have e2 : |(w : ℝ) * (t0 - (a : ℝ) / D)| ≤ w * lwd N := by
          rw [abs_mul, abs_of_pos hwR]
          exact mul_le_mul_of_nonneg_left hv hwR.le
        linarith
      calc (D : ℝ) * |((c0 : ℝ) - w * t0) + w * (t0 - (a : ℝ) / D)|
          < D * (1 / N + w * lwd N) := mul_lt_mul_of_pos_left hs hDR
        _ = D / N + D * w * lwd N := by ring
    have h5 : (D : ℝ) * w * lwd N ≤ w / (N : ℝ) ^ 2 := by
      unfold lwd
      have hX : (0 : ℝ) < (2 * (N : ℝ) - 1) * (N : ℝ) ^ 2 := by
        have a1 : (0 : ℝ) < 2 * N - 1 := by linarith
        positivity
      have e : (D : ℝ) * w * (1 / ((2 * (N : ℝ) - 1) * (N : ℝ) ^ 2)) =
          D * w / ((2 * (N : ℝ) - 1) * (N : ℝ) ^ 2) := by ring
      rw [e, div_le_div_iff₀ hX (by positivity)]
      have : (0 : ℝ) ≤ (w : ℝ) * (N : ℝ) ^ 2 := by positivity
      nlinarith [mul_le_mul_of_nonneg_right hD1 this]
    have h6 : |(((a * w - c0 * D : ℤ)) : ℝ)| < D / N + w / (N : ℝ) ^ 2 := by linarith
    have hN2 : (0 : ℝ) < (N : ℝ) ^ 2 := by positivity
    have h7 : |(((a * w - c0 * D : ℤ)) : ℝ)| * (N : ℝ) ^ 2 < D * N + w := by
      have e1 : ((D : ℝ) / N + w / (N : ℝ) ^ 2) * (N : ℝ) ^ 2 = D * N + w := by
        field_simp
      calc |(((a * w - c0 * D : ℤ)) : ℝ)| * (N : ℝ) ^ 2
          < ((D : ℝ) / N + w / (N : ℝ) ^ 2) * (N : ℝ) ^ 2 := mul_lt_mul_of_pos_right h6 hN2
        _ = D * N + w := e1
    have h8 : ((|a * w - c0 * D| * (N : ℤ) ^ 2 : ℤ) : ℝ) < ((D * N + w : ℤ) : ℝ) := by
      push_cast at h7 ⊢
      exact h7
    exact_mod_cast h8
  · unfold badMeas
    have h1 := measure_mono (μ := volume) hsub
    rw [Real.volume_Ioo] at h1
    have hnn : (0 : ℝ) ≤ 2 / ((N : ℝ) * w) := by positivity
    have e : (((c0 : ℝ) + 1 / N) / w - ((c0 : ℝ) - 1 / N) / w) = 2 / ((N : ℝ) * w) := by
      field_simp
      ring
    rw [e] at h1
    exact ENNReal.toReal_le_of_le_ofReal hnn h1
  · have hsubJ : {t : ℝ | t ∈ Set.Icc ((a : ℝ) / D - lwd N) ((a : ℝ) / D + lwd N) ∧
        nearestIntDist ((w : ℝ) * t) < 1 / (N : ℝ)} ⊆
        Set.Icc (max (((c0 : ℝ) - 1 / N) / w) ((a : ℝ) / D - lwd N))
          (min (((c0 : ℝ) + 1 / N) / w) ((a : ℝ) / D + lwd N)) := by
      intro t ht
      have h := hsub ht
      exact ⟨max_le h.1.le ht.1.1, le_min h.2.le ht.1.2⟩
    have h1 := measure_mono (μ := volume) hsubJ
    rw [Real.volume_Icc] at h1
    unfold badMeas
    refine (ENNReal.toReal_mono ENNReal.ofReal_ne_top h1).trans ?_
    rw [ENNReal.toReal_ofReal']
    unfold lam
    have hs : -(((a * w - c0 * D : ℤ)) : ℝ) / ((w : ℝ) * D) = (c0 : ℝ) / w - (a : ℝ) / D := by
      push_cast
      field_simp
      ring
    rw [hs]
    have e1 : ((c0 : ℝ) + 1 / N) / w =
        (a : ℝ) / D + ((c0 : ℝ) / w - (a : ℝ) / D + 1 / ((N : ℝ) * w)) := by
      field_simp
      ring
    have e2 : ((c0 : ℝ) - 1 / N) / w =
        (a : ℝ) / D + ((c0 : ℝ) / w - (a : ℝ) / D - 1 / ((N : ℝ) * w)) := by
      field_simp
      ring
    have e3 : (a : ℝ) / D - lwd N = (a : ℝ) / D + (-lwd N) := by ring
    rw [e1, e2, e3, min_add_add_left, max_add_add_left, add_sub_add_left_eq_sub, max_comm]

/-- **Lemma 3.** A non-oscillating speed meets a window in one arc. -/
theorem arc_data {N r w D : ℕ} (a b : ℤ) (hab : a * (r : ℤ) + b * (D : ℤ) = 1)
    (hN : 10 ≤ N) (hD0 : 0 < D) (hD : D + 1 ≤ 2 * N) (hw : N < w)
    (hsm : 2 * (w : ℝ) ≤ (2 * (N : ℝ) - 1) * N * (N - 2))
    (hpos : 0 < badMeas N w ((a : ℝ) / D - lwd N) ((a : ℝ) / D + lwd N)) :
    ∃ e : ℤ, (D : ℤ) ∣ (w : ℤ) - e * r ∧ |e| * (N : ℤ) ^ 2 < D * N + w ∧
      badMeas N w ((a : ℝ) / D - lwd N) ((a : ℝ) / D + lwd N) ≤ 2 / ((N : ℝ) * w) := by
  obtain ⟨e, h1, h2, h3, _⟩ := arc_data' a b hab hN hD0 hD hw hsm hpos
  exact ⟨e, h1, h2, h3⟩

end LinL
end Gap
end Sext6
end LRSpectrumFull
