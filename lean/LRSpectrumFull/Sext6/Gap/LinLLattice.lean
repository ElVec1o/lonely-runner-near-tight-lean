import LRSpectrumFull.Sext6.Gap.LinLMeas

/-!
# Theorem L (linear robustness), module 5: the lattice identity  [2026-11-25]

Source: the accompanying notes on Theorem L, Lemma 5(ii).  A closed interval of length `4σ` contains four lattice points of
`σ ℤ` for almost every position, so the overlap lengths of the arcs `[-eσ - 2σ, -eσ + 2σ]` with a window
`[-d, d]` sum to at most `4 · (2d)`.

* `lam_neg`, `lam_mono_rho`, `lam_scale_le` : elementary monotonicity of the overlap length `lam`.
* `lam_le_vol`        : `lam ρ d p` is at most the Lebesgue measure of `(p-ρ, p+ρ) ∩ [-d, d]`.
* `lam_lattice_sum`   : `∑_{e ∈ E} lam (2σ) d (-eσ) ≤ 8 d` for every finite `E ⊆ ℤ`.
Measure theory is used only through `measure_mono`, `measure_union_le`, `measure_biUnion_finset`,
`Real.volume_Icc`, `Real.volume_Ioo` (no integrals).  No `sorry`, no `axiom`.

Convention: pure real analysis; no speed vector, no natural number `N` occurs.
Hypotheses: those of the individual statements.  Axiom audit: `Axioms26`.
-/

namespace LRSpectrumFull
namespace Sext6
namespace Gap
namespace LinL

open MeasureTheory

theorem lam_nonneg (ρ d s : ℝ) : 0 ≤ lam ρ d s := le_max_left _ _

theorem lam_neg (ρ d s : ℝ) : lam ρ d (-s) = lam ρ d s := by
  unfold lam
  congr 1
  simp only [min_def, max_def]
  split_ifs <;> linarith

theorem lam_mono_rho {ρ ρ' : ℝ} (d s : ℝ) (h : ρ ≤ ρ') : lam ρ d s ≤ lam ρ' d s := by
  unfold lam
  refine max_le_max le_rfl ?_
  simp only [min_def, max_def]
  split_ifs <;> linarith

theorem lam_anti {s0 s : ℝ} (ρ d : ℝ) (h0 : 0 ≤ s0) (h : s0 ≤ s) : lam ρ d s ≤ lam ρ d s0 := by
  unfold lam
  refine max_le_max le_rfl ?_
  simp only [min_def, max_def]
  split_ifs <;> linarith

/-- Scaling the position away from the window centre decreases the overlap. -/
theorem lam_scale_le {κ : ℝ} (hκ : 1 ≤ κ) (ρ d p : ℝ) : lam ρ d (κ * p) ≤ lam ρ d p := by
  rcases le_total 0 p with hp | hp
  · exact lam_anti ρ d hp (by nlinarith)
  · rw [← lam_neg ρ d (κ * p), ← lam_neg ρ d p]
    have : -(κ * p) = κ * (-p) := by ring
    rw [this]
    exact lam_anti ρ d (by linarith) (by nlinarith)

/-- The overlap length is at most the measure of the intersection. -/
theorem lam_le_vol {d : ℝ} (hd : 0 ≤ d) (ρ p : ℝ) :
    lam ρ d p ≤ (volume (Set.Ioo (p - ρ) (p + ρ) ∩ Set.Icc (-d) d)).toReal := by
  have hsub : Set.Ioo (max (p - ρ) (-d)) (min (p + ρ) d) ⊆
      Set.Ioo (p - ρ) (p + ρ) ∩ Set.Icc (-d) d := by
    intro x hx
    exact ⟨⟨lt_of_le_of_lt (le_max_left _ _) hx.1, lt_of_lt_of_le hx.2 (min_le_left _ _)⟩,
      ⟨(le_max_right _ _).trans hx.1.le, hx.2.le.trans (min_le_right _ _)⟩⟩
  have h1 := measure_mono (μ := volume) hsub
  rw [Real.volume_Ioo] at h1
  have hfin : volume (Set.Ioo (p - ρ) (p + ρ) ∩ Set.Icc (-d) d) ≠ ⊤ := by
    refine ne_top_of_le_ne_top (b := volume (Set.Icc (-d) d)) ?_ (measure_mono Set.inter_subset_right)
    rw [Real.volume_Icc]; exact ENNReal.ofReal_ne_top
  calc lam ρ d p = (ENNReal.ofReal (min (p + ρ) d - max (p - ρ) (-d))).toReal := by
        rw [ENNReal.toReal_ofReal']
        unfold lam
        rw [max_comm]
    _ ≤ _ := ENNReal.toReal_mono hfin h1

/-- The half-open cell `[mσ, (m+1)σ)`. -/
def cell (σ : ℝ) (m : ℤ) : Set ℝ := Set.Ico ((m : ℝ) * σ) (((m : ℝ) + 1) * σ)

theorem cell_disjoint {σ : ℝ} (hσ : 0 < σ) {m m' : ℤ} (h : m ≠ m') :
    Disjoint (cell σ m) (cell σ m') := by
  rw [Set.disjoint_left]
  intro x hx hx'
  simp only [cell, Set.mem_Ico] at hx hx'
  rcases lt_or_gt_of_ne h with hlt | hgt
  · have h1 : (m : ℝ) + 1 ≤ m' := by exact_mod_cast (by omega : m + 1 ≤ m')
    nlinarith [mul_le_mul_of_nonneg_right h1 hσ.le]
  · have h1 : (m' : ℝ) + 1 ≤ m := by exact_mod_cast (by omega : m' + 1 ≤ m)
    nlinarith [mul_le_mul_of_nonneg_right h1 hσ.le]

theorem cell_sum_le {σ : ℝ} (hσ : 0 < σ) (J : Set ℝ) (hJ : MeasurableSet J) (E : Finset ℤ) (c : ℤ) :
    ∑ e ∈ E, volume (cell σ (-e + c) ∩ J) ≤ volume J := by
  rw [← measure_biUnion_finset]
  · exact measure_mono (Set.iUnion₂_subset (fun e _ => Set.inter_subset_right))
  · intro e _ e' _ hne
    show Disjoint (cell σ (-e + c) ∩ J) (cell σ (-e' + c) ∩ J)
    exact (cell_disjoint hσ (by omega)).mono Set.inter_subset_left Set.inter_subset_left
  · intro e _
    exact measurableSet_Ico.inter hJ

/-- **The lattice identity (inequality form).** -/
theorem lam_lattice_sum {σ d : ℝ} (hσ : 0 < σ) (hd : 0 ≤ d) (E : Finset ℤ) :
    ∑ e ∈ E, lam (2 * σ) d (-(e : ℝ) * σ) ≤ 8 * d := by
  classical
  have hJ : MeasurableSet (Set.Icc (-d) d) := measurableSet_Icc
  have hJfin : volume (Set.Icc (-d) d) = ENNReal.ofReal (2 * d) := by
    rw [Real.volume_Icc]; congr 1; ring
  have hcov : ∀ e : ℤ, Set.Ioo (-(e : ℝ) * σ - 2 * σ) (-(e : ℝ) * σ + 2 * σ) ∩ Set.Icc (-d) d ⊆
      (cell σ (-e + (-2)) ∩ Set.Icc (-d) d) ∪ (cell σ (-e + (-1)) ∩ Set.Icc (-d) d) ∪
      (cell σ (-e + 0) ∩ Set.Icc (-d) d) ∪ (cell σ (-e + 1) ∩ Set.Icc (-d) d) := by
    intro e x hx
    obtain ⟨⟨h1, h2⟩, hxJ⟩ := hx
    simp only [Set.mem_union, Set.mem_inter_iff, cell, Set.mem_Ico]
    push_cast
    by_cases a1 : x < (-(e : ℝ) + (-2)) * σ + σ
    · left; left; left
      exact ⟨⟨by nlinarith, by nlinarith⟩, hxJ⟩
    · by_cases a2 : x < (-(e : ℝ) + (-1)) * σ + σ
      · left; left; right
        exact ⟨⟨by nlinarith, by nlinarith⟩, hxJ⟩
      · by_cases a3 : x < (-(e : ℝ) + 0) * σ + σ
        · left; right
          exact ⟨⟨by nlinarith, by nlinarith⟩, hxJ⟩
        · right
          exact ⟨⟨by nlinarith, by nlinarith⟩, hxJ⟩
  have hbound : ∀ e : ℤ,
      volume (Set.Ioo (-(e : ℝ) * σ - 2 * σ) (-(e : ℝ) * σ + 2 * σ) ∩ Set.Icc (-d) d) ≤
      volume (cell σ (-e + (-2)) ∩ Set.Icc (-d) d) + volume (cell σ (-e + (-1)) ∩ Set.Icc (-d) d) +
      volume (cell σ (-e + 0) ∩ Set.Icc (-d) d) + volume (cell σ (-e + 1) ∩ Set.Icc (-d) d) := by
    intro e
    refine (measure_mono (hcov e)).trans ?_
    exact (measure_union_le _ _).trans (add_le_add
      ((measure_union_le _ _).trans (add_le_add (measure_union_le _ _) le_rfl)) le_rfl)
  have hsum : ∑ e ∈ E, volume (Set.Ioo (-(e : ℝ) * σ - 2 * σ) (-(e : ℝ) * σ + 2 * σ) ∩
      Set.Icc (-d) d) ≤ 4 * ENNReal.ofReal (2 * d) := by
    calc ∑ e ∈ E, volume (Set.Ioo (-(e : ℝ) * σ - 2 * σ) (-(e : ℝ) * σ + 2 * σ) ∩ Set.Icc (-d) d)
        ≤ ∑ e ∈ E, (volume (cell σ (-e + (-2)) ∩ Set.Icc (-d) d) +
            volume (cell σ (-e + (-1)) ∩ Set.Icc (-d) d) +
            volume (cell σ (-e + 0) ∩ Set.Icc (-d) d) + volume (cell σ (-e + 1) ∩ Set.Icc (-d) d)) :=
          Finset.sum_le_sum (fun e _ => hbound e)
      _ = ∑ e ∈ E, volume (cell σ (-e + (-2)) ∩ Set.Icc (-d) d) +
          ∑ e ∈ E, volume (cell σ (-e + (-1)) ∩ Set.Icc (-d) d) +
          ∑ e ∈ E, volume (cell σ (-e + 0) ∩ Set.Icc (-d) d) +
          ∑ e ∈ E, volume (cell σ (-e + 1) ∩ Set.Icc (-d) d) := by
        simp only [Finset.sum_add_distrib]
      _ ≤ volume (Set.Icc (-d) d) + volume (Set.Icc (-d) d) + volume (Set.Icc (-d) d) +
          volume (Set.Icc (-d) d) :=
        add_le_add (add_le_add (add_le_add (cell_sum_le hσ _ hJ E (-2)) (cell_sum_le hσ _ hJ E (-1)))
          (cell_sum_le hσ _ hJ E 0)) (cell_sum_le hσ _ hJ E 1)
      _ = 4 * ENNReal.ofReal (2 * d) := by rw [hJfin]; ring
  have hfin : ∀ e ∈ E, volume (Set.Ioo (-(e : ℝ) * σ - 2 * σ) (-(e : ℝ) * σ + 2 * σ) ∩
      Set.Icc (-d) d) ≠ ⊤ := by
    intro e _
    refine ne_top_of_le_ne_top (b := volume (Set.Icc (-d) d)) ?_ (measure_mono Set.inter_subset_right)
    rw [hJfin]; exact ENNReal.ofReal_ne_top
  have e4 : (4 : ENNReal).toReal = 4 := by norm_num
  calc ∑ e ∈ E, lam (2 * σ) d (-(e : ℝ) * σ)
      ≤ ∑ e ∈ E, (volume (Set.Ioo (-(e : ℝ) * σ - 2 * σ) (-(e : ℝ) * σ + 2 * σ) ∩
          Set.Icc (-d) d)).toReal := Finset.sum_le_sum (fun e _ => lam_le_vol hd (2 * σ) _)
    _ = (∑ e ∈ E, volume (Set.Ioo (-(e : ℝ) * σ - 2 * σ) (-(e : ℝ) * σ + 2 * σ) ∩
          Set.Icc (-d) d)).toReal := (ENNReal.toReal_sum hfin).symm
    _ ≤ (4 * ENNReal.ofReal (2 * d)).toReal :=
        ENNReal.toReal_mono (ENNReal.mul_ne_top (by norm_num) ENNReal.ofReal_ne_top) hsum
    _ = 8 * d := by
        rw [ENNReal.toReal_mul, e4, ENNReal.toReal_ofReal (by linarith)]
        ring

end LinL
end Gap
end Sext6
end LRSpectrumFull
