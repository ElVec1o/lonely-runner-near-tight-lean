import LRSpectrumFull.Sext6.Gap.KStarLower
import LRSpectrumFull.Delta2Boundary

/-!
# Theorem INS, part 1: the Lipschitz lower bound (LIP)  [2026-11-25]

Source: the accompanying notes on single-speed insertion, section 4.

* `gap_lower_lip` : if every runner of `v` is at distance `≥ L` from an integer at time `t0`, then
  `L - M |t - t0| ≤ gap v t` for every `t` (`M` bounds the speeds).
* `ML_snoc_ge_LIP` : for positive integer speeds `v ≤ M` and every positive integer `w`,
  `w * ML v / (w + M) ≤ ML (v, w)`.  No hypothesis on `w` beyond `0 < w` (`w` may already be a speed).
No `sorry`, no `axiom`.

Convention: `v : Fin (k+1) → ℤ` has `k + 1` speeds; `V = (v, w) = Fin.snoc v w` (integer `w`) has `N = k + 2` speeds (moving runners), i.e. `N + 1` runners counting the one at rest. The Lonely Runner value of `V` is `1/(N+1) = 1/(k+3)`; the threshold of D1, D2 is `1/N`.
Hypotheses: those of the individual statements (numerical bounds, structural conditions and, where named in the list above, window predicates such as `PrimeWin`, `CopWin`, `PrimeWindow7`, which later modules discharge for explicit ranges). The unproved predicates `DusartPi`, `LRCHyp`, `CopWinHyp` are not hypotheses of any statement in this module.
Axiom audit: covered by `Axioms20` (`#print axioms`; declarations not printed there are bricks of printed ones, so their axioms are bounded by the printed lines).
-/

namespace LRSpectrumFull
namespace Sext6
namespace Gap

/-- `gap v` is `M`-Lipschitz from below around a time at which all runners are `≥ L` away. -/
theorem gap_lower_lip {k : ℕ} (v : Fin (k + 1) → ℤ) (M : ℤ) (hM : ∀ i, v i ≤ M)
    (hv : ∀ i, 0 < v i) (L t0 t : ℝ)
    (hfar : ∀ i, L ≤ nearestIntDist ((v i : ℝ) * t0)) :
    L - (M : ℝ) * |t - t0| ≤ gap v t := by
  apply le_gap
  intro i
  have hvi : (0 : ℝ) < (v i : ℝ) := by exact_mod_cast hv i
  have hvM : (v i : ℝ) ≤ M := by exact_mod_cast hM i
  have hl := nearestIntDist_lipschitz ((v i : ℝ) * t0) ((v i : ℝ) * t)
  have h1 : |(v i : ℝ) * t0 - (v i : ℝ) * t| = (v i : ℝ) * |t - t0| := by
    rw [← mul_sub, abs_mul, abs_of_pos hvi, abs_sub_comm]
  rw [h1] at hl
  have h2 : (v i : ℝ) * |t - t0| ≤ (M : ℝ) * |t - t0| :=
    mul_le_mul_of_nonneg_right hvM (abs_nonneg _)
  have h3 := (abs_sub_le_iff.mp hl).1
  have h4 := hfar i
  linarith

/-- **LIP.** `w * ML v / (w + M) ≤ ML (v, w)` for every positive integer `w`. -/
theorem ML_snoc_ge_LIP {k : ℕ} (v : Fin (k + 1) → ℤ) (hv : ∀ i, 0 < v i) (M : ℤ)
    (hM : ∀ i, v i ≤ M) (w : ℤ) (hw : 0 < w) :
    (w : ℝ) * ML v / ((w : ℝ) + M) ≤ ML (Fin.snoc v w : Fin (k + 2) → ℤ) := by
  have hw' : (0 : ℝ) < (w : ℝ) := by exact_mod_cast hw
  have hM1 : 1 ≤ M := by
    have := hv 0
    have := hM 0
    omega
  have hMR : (1 : ℝ) ≤ (M : ℝ) := by exact_mod_cast hM1
  have hwM : (0 : ℝ) < (w : ℝ) + M := by linarith
  obtain ⟨t0, -, ht0⟩ := exists_gap_eq_ML v
  have hL0 : 0 ≤ ML v := ML_nonneg v
  have hLh : ML v ≤ 1 / 2 := ML_le_half v
  have hfar : ∀ i, ML v ≤ nearestIntDist ((v i : ℝ) * t0) := by
    intro i
    have := gap_le v t0 i
    rwa [ht0] at this
  obtain ⟨K, hK⟩ : ∃ K : ℝ, K = (w : ℝ) * ML v / ((w : ℝ) + M) := ⟨_, rfl⟩
  have hKw : K * ((w : ℝ) + M) = (w : ℝ) * ML v := by
    rw [hK]; field_simp
  have hK0 : 0 ≤ K := by
    rw [hK]; exact div_nonneg (mul_nonneg hw'.le hL0) hwM.le
  have hKL : K ≤ ML v := by
    rw [hK, div_le_iff₀ hwM]
    nlinarith [mul_nonneg hL0 (by linarith : (0 : ℝ) ≤ (M : ℝ))]
  have hK1 : K ≤ 1 / 2 := by linarith
  rw [← hK]
  obtain ⟨t, hgt, hwt⟩ : ∃ t : ℝ, K ≤ gap v t ∧ K ≤ nearestIntDist ((w : ℝ) * t) := by
    by_cases hphi : K ≤ nearestIntDist ((w : ℝ) * t0)
    · exact ⟨t0, by rw [ht0]; exact hKL, hphi⟩
    · push_neg at hphi
      obtain ⟨n, hn⟩ := nearestIntDist_eq_abs ((w : ℝ) * t0)
      obtain ⟨phi, hphidef⟩ : ∃ phi : ℝ, phi = nearestIntDist ((w : ℝ) * t0) := ⟨_, rfl⟩
      rw [← hphidef] at hn hphi
      have hphi0 : 0 ≤ phi := by rw [hphidef]; exact nearestIntDist_nonneg _
      obtain ⟨h, hh⟩ : ∃ h : ℝ, h = (K - phi) / (w : ℝ) := ⟨_, rfl⟩
      have hh0 : 0 ≤ h := by rw [hh]; exact div_nonneg (by linarith) hw'.le
      have hwh : (w : ℝ) * h = K - phi := by rw [hh]; field_simp
      have hMh : K ≤ ML v - (M : ℝ) * h := by
        have e : (w : ℝ) * (ML v - (M : ℝ) * h - K) =
            (w : ℝ) * ML v - (M : ℝ) * (K - phi) - (w : ℝ) * K := by
          rw [← hwh]; ring
        have hpos : 0 ≤ (w : ℝ) * (ML v - (M : ℝ) * h - K) := by
          rw [e]
          nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ (M : ℝ)) hphi0, hKw]
        have := nonneg_of_mul_nonneg_right hpos hw'
        linarith
      rcases le_or_gt 0 ((w : ℝ) * t0 - n) with he | he
      · have hab : |(w : ℝ) * t0 - n| = (w : ℝ) * t0 - n := abs_of_nonneg he
        refine ⟨t0 + h, ?_, ?_⟩
        · have hl := gap_lower_lip v M hM hv (ML v) t0 (t0 + h) hfar
          have habs : |t0 + h - t0| = h := by
            have e0 : t0 + h - t0 = h := by ring
            rw [e0]; exact abs_of_nonneg hh0
          rw [habs] at hl
          linarith
        · have e : (w : ℝ) * (t0 + h) = K + n := by
            have e1 : (w : ℝ) * (t0 + h) = (w : ℝ) * t0 + (w : ℝ) * h := by ring
            rw [e1, hwh]
            linarith
          rw [e, nearestIntDist_add_int, nid_of_le_half hK0 hK1]
      · have hab : |(w : ℝ) * t0 - n| = -((w : ℝ) * t0 - n) := abs_of_neg he
        refine ⟨t0 - h, ?_, ?_⟩
        · have hl := gap_lower_lip v M hM hv (ML v) t0 (t0 - h) hfar
          have habs : |t0 - h - t0| = h := by
            have e0 : t0 - h - t0 = -h := by ring
            rw [e0, abs_neg]; exact abs_of_nonneg hh0
          rw [habs] at hl
          linarith
        · have e : (w : ℝ) * (t0 - h) = -K + n := by
            have e1 : (w : ℝ) * (t0 - h) = (w : ℝ) * t0 - (w : ℝ) * h := by ring
            rw [e1, hwh]
            linarith
          rw [e, nearestIntDist_add_int, nearestIntDist_neg, nid_of_le_half hK0 hK1]
  apply ML_ge_of_far (Fin.snoc v w : Fin (k + 2) → ℤ) K t
  intro i
  rcases Fin.eq_castSucc_or_eq_last i with ⟨j, rfl⟩ | rfl
  · rw [snoc_castSucc_eq]
    exact hgt.trans (gap_le v t j)
  · rw [snoc_last_eq]
    exact hwt

end Gap
end Sext6
end LRSpectrumFull
