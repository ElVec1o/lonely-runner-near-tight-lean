import LRSpectrumFull.Sext6.Gap.KStarMain

/-!
# Theorem K*, part 7: Corollary B = Kravitz Theorem 5.1  [2026-11-25]

Source: the accompanying notes on Theorem K*, section 6.

For `n = k + 2 ≥ 3` and `s ≥ 1`:  `ML (1, 2, …, n-1, n s) = s / (n s + 1)`.

Derived from `K_eq` with `B = [N]` (`N = k+1`), `L = 1/(N+1)`, `vμ = 1`, `L2 ≤ 1/(N+2)` (`L2_vInt_le`),
`D = N + 1` (every equality time is `a/(N+1)`), `w = (N+1) s`.
No `sorry`, no `axiom`.

Convention: `v : Fin (k+1) → ℤ` has `k + 1` speeds and `(v, w) = Fin.snoc v w` has `k + 2`; for the base `[N]` one has `N = k + 1`. Speeds are the moving runners; the runner at rest is not counted, so a vector of `N` speeds means `N + 1` runners and the Lonely Runner value is `1/(N+1)`.
Hypotheses: those of the individual statements (numerical bounds, structural conditions and, where named in the list above, window predicates such as `PrimeWin`, `CopWin`, `PrimeWindow7`, which later modules discharge for explicit ranges). The unproved predicates `DusartPi`, `LRCHyp`, `CopWinHyp` are not hypotheses of any statement in this module.
Axiom audit: covered by `Axioms15` (`#print axioms`; declarations not printed there are bricks of printed ones, so their axioms are bounded by the printed lines).
-/

namespace LRSpectrumFull
namespace Sext6
namespace Gap

lemma vInt_cast (k : ℕ) (i : Fin (k + 1)) : ((vInt k i : ℤ) : ℝ) = ((i : ℕ) : ℝ) + 1 := by
  simp [vInt]

/-- `ML [N] = 1/(N+1)` (`N = k + 1`): Dirichlet above, the time `1/(N+1)` below. -/
theorem ML_vInt_eq (k : ℕ) : ML (vInt k) = 1 / ((k : ℝ) + 2) := by
  have hk2 : (0 : ℝ) < (k : ℝ) + 2 := by positivity
  apply le_antisymm (ML_vInt_le k)
  apply ML_ge_of_far (vInt k) _ (1 / ((k : ℝ) + 2))
  intro i
  rw [vInt_cast]
  have hi : (i : ℕ) ≤ k := Nat.lt_succ_iff.mp i.isLt
  have hi' : ((i : ℕ) : ℝ) ≤ k := by exact_mod_cast hi
  have hi0 : (0 : ℝ) ≤ ((i : ℕ) : ℝ) := Nat.cast_nonneg _
  have e : (((i : ℕ) : ℝ) + 1) * (1 / ((k : ℝ) + 2)) = (((i : ℕ) : ℝ) + 1) / ((k : ℝ) + 2) :=
    mul_one_div _ _
  rw [e]
  refine nearestIntDist_ge (c := 1 / ((k : ℝ) + 2)) (by positivity) ?_ ?_ ?_
  · rw [div_lt_one hk2]
    linarith
  · refine div_le_div_of_nonneg_right ?_ hk2.le
    linarith
  · have h : (((i : ℕ) : ℝ) + 1) / ((k : ℝ) + 2) + 1 / ((k : ℝ) + 2) ≤ 1 := by
      rw [← add_div, div_le_one hk2]
      linarith
    linarith

theorem ML_vInt_pos (k : ℕ) : 0 < ML (vInt k) := by
  rw [ML_vInt_eq]
  positivity

theorem ML_vInt_lt_half (k : ℕ) (hk : 1 ≤ k) : ML (vInt k) < 1 / 2 := by
  rw [ML_vInt_eq]
  have hk' : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have : (0 : ℝ) < (k : ℝ) + 2 := by positivity
  rw [div_lt_div_iff₀ this (by norm_num)]
  linarith

/-- **Corollary B (Kravitz, Theorem 5.1).**  `n = k + 2 ≥ 3`, `s ≥ 1`:
`ML (1, …, n-1, n s) = s / (n s + 1)`. -/
theorem kravitz_5_1 (k s : ℕ) (hk : 1 ≤ k) (hs : 1 ≤ s) :
    ML (Fin.snoc (vInt k) (((k : ℤ) + 2) * (s : ℤ)) : Fin (k + 2) → ℤ) =
      (s : ℝ) / (((k : ℝ) + 2) * s + 1) := by
  have hk2 : (0 : ℝ) < (k : ℝ) + 2 := by positivity
  have hk2ne : (k : ℝ) + 2 ≠ 0 := hk2.ne'
  have hs1 : (1 : ℝ) ≤ s := by exact_mod_cast hs
  have hs0 : (0 : ℝ) < s := by linarith
  have hML := ML_vInt_eq k
  have hL0 := ML_vInt_pos k
  have hL1 := ML_vInt_lt_half k hk
  have hwR : (((((k : ℤ) + 2) * (s : ℤ) : ℤ)) : ℝ) = ((k : ℝ) + 2) * s := by simp
  have hw : (0 : ℤ) < ((k : ℤ) + 2) * (s : ℤ) := by
    have : (0 : ℤ) < (s : ℤ) := by exact_mod_cast hs
    positivity
  -- (V1) with vμ = 1
  have hV1 : ∀ p, gap (vInt k) p = ML (vInt k) →
      (∃ i : Fin (k + 1), ∃ n : ℤ, (1 : ℝ) ≤ (vInt k i : ℝ) ∧
          (vInt k i : ℝ) * p = n + ML (vInt k)) ∧
      (∃ j : Fin (k + 1), ∃ m : ℤ, (1 : ℝ) ≤ (vInt k j : ℝ) ∧
          (vInt k j : ℝ) * p = m - ML (vInt k)) := by
    intro p hp
    obtain ⟨i, j, n, m, hi, hj, -⟩ := local_max_structure (vInt k) (vInt_pos k) ((k : ℤ) + 1)
      (vInt_le k) p (isLocalMax_of_eq_ML _ p hp) (by rw [hp]; exact hL0) (by rw [hp]; exact hL1)
    rw [hp] at hi hj
    have h1 : (1 : ℝ) ≤ (vInt k i : ℝ) := by
      have h : (1 : ℤ) ≤ vInt k i := by
        have := vInt_pos k i
        omega
      exact_mod_cast h
    have h2 : (1 : ℝ) ≤ (vInt k j : ℝ) := by
      have h : (1 : ℤ) ≤ vInt k j := by
        have := vInt_pos k j
        omega
      exact_mod_cast h
    exact ⟨⟨i, n, h1, hi⟩, ⟨j, m, h2, hj⟩⟩
  -- (hL2) from L2_vInt_le
  have hL2 : ∀ p, IsLocalMax (gap (vInt k)) p → gap (vInt k) p < ML (vInt k) →
      gap (vInt k) p ≤ 1 / ((k : ℝ) + 3) := fun p hp hlt => L2_vInt_le k p hp hlt
  -- D | w : every equality time is a/(k+2)
  have hDw : ∀ p, gap (vInt k) p = ML (vInt k) →
      ∃ z : ℤ, ((((k : ℤ) + 2) * (s : ℤ) : ℤ) : ℝ) * p = z := by
    intro p hp
    obtain ⟨a, d, hd, hdM, hpa, b, hb⟩ := equality_time_rational (vInt k) (vInt_pos k)
      ((k : ℤ) + 1) (vInt_le k) p hp hL0 hL1
    have hdR : (0 : ℝ) < d := by exact_mod_cast hd
    have hbd : (b : ℝ) / d = 1 / ((k : ℝ) + 2) := hb.symm.trans hML
    rw [div_eq_div_iff hdR.ne' hk2ne] at hbd
    have hbd' : b * ((k : ℤ) + 2) = d := by
      have : (b : ℝ) * ((k : ℝ) + 2) = d := by linarith
      exact_mod_cast this
    have hb0 : 0 < b := by
      by_contra h
      push_neg at h
      have : (0 : ℤ) < d := by exact_mod_cast hd
      nlinarith [mul_nonneg (neg_nonneg.mpr h) (by positivity : (0 : ℤ) ≤ (k : ℤ) + 2)]
    have hb1 : b = 1 := by
      by_contra h
      have h2 : 2 ≤ b := by omega
      nlinarith [mul_nonneg (sub_nonneg.mpr h2) (by positivity : (0 : ℤ) ≤ (k : ℤ) + 2)]
    subst hb1
    have hdk : (d : ℝ) = (k : ℝ) + 2 := by
      have : (d : ℤ) = (k : ℤ) + 2 := by linarith
      exact_mod_cast this
    refine ⟨(s : ℤ) * a, ?_⟩
    rw [hpa, hwR, hdk]
    push_cast
    field_simp <;> ring
  -- the equality time 1/(k+2)
  have hfar : ∀ i, ML (vInt k) ≤ nearestIntDist ((vInt k i : ℝ) * (((1 : ℤ) : ℝ) / ((k + 2 : ℕ) : ℝ))) := by
    intro i
    have e : (((1 : ℤ) : ℝ) / ((k + 2 : ℕ) : ℝ)) = 1 / ((k : ℝ) + 2) := by simp
    rw [e, hML, vInt_cast]
    have hi : (i : ℕ) ≤ k := Nat.lt_succ_iff.mp i.isLt
    have hi' : ((i : ℕ) : ℝ) ≤ k := by exact_mod_cast hi
    have hi0 : (0 : ℝ) ≤ ((i : ℕ) : ℝ) := Nat.cast_nonneg _
    have e2 : (((i : ℕ) : ℝ) + 1) * (1 / ((k : ℝ) + 2)) = (((i : ℕ) : ℝ) + 1) / ((k : ℝ) + 2) :=
      mul_one_div _ _
    rw [e2]
    refine nearestIntDist_ge (c := 1 / ((k : ℝ) + 2)) (by positivity) ?_ ?_ ?_
    · rw [div_lt_one hk2]
      linarith
    · refine div_le_div_of_nonneg_right ?_ hk2.le
      linarith
    · have h : (((i : ℕ) : ℝ) + 1) / ((k : ℝ) + 2) + 1 / ((k : ℝ) + 2) ≤ 1 := by
        rw [← add_div, div_le_one hk2]
        linarith
      linarith
  have hat0 : gap (vInt k) (((1 : ℤ) : ℝ) / ((k + 2 : ℕ) : ℝ)) = ML (vInt k) := by
    apply le_antisymm
    · exact le_csSup (bddAbove_range_gap _) ⟨_, rfl⟩
    · exact le_gap _ _ _ hfar
  have hext : ∀ i (n : ℤ), (vInt k i : ℝ) * (((1 : ℤ) : ℝ) / ((k + 2 : ℕ) : ℝ)) = n + ML (vInt k) →
      (vInt k i : ℝ) ≤ (1 : ℝ) := by
    intro i n hn
    have e : (((1 : ℤ) : ℝ) / ((k + 2 : ℕ) : ℝ)) = 1 / ((k : ℝ) + 2) := by simp
    rw [e, hML] at hn
    have hv1 : (vInt k i : ℝ) = (n : ℝ) * ((k : ℝ) + 2) + 1 := by
      field_simp at hn
      linarith
    have hv1' : vInt k i = n * ((k : ℤ) + 2) + 1 := by exact_mod_cast hv1
    have hlo := vInt_pos k i
    have hhi := vInt_le k i
    have hn0 : n = 0 := by
      by_contra hne
      rcases lt_or_gt_of_ne hne with h | h
      · nlinarith [mul_nonneg (by omega : (0 : ℤ) ≤ -n - 1) (by positivity : (0 : ℤ) ≤ (k : ℤ) + 2)]
      · nlinarith [mul_nonneg (by omega : (0 : ℤ) ≤ n - 1) (by positivity : (0 : ℤ) ≤ (k : ℤ) + 2)]
    rw [hn0] at hv1'
    have : vInt k i ≤ 1 := by omega
    exact_mod_cast this
  have hsize : ML (vInt k) * ((k + 2 : ℕ) : ℝ) * (((k : ℤ) + 1 : ℤ) : ℝ) ≤
      ((((k : ℤ) + 2) * (s : ℤ) : ℤ) : ℝ) + (1 : ℝ) := by
    rw [hML, hwR]
    push_cast
    have e : 1 / ((k : ℝ) + 2) * ((k : ℝ) + 2) * ((k : ℝ) + 1) = (k : ℝ) + 1 := by
      field_simp
    have hmul : ((k : ℝ) + 2) * 1 ≤ ((k : ℝ) + 2) * s := mul_le_mul_of_nonneg_left hs1 hk2.le
    linarith [e, hmul]
  have hKeq : ((((k : ℤ) + 2) * (s : ℤ) : ℤ) : ℝ) * ML (vInt k) /
      ((((k : ℤ) + 2) * (s : ℤ) : ℤ) + (1 : ℝ)) = (s : ℝ) / (((k : ℝ) + 2) * s + 1) := by
    rw [hML, hwR]
    have e : ((k : ℝ) + 2) * s * (1 / ((k : ℝ) + 2)) = s := by field_simp <;> ring
    rw [e]
  have hK : 1 / ((k : ℝ) + 3) ≤
      ((((k : ℤ) + 2) * (s : ℤ) : ℤ) : ℝ) * ML (vInt k) /
        ((((k : ℤ) + 2) * (s : ℤ) : ℤ) + (1 : ℝ)) := by
    rw [hKeq]
    have hk3 : (0 : ℝ) < (k : ℝ) + 3 := by positivity
    have hden : (0 : ℝ) < ((k : ℝ) + 2) * s + 1 := by positivity
    rw [div_le_div_iff₀ hk3 hden]
    nlinarith
  have hLl : ML (vInt k) = ((1 : ℤ) : ℝ) / ((k + 2 : ℕ) : ℝ) := by
    rw [hML]; simp
  have := K_eq (vInt k) (vInt_pos k) ((k : ℤ) + 1) (vInt_le k) (((k : ℤ) + 2) * (s : ℤ)) hw
    (ML (vInt k)) 1 (1 / ((k : ℝ) + 3)) rfl hL0 hL1 one_pos hV1 hL2 hDw (k + 2) (by omega) 1 1
    hLl hat0 (Or.inr hext) hsize hK
  rw [this, hKeq]

end Gap
end Sext6
end LRSpectrumFull
