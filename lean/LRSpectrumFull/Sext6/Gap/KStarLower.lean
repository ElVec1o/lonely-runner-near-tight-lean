import LRSpectrumFull.Sext6.Gap.KStarLocal

/-!
# Theorem K*, part 4: the lower bound (L)  [2026-11-25]

Source: the accompanying notes on Theorem K*, section 3.

`K_lower`: let `t0 = a/d` be a time at which every runner is at distance `≥ L = l/d` from an integer
(`0 < L < 1/2`), such that every runner sitting at `-L` has speed `≤ vμ`, `w t0 ∈ ℤ`, and
`L d M ≤ w + vμ` (`M` a bound for the speeds).  Then `ML (v, w) ≥ w L / (w + vμ)`.
`K_lower_plus` is the mirror image (the extremal runners sit at `+L`).
The size condition is stated with the *given* common denominator `d` of `t0` and `L` (the reduced denominator
is the best choice, but it is not needed).  The granularity argument is done with the residue `r = u a mod d`:
the only old runner that can fall below `L - vμ δ` is the one with `r = d - l`.
No `sorry`, no `axiom`.

Convention: `v : Fin (k+1) → ℤ` has `k + 1` speeds and `(v, w) = Fin.snoc v w` has `k + 2`; for the base `[N]` one has `N = k + 1`. Speeds are the moving runners; the runner at rest is not counted, so a vector of `N` speeds means `N + 1` runners and the Lonely Runner value is `1/(N+1)`.
Hypotheses: those of the individual statements (numerical bounds, structural conditions and, where named in the list above, window predicates such as `PrimeWin`, `CopWin`, `PrimeWindow7`, which later modules discharge for explicit ranges). The unproved predicates `DusartPi`, `LRCHyp`, `CopWinHyp` are not hypotheses of any statement in this module.
Axiom audit: covered by `Axioms15` (also reached through the imports of `Axioms19`, `Axioms20`) (`#print axioms`; declarations not printed there are bricks of printed ones, so their axioms are bounded by the printed lines).
-/

namespace LRSpectrumFull
namespace Sext6
namespace Gap

/-- One old runner `u` at the crossing time `a/d + δ`. -/
lemma old_runner_bound (d : ℕ) (hd : 0 < d) (a l u : ℤ) (L vμ δ : ℝ)
    (hLl : L = (l : ℝ) / d) (hL0 : 0 < L) (hL1 : L < 1 / 2)
    (hfar : L ≤ nearestIntDist ((u : ℝ) * ((a : ℝ) / d)))
    (hext : ∀ m : ℤ, (u : ℝ) * ((a : ℝ) / d) = m - L → (u : ℝ) ≤ vμ)
    (hu : 0 < u) (hδ : 0 ≤ δ) (hδd : (u : ℝ) * δ * d ≤ 1) (hvδ : vμ * δ ≤ L)
    (hvμ0 : 0 ≤ vμ) :
    L - vμ * δ ≤ nearestIntDist ((u : ℝ) * ((a : ℝ) / d + δ)) := by
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have hdne : (d : ℝ) ≠ 0 := hdR.ne'
  have huR : (0 : ℝ) < (u : ℝ) := by exact_mod_cast hu
  have hy0 : 0 ≤ (u : ℝ) * δ := mul_nonneg huR.le hδ
  obtain ⟨n, r, hr0, hrd, hN⟩ : ∃ n r : ℤ, 0 ≤ r ∧ r < d ∧ u * a = d * n + r :=
    ⟨u * a / d, u * a % d, Int.emod_nonneg _ (by omega), Int.emod_lt_of_pos _ (by omega),
      (Int.mul_ediv_add_emod (u * a) d).symm⟩
  have hNR : (u : ℝ) * (a : ℝ) = d * n + r := by exact_mod_cast hN
  obtain ⟨ρ, hρ⟩ : ∃ ρ : ℝ, ρ = (r : ℝ) / d := ⟨_, rfl⟩
  have hX : (u : ℝ) * ((a : ℝ) / d) = ρ + n := by
    rw [hρ]
    field_simp
    linear_combination hNR
  have hρ0 : 0 ≤ ρ := by rw [hρ]; exact div_nonneg (by exact_mod_cast hr0) hdR.le
  have hρ1 : ρ < 1 := by rw [hρ, div_lt_one hdR]; exact_mod_cast hrd
  have hρn : nearestIntDist ρ = min ρ (1 - ρ) := by
    have hf : Int.fract ρ = ρ := Int.fract_eq_self.mpr ⟨hρ0, hρ1⟩
    simp only [nearestIntDist, hf]
  rw [hX, nearestIntDist_add_int, hρn] at hfar
  obtain ⟨hLρ1, hLρ2⟩ := le_min_iff.mp hfar
  have e : (u : ℝ) * ((a : ℝ) / d + δ) = (ρ + (u : ℝ) * δ) + n := by linear_combination hX
  rw [e, nearestIntDist_add_int]
  by_cases hcase : ρ + (u : ℝ) * δ ≤ 1 - L
  · have h1 : L ≤ nearestIntDist (ρ + (u : ℝ) * δ) :=
      nearestIntDist_ge (by linarith) (by linarith) (by linarith) (by linarith)
    have h2 : 0 ≤ vμ * δ := mul_nonneg hvμ0 hδ
    linarith
  · push_neg at hcase
    have hl : (l : ℝ) = L * d := by rw [hLl]; field_simp
    have hrR : (r : ℝ) = ρ * d := by rw [hρ]; field_simp
    have hA : L * d ≤ (1 - ρ) * d := mul_le_mul_of_nonneg_right hLρ2 hdR.le
    have hB : (1 - L) * d < (ρ + (u : ℝ) * δ) * d := mul_lt_mul_of_pos_right hcase hdR
    have h1 : (r : ℝ) ≤ d - l := by linarith
    have h2 : (d : ℝ) - l - 1 < r := by nlinarith
    have h1i : r ≤ (d : ℤ) - l := by exact_mod_cast h1
    have h2i : (d : ℤ) - l - 1 < r := by exact_mod_cast h2
    have hreq : r = (d : ℤ) - l := by omega
    have hrR' : (r : ℝ) = d - l := by exact_mod_cast hreq
    have hρ' : ρ = 1 - L := by
      rw [hρ, hrR', hLl, sub_div, div_self hdne]
    have hu_le : (u : ℝ) ≤ vμ := hext (n + 1) (by rw [hX, hρ']; push_cast; ring)
    have hy_le : (u : ℝ) * δ ≤ vμ * δ := mul_le_mul_of_nonneg_right hu_le hδ
    have e2 : ρ + (u : ℝ) * δ = -(L - (u : ℝ) * δ) + ((1 : ℤ) : ℝ) := by
      rw [hρ']; push_cast; ring
    have hnn : nearestIntDist (L - (u : ℝ) * δ) = L - (u : ℝ) * δ :=
      nid_of_le_half (by linarith) (by linarith)
    rw [e2, nearestIntDist_add_int, nearestIntDist_neg, hnn]
    linarith

lemma snoc_castSucc_eq {k : ℕ} (v : Fin (k + 1) → ℤ) (w : ℤ) (j : Fin (k + 1)) :
    (Fin.snoc v w : Fin (k + 2) → ℤ) (Fin.castSucc j) = v j := by simp

lemma snoc_last_eq {k : ℕ} (v : Fin (k + 1) → ℤ) (w : ℤ) :
    (Fin.snoc v w : Fin (k + 2) → ℤ) (Fin.last (k + 1)) = w := by simp

/-- **(L), minus side.** -/
theorem K_lower {k : ℕ} (v : Fin (k + 1) → ℤ) (hv : ∀ i, 0 < v i) (M : ℤ) (hM : ∀ i, v i ≤ M)
    (w : ℤ) (hw : 0 < w) (L vμ : ℝ) (d : ℕ) (hd : 0 < d) (a l : ℤ)
    (hLl : L = (l : ℝ) / d) (hL0 : 0 < L) (hL1 : L < 1 / 2) (hvμ : 0 < vμ)
    (hfar : ∀ i, L ≤ nearestIntDist ((v i : ℝ) * ((a : ℝ) / d)))
    (hext : ∀ i (m : ℤ), (v i : ℝ) * ((a : ℝ) / d) = m - L → (v i : ℝ) ≤ vμ)
    (hwt0 : ∃ z : ℤ, (w : ℝ) * ((a : ℝ) / d) = z)
    (hsize : L * d * M ≤ (w : ℝ) + vμ) :
    (w : ℝ) * L / ((w : ℝ) + vμ) ≤ ML (Fin.snoc v w : Fin (k + 2) → ℤ) := by
  have hw' : (0 : ℝ) < w := by exact_mod_cast hw
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have hwv : (0 : ℝ) < (w : ℝ) + vμ := by linarith
  obtain ⟨δ, hδ⟩ : ∃ δ : ℝ, δ = L / ((w : ℝ) + vμ) := ⟨_, rfl⟩
  have hwvne : (w : ℝ) + vμ ≠ 0 := hwv.ne'
  have hδ0 : 0 < δ := by rw [hδ]; exact div_pos hL0 hwv
  have hδL : δ * ((w : ℝ) + vμ) = L := by rw [hδ]; field_simp
  have hKeq : (w : ℝ) * δ = (w : ℝ) * L / ((w : ℝ) + vμ) := by rw [hδ]; ring
  have hKL : (w : ℝ) * L / ((w : ℝ) + vμ) = L - vμ * δ := by
    rw [div_eq_iff hwv.ne']
    linear_combination vμ * hδL
  have hvδ : vμ * δ ≤ L := by
    have h1 : 0 ≤ (w : ℝ) * δ := mul_nonneg hw'.le hδ0.le
    have h2 : (w : ℝ) * δ = L - vμ * δ := by rw [hKeq, hKL]
    linarith
  have hMd : (M : ℝ) * δ * d * ((w : ℝ) + vμ) = L * d * M := by
    calc (M : ℝ) * δ * d * ((w : ℝ) + vμ) = (M : ℝ) * d * (δ * ((w : ℝ) + vμ)) := by ring
      _ = (M : ℝ) * d * L := by rw [hδL]
      _ = L * d * M := by ring
  have hMd1 : (M : ℝ) * δ * d ≤ 1 := by
    have h : (M : ℝ) * δ * d * ((w : ℝ) + vμ) ≤ 1 * ((w : ℝ) + vμ) := by
      rw [hMd]; linarith
    exact le_of_mul_le_mul_right h hwv
  apply ML_ge_of_far (Fin.snoc v w : Fin (k + 2) → ℤ) _ (((a : ℝ) / d) + δ)
  intro i
  rcases Fin.eq_castSucc_or_eq_last i with ⟨j, rfl⟩ | rfl
  · rw [snoc_castSucc_eq]
    have hvM : (v j : ℝ) ≤ M := by exact_mod_cast hM j
    have hδd : (v j : ℝ) * δ * d ≤ 1 := by
      have h1 : (v j : ℝ) * δ ≤ M * δ := mul_le_mul_of_nonneg_right hvM hδ0.le
      have h2 : (v j : ℝ) * δ * d ≤ M * δ * d := mul_le_mul_of_nonneg_right h1 hdR.le
      linarith
    have hb := old_runner_bound d hd a l (v j) L vμ δ hLl hL0 hL1 (hfar j) (hext j) (hv j)
      hδ0.le hδd hvδ hvμ.le
    rw [hKL]
    exact hb
  · rw [snoc_last_eq]
    obtain ⟨z, hz⟩ := hwt0
    have e : (w : ℝ) * ((a : ℝ) / d + δ) = (w : ℝ) * δ + z := by linear_combination hz
    have hKh : (w : ℝ) * δ ≤ 1 / 2 := by
      have h2 : (w : ℝ) * δ = L - vμ * δ := by rw [hKeq, hKL]
      have h3 : 0 ≤ vμ * δ := mul_nonneg hvμ.le hδ0.le
      linarith
    apply le_of_eq
    calc (w : ℝ) * L / ((w : ℝ) + vμ) = (w : ℝ) * δ := hKeq.symm
      _ = nearestIntDist ((w : ℝ) * δ) := (nid_of_le_half (mul_nonneg hw'.le hδ0.le) hKh).symm
      _ = nearestIntDist ((w : ℝ) * ((a : ℝ) / d + δ)) := by rw [e, nearestIntDist_add_int]

/-- **(L), plus side**: the mirror image `t ↦ -t`. -/
theorem K_lower_plus {k : ℕ} (v : Fin (k + 1) → ℤ) (hv : ∀ i, 0 < v i) (M : ℤ)
    (hM : ∀ i, v i ≤ M) (w : ℤ) (hw : 0 < w) (L vμ : ℝ) (d : ℕ) (hd : 0 < d) (a l : ℤ)
    (hLl : L = (l : ℝ) / d) (hL0 : 0 < L) (hL1 : L < 1 / 2) (hvμ : 0 < vμ)
    (hfar : ∀ i, L ≤ nearestIntDist ((v i : ℝ) * ((a : ℝ) / d)))
    (hext : ∀ i (n : ℤ), (v i : ℝ) * ((a : ℝ) / d) = n + L → (v i : ℝ) ≤ vμ)
    (hwt0 : ∃ z : ℤ, (w : ℝ) * ((a : ℝ) / d) = z)
    (hsize : L * d * M ≤ (w : ℝ) + vμ) :
    (w : ℝ) * L / ((w : ℝ) + vμ) ≤ ML (Fin.snoc v w : Fin (k + 2) → ℤ) := by
  have hneg : ((-a : ℤ) : ℝ) / d = -((a : ℝ) / d) := by rw [Int.cast_neg, neg_div]
  refine K_lower v hv M hM w hw L vμ d hd (-a) l hLl hL0 hL1 hvμ ?_ ?_ ?_ hsize
  · intro i
    rw [hneg, mul_neg, nearestIntDist_neg]
    exact hfar i
  · intro i m hm
    rw [hneg] at hm
    exact hext i (-m) (by push_cast; linarith)
  · obtain ⟨z, hz⟩ := hwt0
    exact ⟨-z, by rw [hneg]; push_cast; linarith⟩

end Gap
end Sext6
end LRSpectrumFull
