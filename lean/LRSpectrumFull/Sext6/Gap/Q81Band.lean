import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Topology.Order.DenselyOrdered
import Mathlib.Topology.Algebra.Order.Field
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FunProp
import LRSpectrumFull.NearestIntLipschitz

/-!
# Q8.1, Theorem BC: the band lemma (Lemma R of the notes (part 2) section 2)  [2026-11-25]

Source: the accompanying notes on Zhang's Question 8.1 sections 2 (Lemma B, Lemma R, Corollary R1) and 4.
Pure real analysis.  For a "free class" `t = (c + η)/M`, `η ∈ (0, 1/A]` (no retained speed within `1/A` of an
integer), an inserted multiple `m M` of the modulus is within `1/A` only for `η ≤ 1/(A m)` or `η ≥ (A-1)/(A m)`;
on the open window in between the other inserted speed `p` must cover, hence (affine in `η`, bands of one speed
are separated) lies in ONE band `|p η - z| ≤ M/A`, `z ≡ -p c (mod M)`:

* `same_band`        : two covered points of the window share the nearest integer (intermediate value).
* `uniform_band`     : one integer `n` works on the whole closed window (closure of the open window).
* `free_class_band`  : the integer inequalities `m (z A - M) ≤ p` and `p min(N/m, 1) ≤ z A + M`.
No `sorry`, no `axiom`.

Convention: No speed vector is involved in this module (number theory or real analysis); `N` denotes a natural number, the size of the ambient interval `[1,N]`.
Hypotheses: those of the individual statements (numerical bounds, structural conditions and, where named in the list above, window predicates such as `PrimeWin`, `CopWin`, `PrimeWindow7`, which later modules discharge for explicit ranges). The unproved predicates `DusartPi`, `LRCHyp`, `CopWinHyp` are not hypotheses of any statement in this module.
Axiom audit: covered by `Axioms8` (`#print axioms`; declarations not printed there are bricks of printed ones, so their axioms are bounded by the printed lines).
-/

namespace LRSpectrumFull
namespace Sext6
namespace Gap

/-- `x ∈ (θ, 1 - θ)` gives `θ < ‖x‖`. -/
theorem nid_gt_of_mem {x θ : ℝ} (hθ : 0 ≤ θ) (h1 : θ < x) (h2 : x < 1 - θ) :
    θ < nearestIntDist x := by
  have hx0 : 0 ≤ x := by linarith
  have hx1 : x < 1 := by linarith
  unfold nearestIntDist
  rw [Int.fract_eq_self.mpr ⟨hx0, hx1⟩]
  exact lt_min h1 (by linarith)

/-- `‖n + 1/2‖ ≥ 1/2`. -/
theorem nid_half (n : ℤ) : (1 : ℝ) / 2 ≤ nearestIntDist (((n : ℝ)) + 1 / 2) := by
  rw [add_comm, nearestIntDist_add_int]
  exact nearestIntDist_ge (by norm_num) (by norm_num) (by norm_num) (by norm_num)

/-- Two covered points of an affine window share the same nearest integer. -/
theorem same_band {σ g0 θ L U : ℝ} (hσ : 0 < σ) (hθ4 : θ ≤ 1 / 4)
    (hcov : ∀ η, L < η → η < U → nearestIntDist (σ * η + g0) ≤ θ)
    {η1 η2 : ℝ} (h1 : L < η1) (h12 : η1 < η2) (h2 : η2 < U) {n1 n2 : ℤ}
    (e1 : |σ * η1 + g0 - n1| ≤ θ) (e2 : |σ * η2 + g0 - n2| ≤ θ) : n1 = n2 := by
  by_contra hne
  obtain ⟨e1a, e1b⟩ := abs_le.mp e1
  obtain ⟨e2a, e2b⟩ := abs_le.mp e2
  have hmono : σ * η1 + g0 < σ * η2 + g0 := by nlinarith [mul_pos hσ (sub_pos.mpr h12)]
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · have hn : (n1 : ℝ) + 1 ≤ n2 := by exact_mod_cast hlt
    -- intermediate point with value n1 + 1/2
    obtain ⟨ηm, hηm⟩ : ∃ ηm : ℝ, ηm = η1 + ((n1 : ℝ) + 1 / 2 - (σ * η1 + g0)) / σ := ⟨_, rfl⟩
    have hval : σ * ηm + g0 = (n1 : ℝ) + 1 / 2 := by
      rw [hηm]
      field_simp
      try ring
    have hq0 : 0 < ((n1 : ℝ) + 1 / 2 - (σ * η1 + g0)) / σ := by
      apply div_pos _ hσ
      linarith
    have hq1 : ((n1 : ℝ) + 1 / 2 - (σ * η1 + g0)) / σ < η2 - η1 := by
      rw [div_lt_iff₀ hσ]
      nlinarith
    have hm1 : L < ηm := by rw [hηm]; linarith
    have hm2 : ηm < U := by rw [hηm]; linarith
    have hc := hcov ηm hm1 hm2
    rw [hval] at hc
    have := nid_half n1
    linarith
  · have hn : (n2 : ℝ) + 1 ≤ n1 := by exact_mod_cast hgt
    linarith

/-- One integer works on the whole closed window. -/
theorem uniform_band {σ g0 θ L U : ℝ} (hσ : 0 < σ) (hθ4 : θ ≤ 1 / 4) (hLU : L < U)
    (hcov : ∀ η, L < η → η < U → nearestIntDist (σ * η + g0) ≤ θ) :
    ∃ n : ℤ, ∀ η, L ≤ η → η ≤ U → |σ * η + g0 - n| ≤ θ := by
  obtain ⟨η0, hη0⟩ : ∃ η0 : ℝ, η0 = (L + U) / 2 := ⟨_, rfl⟩
  have hη0a : L < η0 := by rw [hη0]; linarith
  have hη0b : η0 < U := by rw [hη0]; linarith
  obtain ⟨n0, hn0⟩ := nearestIntDist_eq_abs (σ * η0 + g0)
  have hn0' : |σ * η0 + g0 - n0| ≤ θ := by rw [← hn0]; exact hcov η0 hη0a hη0b
  have hopen : ∀ η, L < η → η < U → |σ * η + g0 - n0| ≤ θ := by
    intro η hηa hηb
    obtain ⟨n, hn⟩ := nearestIntDist_eq_abs (σ * η + g0)
    have hn' : |σ * η + g0 - n| ≤ θ := by rw [← hn]; exact hcov η hηa hηb
    rcases lt_trichotomy η η0 with hlt | heq | hgt
    · have := same_band hσ hθ4 hcov hηa hlt hη0b hn' hn0'
      rw [← this]; exact hn'
    · rw [heq]; exact hn0'
    · have := same_band hσ hθ4 hcov hη0a hgt hηb hn0' hn'
      rw [this]; exact hn'
  refine ⟨n0, ?_⟩
  intro η hηL hηU
  have hsub : Set.Ioo L U ⊆ {x : ℝ | |σ * x + g0 - n0| ≤ θ} := by
    intro x hx
    exact hopen x hx.1 hx.2
  have hclosed : IsClosed {x : ℝ | |σ * x + g0 - n0| ≤ θ} :=
    isClosed_le (continuous_abs.comp (by fun_prop)) continuous_const
  have hcl : closure (Set.Ioo L U) ⊆ {x : ℝ | |σ * x + g0 - n0| ≤ θ} :=
    closure_minimal hsub hclosed
  have hmem : η ∈ closure (Set.Ioo L U) := by
    rw [closure_Ioo hLU.ne]
    exact ⟨hηL, hηU⟩
  exact hcl hmem

/-- **The band lemma** for a free class `t = (c + η)/M`:  if for every `η ∈ (0, 1/(N+1)]` either the multiple
`m M` of the modulus (`‖m η‖`) or the other inserted speed `p` is within `1/(N+1)` of an integer, then there is an
integer `z ≡ -p c (mod M)` with `m (z A - M) ≤ p` and `p · min(N/m, 1) ≤ z A + M`, where `A = N + 1`. -/
theorem free_class_band {N : ℝ} (hN : 4 ≤ N) (M m p : ℕ) (c : ℤ) (hM : 0 < M) (hm : 2 ≤ m)
    (hp : 0 < p)
    (hcov : ∀ η : ℝ, 0 < η → η ≤ 1 / (N + 1) →
      nearestIntDist ((m : ℝ) * η) ≤ 1 / (N + 1) ∨
      nearestIntDist ((p : ℝ) * (((c : ℝ) + η) / M)) ≤ 1 / (N + 1)) :
    ∃ z : ℤ, (M : ℤ) ∣ z + (p : ℤ) * c ∧
      (m : ℝ) * ((z : ℝ) * (N + 1) - M) ≤ p ∧
      (p : ℝ) * min (N / m) 1 ≤ (z : ℝ) * (N + 1) + M := by
  have hA : (0 : ℝ) < N + 1 := by linarith
  have hN0 : (0 : ℝ) < N := by linarith
  have hA0 : (N : ℝ) + 1 ≠ 0 := hA.ne'
  have hMR : (0 : ℝ) < M := by exact_mod_cast hM
  have hmR : (2 : ℝ) ≤ m := by exact_mod_cast hm
  have hmpos : (0 : ℝ) < m := by linarith
  have hm0 : (m : ℝ) ≠ 0 := hmpos.ne'
  have hM0 : (M : ℝ) ≠ 0 := by positivity
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp
  have hθ : (1 : ℝ) / (N + 1) ≤ 1 / 4 := by
    rw [div_le_div_iff₀ hA (by norm_num)]
    linarith
  have hθ0 : (0 : ℝ) < 1 / (N + 1) := by positivity
  -- the window
  obtain ⟨L, hL⟩ : ∃ L : ℝ, L = 1 / ((N + 1) * m) := ⟨_, rfl⟩
  obtain ⟨U, hU⟩ : ∃ U : ℝ, U = (1 / (N + 1)) * min (N / m) 1 := ⟨_, rfl⟩
  have hLpos : 0 < L := by rw [hL]; positivity
  have hmin_pos : 0 < min (N / (m : ℝ)) 1 := lt_min (div_pos (by linarith) hmpos) one_pos
  have hmin_le1 : min (N / (m : ℝ)) 1 ≤ 1 := min_le_right _ _
  have hmin_leN : min (N / (m : ℝ)) 1 ≤ N / m := min_le_left _ _
  have hLU : L < U := by
    rw [hL, hU]
    have h1 : (1 : ℝ) / m < min (N / (m : ℝ)) 1 := by
      apply lt_min
      · exact div_lt_div_of_pos_right (by linarith) hmpos
      · rw [div_lt_one hmpos]
        linarith
    have : 1 / ((N + 1) * (m : ℝ)) = (1 / (N + 1)) * (1 / m) := by
      field_simp
      try ring
    rw [this]
    exact mul_lt_mul_of_pos_left h1 hθ0
  have hUle : U ≤ 1 / (N + 1) := by
    rw [hU]
    calc (1 / (N + 1)) * min (N / (m : ℝ)) 1 ≤ (1 / (N + 1)) * 1 :=
        mul_le_mul_of_nonneg_left hmin_le1 hθ0.le
      _ = 1 / (N + 1) := by ring
  have hUN : (m : ℝ) * U ≤ N / (N + 1) := by
    rw [hU]
    have : (m : ℝ) * ((1 / (N + 1)) * min (N / (m : ℝ)) 1) =
        (1 / (N + 1)) * ((m : ℝ) * min (N / (m : ℝ)) 1) := by ring
    rw [this]
    have h2 : (m : ℝ) * min (N / (m : ℝ)) 1 ≤ N := by
      calc (m : ℝ) * min (N / (m : ℝ)) 1 ≤ (m : ℝ) * (N / m) :=
          mul_le_mul_of_nonneg_left hmin_leN hmpos.le
        _ = N := by field_simp
    calc (1 / (N + 1)) * ((m : ℝ) * min (N / (m : ℝ)) 1) ≤ (1 / (N + 1)) * N :=
        mul_le_mul_of_nonneg_left h2 hθ0.le
      _ = N / (N + 1) := by ring
  -- covering inside the window
  have hwin : ∀ η, L < η → η < U →
      nearestIntDist (((p : ℝ) / M) * η + ((p : ℝ) * c / M)) ≤ 1 / (N + 1) := by
    intro η hηL hηU
    have hη0 : 0 < η := lt_trans hLpos hηL
    have hη1 : η ≤ 1 / (N + 1) := by linarith
    have hmL : (m : ℝ) * L = 1 / (N + 1) := by
      rw [hL]
      field_simp
      try ring
    have hlow : 1 / (N + 1) < (m : ℝ) * η := by
      rw [← hmL]
      exact mul_lt_mul_of_pos_left hηL hmpos
    have hhigh : (m : ℝ) * η < 1 - 1 / (N + 1) := by
      have h3 : (m : ℝ) * η < (m : ℝ) * U := mul_lt_mul_of_pos_left hηU hmpos
      have h4 : (1 : ℝ) - 1 / (N + 1) = N / (N + 1) := by
        field_simp
        try ring
      rw [h4]
      linarith
    have hn : 1 / (N + 1) < nearestIntDist ((m : ℝ) * η) :=
      nid_gt_of_mem hθ0.le hlow hhigh
    rcases hcov η hη0 hη1 with h | h
    · exact absurd h (not_le.mpr hn)
    · have e : (p : ℝ) * (((c : ℝ) + η) / M) = ((p : ℝ) / M) * η + ((p : ℝ) * c / M) := by
        field_simp
        try ring
      rw [← e]
      exact h
  have hσ : 0 < (p : ℝ) / M := div_pos hpR hMR
  obtain ⟨n, hn⟩ := uniform_band hσ hθ hLU hwin
  refine ⟨(n : ℤ) * M - (p : ℤ) * c, ⟨n, by ring⟩, ?_, ?_⟩
  · -- lower end of the band
    have h := hn L le_rfl hLU.le
    obtain ⟨h1, _⟩ := abs_le.mp h
    have hz : (((n * M - p * c : ℤ)) : ℝ) = (n : ℝ) * M - (p : ℝ) * c := by push_cast; ring
    rw [hz]
    have h2 : (-(1 / (N + 1)) * (M * (N + 1))) ≤
        (((p : ℝ) / M) * L + ((p : ℝ) * c / M) - n) * (M * (N + 1)) :=
      mul_le_mul_of_nonneg_right h1 (by positivity)
    have h3 : (((p : ℝ) / M) * L + ((p : ℝ) * c / M) - n) * (M * (N + 1)) =
        (p : ℝ) * L * (N + 1) + (p : ℝ) * c * (N + 1) - n * M * (N + 1) := by
      field_simp
      try ring
    have h4 : (-(1 / (N + 1)) * (M * (N + 1))) = -(M : ℝ) := by
      field_simp
      try ring
    have h5 : L * (N + 1) = 1 / m := by
      rw [hL]
      field_simp
      try ring
    rw [h3, h4] at h2
    have h6 : (p : ℝ) * L * (N + 1) = (p : ℝ) * (1 / m) := by
      rw [mul_assoc, h5]
    have h7 : (m : ℝ) * ((p : ℝ) * (1 / m)) = p := by
      field_simp
      try ring
    have h8 : ((n : ℝ) * M - (p : ℝ) * c) * (N + 1) - M ≤ (p : ℝ) * (1 / m) := by
      linarith [h2, h6]
    have h9 := mul_le_mul_of_nonneg_left h8 hmpos.le
    rw [h7] at h9
    linarith
  · -- upper end of the band
    have h := hn U hLU.le le_rfl
    obtain ⟨_, h1⟩ := abs_le.mp h
    have hz : (((n * M - p * c : ℤ)) : ℝ) = (n : ℝ) * M - (p : ℝ) * c := by push_cast; ring
    rw [hz]
    have h2 : (((p : ℝ) / M) * U + ((p : ℝ) * c / M) - n) * (M * (N + 1)) ≤
        (1 / (N + 1)) * (M * (N + 1)) :=
      mul_le_mul_of_nonneg_right h1 (by positivity)
    have h3 : (((p : ℝ) / M) * U + ((p : ℝ) * c / M) - n) * (M * (N + 1)) =
        (p : ℝ) * (U * (N + 1)) + (p : ℝ) * c * (N + 1) - n * M * (N + 1) := by
      field_simp
      try ring
    have h4 : (1 / (N + 1)) * (M * (N + 1)) = (M : ℝ) := by
      field_simp
      try ring
    have h5 : U * (N + 1) = min (N / (m : ℝ)) 1 := by
      rw [hU]
      field_simp
      try ring
    rw [h3, h4, h5] at h2
    linarith [h2]

end Gap
end Sext6
end LRSpectrumFull
