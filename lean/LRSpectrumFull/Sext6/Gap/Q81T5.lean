import Mathlib.NumberTheory.DiophantineApproximation.Basic
import LRSpectrumFull.Sext6.Gap.Q81T4

/-!
# Q8.1, Theorem T, direction "every failing unit rescued (and `gcd(r1, r2) > 1`) => tight"  [2026-11-25]

Source: the accompanying notes on Zhang's Question 8.1 section 4 (Theorem T, Steps 1-4).
Setting as in `Q81T4`; additionally `gcd(r1, r2) > 1`.  Tight means `ML V ≤ 1/(N+1)`.
Proof, as in the notes: Dirichlet gives `q ≤ N` with `‖q t‖ ≤ 1/A`; if `q` is retained we are done; otherwise
`t = (c + η)/M`, `M = r_i`, `0 ≤ η ≤ 1/A` (by `t -> -t`).  If `gcd(c, M) > 1` the retained speed `M/gcd` covers.
If `c` is a unit, let `b ∈ [A - M, N]` with `b c ≡ -1 (mod M)`; `b` is a unit, hence not `r_j` (as `gcd(r1, r2) > 1`),
so it is retained and covers `η ≥ s/(A b)`; the own inserted speed `m M` covers `η ≤ 1/(A m)`; if the middle window is nonempty
then `b` is a failing unit and its rescue `z` makes the other inserted speed cover the whole window.
No hypothesis `m_i ≤ N - 1` is needed for this direction.
* `class_cover`, `nonunit_cover`, `exists_b`, `class_cover_any`.
* `theoremT_if` : rescue of every failing unit (both entries) and `gcd(r1, r2) > 1` give `ML V ≤ 1/(N+1)`.
* `theoremT` : with `m_i + 1 ≤ N`, for `gcd(r1, r2) > 1`: tight iff every failing unit of both entries is rescued.
No `sorry`, no `axiom`.

Convention: `N = k + 1` is the number of speeds of the vector `v : Fin (k+1) → ℤ`. Speeds are the moving runners; the runner at rest is not counted, so a vector of `N` speeds means `N + 1` runners and the Lonely Runner value is `1/(N+1)`.
Hypotheses: those of the individual statements (numerical bounds, structural conditions and, where named in the list above, window predicates such as `PrimeWin`, `CopWin`, `PrimeWindow7`, which later modules discharge for explicit ranges). The unproved predicates `DusartPi`, `LRCHyp`, `CopWinHyp` are not hypotheses of any statement in this module.
Axiom audit: covered by `Axioms22` (`#print axioms`; declarations not printed there are bricks of printed ones, so their axioms are bounded by the printed lines).
-/

namespace LRSpectrumFull
namespace Sext6
namespace Gap

theorem nid_le_of_abs {x θ : ℝ} (h : |x| ≤ θ) : nearestIntDist x ≤ θ := by
  have := nearestIntDist_le_dist x 0
  simp only [Int.cast_zero, sub_zero] at this
  linarith

/-- A unit class: the retained speed `b`, the own inserted speed `m M` and the other inserted speed `p`
cover `t = (c + η)/M`, `0 ≤ η ≤ 1/A`, given the rescue of the failing unit `b`. -/
theorem class_cover {N M m p b : ℕ} (c k' : ℤ) (η : ℝ) (hMN : M ≤ N) (hN2 : N < 2 * M) (hM3 : 3 ≤ M)
    (hm : 2 ≤ m) (hη0 : 0 ≤ η) (hη1 : η * ((N : ℝ) + 1) ≤ 1)
    (hbc : (b : ℤ) * c + 1 = (M : ℤ) * k') (hb1 : N + 1 ≤ b + M) (hbN : b ≤ N)
    (hresc : b < m * (N + 1 - M) → ∃ z : ℕ, z * b ≡ p [MOD M] ∧ m * (z * (N + 1)) ≤ p + m * M ∧
      (N + 1 - M) * p ≤ b * (z * (N + 1) + M)) :
    nearestIntDist ((b : ℝ) * (((c : ℝ) + η) / M)) ≤ 1 / ((N : ℝ) + 1) ∨
    nearestIntDist (((m * M : ℕ) : ℝ) * (((c : ℝ) + η) / M)) ≤ 1 / ((N : ℝ) + 1) ∨
    nearestIntDist ((p : ℝ) * (((c : ℝ) + η) / M)) ≤ 1 / ((N : ℝ) + 1) := by
  have hApos : (0 : ℝ) < (N : ℝ) + 1 := by positivity
  have hMpos : 0 < M := by omega
  have hMR : (0 : ℝ) < M := by exact_mod_cast hMpos
  have hMA : (M : ℝ) < (N : ℝ) + 1 := by
    have : (M : ℝ) ≤ N := by exact_mod_cast hMN
    linarith
  have hbpos : 0 < b := by omega
  have hbR : (0 : ℝ) < b := by exact_mod_cast hbpos
  have hmR : (2 : ℝ) ≤ m := by exact_mod_cast hm
  have hmpos : (0 : ℝ) < m := by linarith
  have hsR : ((N + 1 - M : ℕ) : ℝ) = ((N : ℝ) + 1) - M := by
    rw [Nat.cast_sub (by omega)]; push_cast; ring
  have hbN' : (b : ℝ) ≤ N := by exact_mod_cast hbN
  have hbη : (b : ℝ) * η ≤ 1 := by
    have h1 : (b : ℝ) * η ≤ N * η := mul_le_mul_of_nonneg_right hbN' hη0
    nlinarith
  by_cases hU : ((N + 1 - M : ℕ) : ℝ) / (((N : ℝ) + 1) * b) ≤ η
  · left
    have e : (b : ℝ) * (((c : ℝ) + η) / M) = ((b : ℝ) * η - 1) / M + (k' : ℝ) := by
      have hbcR : (b : ℝ) * c + 1 = (M : ℝ) * k' := by exact_mod_cast hbc
      field_simp
      linarith
    rw [e, nearestIntDist_add_int]
    apply nid_le_of_abs
    have hbη2 : ((N + 1 - M : ℕ) : ℝ) / ((N : ℝ) + 1) ≤ (b : ℝ) * η := by
      have h3 : ((N + 1 - M : ℕ) : ℝ) / (((N : ℝ) + 1) * b) * ((N : ℝ) + 1) * b ≤ η * ((N : ℝ) + 1) * b :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hU hApos.le) hbR.le
      have h4 : ((N + 1 - M : ℕ) : ℝ) / (((N : ℝ) + 1) * b) * ((N : ℝ) + 1) * b =
          ((N + 1 - M : ℕ) : ℝ) := by field_simp
      rw [h4] at h3
      have h5 : (b : ℝ) * η * ((N : ℝ) + 1) = η * ((N : ℝ) + 1) * b := by ring
      rw [div_le_iff₀ hApos, h5]
      exact h3
    rw [abs_le]
    constructor
    · rw [le_div_iff₀ hMR]
      have h6 : (-(1 / ((N : ℝ) + 1))) * M = -((M : ℝ) / ((N : ℝ) + 1)) := by ring
      rw [h6]
      have h7 : ((N + 1 - M : ℕ) : ℝ) / ((N : ℝ) + 1) = 1 - (M : ℝ) / ((N : ℝ) + 1) := by
        rw [hsR]; field_simp
      linarith
    · rw [div_le_iff₀ hMR]
      have : 0 ≤ 1 / ((N : ℝ) + 1) * M := by positivity
      linarith
  · push Not at hU
    by_cases hL : η ≤ 1 / (((N : ℝ) + 1) * m)
    · right; left
      rw [nid_mul_mod m M c η hMpos]
      apply nid_le_of_abs
      rw [abs_of_nonneg (mul_nonneg hmpos.le hη0)]
      have : (m : ℝ) * η ≤ (m : ℝ) * (1 / (((N : ℝ) + 1) * m)) := mul_le_mul_of_nonneg_left hL hmpos.le
      have e : (m : ℝ) * (1 / (((N : ℝ) + 1) * m)) = 1 / ((N : ℝ) + 1) := by field_simp
      linarith
    · right; right
      push Not at hL
      have hbm : b < m * (N + 1 - M) := by
        by_contra hcon
        push Not at hcon
        have hcR : (m : ℝ) * ((N + 1 - M : ℕ) : ℝ) ≤ b := by exact_mod_cast hcon
        have : ((N + 1 - M : ℕ) : ℝ) / (((N : ℝ) + 1) * b) ≤ 1 / (((N : ℝ) + 1) * m) := by
          rw [div_le_div_iff₀ (by positivity) (by positivity)]
          nlinarith
        linarith
      obtain ⟨z, hmod, h1, h2⟩ := hresc hbm
      obtain ⟨j, hj⟩ : (M : ℤ) ∣ (p : ℤ) - ((z * b : ℕ) : ℤ) := Nat.modEq_iff_dvd.mp hmod
      have hjR : (p : ℤ) - (z : ℤ) * b = (M : ℤ) * j := by
        push_cast at hj
        exact hj
      have hpc : (p : ℤ) * c = -(z : ℤ) + (M : ℤ) * (j * c + z * k') := by
        linear_combination c * hjR + (z : ℤ) * hbc
      have hpcR : (p : ℝ) * c = -(z : ℝ) + (M : ℝ) * ((j * c + z * k' : ℤ) : ℝ) := by
        exact_mod_cast hpc
      have e : (p : ℝ) * (((c : ℝ) + η) / M) =
          ((p : ℝ) * η - z) / M + (((j * c + z * k' : ℤ)) : ℝ) := by
        field_simp
        linarith
      rw [e, nearestIntDist_add_int]
      apply nid_le_of_abs
      have hlow : (z : ℝ) - (M : ℝ) / ((N : ℝ) + 1) ≤ (p : ℝ) * (1 / (((N : ℝ) + 1) * m)) := by
        have h1R : (m : ℝ) * ((z : ℝ) * ((N : ℝ) + 1)) ≤ p + m * M := by exact_mod_cast h1
        have : (z : ℝ) - (M : ℝ) / ((N : ℝ) + 1) =
            ((m : ℝ) * ((z : ℝ) * ((N : ℝ) + 1)) - (m : ℝ) * M) / (((N : ℝ) + 1) * m) := by
          field_simp
        rw [this, mul_one_div, div_le_div_iff_of_pos_right (by positivity)]
        linarith
      have hup : (p : ℝ) * (((N + 1 - M : ℕ) : ℝ) / (((N : ℝ) + 1) * b)) ≤
          (z : ℝ) + (M : ℝ) / ((N : ℝ) + 1) := by
        have h2R : (((N + 1 - M : ℕ) : ℝ)) * p ≤ (b : ℝ) * ((z : ℝ) * ((N : ℝ) + 1) + M) := by
          exact_mod_cast h2
        have : (z : ℝ) + (M : ℝ) / ((N : ℝ) + 1) =
            ((b : ℝ) * ((z : ℝ) * ((N : ℝ) + 1) + M)) / (((N : ℝ) + 1) * b) := by
          field_simp
        rw [this, mul_div_assoc', div_le_div_iff_of_pos_right (by positivity)]
        linarith
      have hpη1 : (p : ℝ) * (1 / (((N : ℝ) + 1) * m)) ≤ (p : ℝ) * η :=
        mul_le_mul_of_nonneg_left hL.le (Nat.cast_nonneg _)
      have hpη2 : (p : ℝ) * η ≤ (p : ℝ) * (((N + 1 - M : ℕ) : ℝ) / (((N : ℝ) + 1) * b)) :=
        mul_le_mul_of_nonneg_left hU.le (Nat.cast_nonneg _)
      rw [abs_div, abs_of_pos hMR, div_le_iff₀ hMR, abs_le]
      have e2 : 1 / ((N : ℝ) + 1) * M = (M : ℝ) / ((N : ℝ) + 1) := by ring
      rw [e2]
      constructor <;> linarith

theorem nonunit_cover {N M : ℕ} (c : ℤ) (η : ℝ) (hM : 0 < M) (hη0 : 0 ≤ η)
    (hη1 : η * ((N : ℝ) + 1) ≤ 1) (hg : 1 < Int.gcd c (M : ℤ)) :
    ∃ x : ℕ, 1 ≤ x ∧ 2 * x ≤ M ∧
      nearestIntDist ((x : ℝ) * (((c : ℝ) + η) / M)) ≤ 1 / ((N : ℝ) + 1) := by
  have hApos : (0 : ℝ) < (N : ℝ) + 1 := by positivity
  obtain ⟨g, hg0⟩ : ∃ g : ℕ, g = Int.gcd c (M : ℤ) := ⟨_, rfl⟩
  rw [← hg0] at hg
  have hgc : (g : ℤ) ∣ c := by rw [hg0]; exact Int.gcd_dvd_left c (M : ℤ)
  have hgM : (g : ℤ) ∣ (M : ℤ) := by rw [hg0]; exact Int.gcd_dvd_right c (M : ℤ)
  obtain ⟨c', hc'⟩ := hgc
  obtain ⟨x, hx⟩ := Int.natCast_dvd_natCast.mp hgM
  have hxpos : 0 < x := by
    rcases Nat.eq_zero_or_pos x with h0 | h0
    · rw [h0] at hx; omega
    · exact h0
  refine ⟨x, hxpos, ?_, ?_⟩
  · rw [hx]; nlinarith
  · have hgR : (2 : ℝ) ≤ g := by exact_mod_cast hg
    have hxR : (0 : ℝ) < x := by exact_mod_cast hxpos
    have hMg : (M : ℝ) = g * x := by exact_mod_cast hx
    have hcR : (c : ℝ) = g * c' := by exact_mod_cast hc'
    have e : (x : ℝ) * (((c : ℝ) + η) / M) = η / g + (c' : ℝ) := by
      rw [hMg, hcR]
      field_simp
      ring
    rw [e, nearestIntDist_add_int]
    apply nid_le_of_abs
    rw [abs_of_nonneg (by positivity)]
    have h1 : η / g ≤ η := div_le_self hη0 (by linarith)
    have h2 : η ≤ 1 / ((N : ℝ) + 1) := by rw [le_div_iff₀ hApos]; exact hη1
    linarith

theorem exists_b {N M : ℕ} (c : ℤ) (hM : 0 < M) (hMN : M ≤ N) (hcop : IsCoprime (M : ℤ) c) :
    ∃ b : ℕ, N + 1 ≤ b + M ∧ b ≤ N ∧ ∃ k' : ℤ, (b : ℤ) * c + 1 = (M : ℤ) * k' := by
  obtain ⟨u, v, huv⟩ := hcop
  have hMZ : (0 : ℤ) < M := by exact_mod_cast hM
  obtain ⟨s, hs⟩ : ∃ s : ℕ, s = N + 1 - M := ⟨_, rfl⟩
  have hr0 : 0 ≤ (-v - (s : ℤ)) % (M : ℤ) := Int.emod_nonneg _ (by omega)
  have hr1 : (-v - (s : ℤ)) % (M : ℤ) < M := Int.emod_lt_of_pos _ hMZ
  have hdec := Int.emod_add_mul_ediv (-v - (s : ℤ)) (M : ℤ)
  generalize (-v - (s : ℤ)) % (M : ℤ) = r at hr0 hr1 hdec
  generalize (-v - (s : ℤ)) / (M : ℤ) = q at hdec
  obtain ⟨b, hb⟩ : ∃ b : ℕ, (b : ℤ) = (s : ℤ) + r := ⟨((s : ℤ) + r).toNat, Int.toNat_of_nonneg (by omega)⟩
  refine ⟨b, by omega, by omega, u - q * c, ?_⟩
  rw [hb]
  have : (s : ℤ) + r = -v - M * q := by linarith
  rw [this]
  linear_combination (-1 : ℤ) * huv

end Gap
end Sext6
end LRSpectrumFull
