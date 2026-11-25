import LRSpectrumFull.Sext6.Gap.Q81BC

/-!
# Q8.1, Theorem T, direction "tight => every failing unit is rescued"  [2026-11-25]

Source: the accompanying notes on Zhang's Question 8.1 section 4 (Theorem T, the exact rescue window `(R_b)`).
Setting: `N = k + 1`, `A = N + 1`, `4 ≤ N`, `N < 2 r1`, `r1 < r2 ≤ N`, `V = v2Fam k r1 r2 m1 m2`.
"Tight" is the covering statement `ML V ≤ 1/A` (every time some speed is within `1/A` of an integer).
For the modulus `M = r_i` (own multiplier `m = m_i`, other inserted speed `p = w_j`), a *failing unit* is a `b`
coprime to `M` with `s ≤ b ≤ N`, `b < m s`, `s = A - M`.

* `ret_far`        : at `t = (c + η)/M`, `b c ≡ -1 (mod M)`, `0 < η`, `b η < s/A`: every speed `x ≤ N`, `x ≠ M`
  is at distance `> 1/A` from an integer (Lemma C of the notes: only the class `x ≡ b` comes close, and only from `η ≥ s/(A b)`).
* `window_band`    : an affine window `(L, U)` covered by one speed lies in a single band `|p η - z| ≤ M/A`.
* `rescue_core`    : the integer inequalities of `(R_b)`: `z b ≡ p (mod M)`, `m (z A - M) ≤ p`, `s p ≤ b (z A + M)`, `z ≥ 0`.
* `theoremT_only_if` : both entries.
Not formalised here: the converse (rescued => tight).  `gcd(r1, r2) > 1` is not needed for this direction.
No `sorry`, no `axiom`.

Convention: `N = k + 1` is the number of speeds of the vector `v : Fin (k+1) → ℤ`. Speeds are the moving runners; the runner at rest is not counted, so a vector of `N` speeds means `N + 1` runners and the Lonely Runner value is `1/(N+1)`.
Hypotheses: those of the individual statements (numerical bounds, structural conditions and, where named in the list above, window predicates such as `PrimeWin`, `CopWin`, `PrimeWindow7`, which later modules discharge for explicit ranges). The unproved predicates `DusartPi`, `LRCHyp`, `CopWinHyp` are not hypotheses of any statement in this module.
Axiom audit: covered by `Axioms22` (`#print axioms`; declarations not printed there are bricks of printed ones, so their axioms are bounded by the printed lines).
-/

namespace LRSpectrumFull
namespace Sext6
namespace Gap

theorem ret_far {N M x b : ℕ} (c k' : ℤ) (η : ℝ) (hMN : M ≤ N) (hN2 : N < 2 * M) (hM3 : 3 ≤ M)
    (hcop : IsCoprime (M : ℤ) c) (hbc : (b : ℤ) * c + 1 = (M : ℤ) * k')
    (hb1 : N + 1 ≤ b + M) (hbN : b ≤ N) (hx1 : 1 ≤ x) (hxN : x ≤ N) (hxM : x ≠ M)
    (hη0 : 0 < η) (hηA : η * ((N : ℝ) + 1) < 1)
    (hηb : (b : ℝ) * η < 1 - (M : ℝ) / ((N : ℝ) + 1)) :
    1 / ((N : ℝ) + 1) < nearestIntDist ((x : ℝ) * (((c : ℝ) + η) / M)) := by
  have hMpos : (0 : ℝ) < M := by exact_mod_cast (by omega : 0 < M)
  have hApos : (0 : ℝ) < (N : ℝ) + 1 := by positivity
  have hMA : (M : ℝ) < (N : ℝ) + 1 := by
    have : (M : ℝ) ≤ N := by exact_mod_cast hMN
    linarith
  have hMA1 : (M : ℝ) * (1 / ((N : ℝ) + 1)) < 1 := by
    rw [mul_one_div, div_lt_one hApos]
    exact hMA
  have hM3R : (3 : ℝ) ≤ M := by exact_mod_cast hM3
  have hxη : (x : ℝ) * η < 1 := by
    have hx : (x : ℝ) ≤ N := by exact_mod_cast hxN
    have : (x : ℝ) * η ≤ N * η := mul_le_mul_of_nonneg_right hx hη0.le
    nlinarith
  have hxη0 : 0 ≤ (x : ℝ) * η := mul_nonneg (Nat.cast_nonneg _) hη0.le
  have hMZ : (0 : ℤ) < M := by exact_mod_cast (by omega : 0 < M)
  have hdec := Int.emod_add_mul_ediv ((x : ℤ) * c) (M : ℤ)
  have hy0 : 0 ≤ (x : ℤ) * c % (M : ℤ) := Int.emod_nonneg _ (by omega)
  have hy1 : (x : ℤ) * c % (M : ℤ) < M := Int.emod_lt_of_pos _ hMZ
  generalize (x : ℤ) * c % (M : ℤ) = y at hdec hy0 hy1
  generalize (x : ℤ) * c / (M : ℤ) = q at hdec
  have hdecR : (y : ℝ) + (M : ℝ) * (q : ℝ) = (x : ℝ) * (c : ℝ) := by exact_mod_cast hdec
  have e : (x : ℝ) * (((c : ℝ) + η) / M) = ((y : ℝ) + (x : ℝ) * η) / M + (q : ℝ) := by
    field_simp
    linarith
  have hy_ne0 : y ≠ 0 := by
    intro hy
    have hd : (M : ℤ) ∣ (x : ℤ) * c := ⟨q, by rw [hy] at hdec; linarith⟩
    have h3 : (M : ℤ) ∣ (x : ℤ) := hcop.dvd_of_dvd_mul_right hd
    exact not_dvd_retained hN2 hx1 hxN hxM (Int.natCast_dvd_natCast.mp h3)
  have hθ0 : (0 : ℝ) ≤ 1 / ((N : ℝ) + 1) := by positivity
  rw [e, nearestIntDist_add_int]
  by_cases hyM : y = (M : ℤ) - 1
  · have hd : (M : ℤ) ∣ (x : ℤ) * c + 1 := ⟨q + 1, by rw [hyM] at hdec; linarith⟩
    have h4 : (M : ℤ) ∣ ((x : ℤ) - b) * c := by
      have e2 : ((x : ℤ) - b) * c = ((x : ℤ) * c + 1) - ((b : ℤ) * c + 1) := by ring
      rw [e2]
      exact dvd_sub hd ⟨k', hbc⟩
    have h5 : (M : ℤ) ∣ (x : ℤ) - b := hcop.dvd_of_dvd_mul_right h4
    obtain ⟨j, hj⟩ := h5
    have hxb : x ≤ b := by
      by_contra hcon
      push Not at hcon
      have hj1 : 1 ≤ j := by
        by_contra hj0
        have hj0' : j ≤ 0 := by omega
        have : (M : ℤ) * j ≤ 0 := by nlinarith
        omega
      have : (M : ℤ) ≤ M * j := by nlinarith
      omega
    have hxbR : (x : ℝ) ≤ b := by exact_mod_cast hxb
    have hxη' : (x : ℝ) * η ≤ b * η := mul_le_mul_of_nonneg_right hxbR hη0.le
    rw [hyM]
    have hcast : (((M : ℤ) - 1 : ℤ) : ℝ) = (M : ℝ) - 1 := by push_cast; ring
    rw [hcast]
    apply nid_gt_of_mem hθ0
    · rw [lt_div_iff₀ hMpos]
      linarith
    · rw [div_lt_iff₀ hMpos]
      have h6 : (1 - 1 / ((N : ℝ) + 1)) * M = M - (M : ℝ) / ((N : ℝ) + 1) := by
        field_simp
      rw [h6]
      linarith
  · have hy1' : 1 ≤ y := by omega
    have hy2' : y ≤ (M : ℤ) - 2 := by omega
    have hYR1 : (1 : ℝ) ≤ (y : ℝ) := by exact_mod_cast hy1'
    have hYR2 : (y : ℝ) ≤ (M : ℝ) - 2 := by
      have h : (y : ℝ) ≤ (((M : ℤ) - 2 : ℤ) : ℝ) := by exact_mod_cast hy2'
      simpa using h
    apply nid_gt_of_mem hθ0
    · rw [lt_div_iff₀ hMpos]
      linarith
    · rw [div_lt_iff₀ hMpos]
      have h6 : (1 - 1 / ((N : ℝ) + 1)) * M = M - (M : ℝ) / ((N : ℝ) + 1) := by
        field_simp
      have h7 : (M : ℝ) / ((N : ℝ) + 1) ≤ 1 := by
        rw [div_le_one hApos]; exact hMA.le
      rw [h6]
      linarith

theorem window_band {A : ℝ} {M p : ℕ} {c : ℤ} (L U : ℝ) (hA : 4 ≤ A) (hM : 0 < M)
    (hMA : (M : ℝ) < A) (hpR : 0 < p) (hL0 : 0 < L) (hLU : L < U)
    (hcov : ∀ η : ℝ, L < η → η < U →
      nearestIntDist ((p : ℝ) * (((c : ℝ) + η) / M)) ≤ 1 / A) :
    ∃ z : ℤ, (M : ℤ) ∣ z + (p : ℤ) * c ∧ 0 ≤ z ∧ (z : ℝ) - (M : ℝ) / A ≤ (p : ℝ) * L ∧
      (p : ℝ) * U ≤ (z : ℝ) + (M : ℝ) / A := by
  have hApos : 0 < A := by linarith
  have hθ : 1 / A ≤ 1 / 4 := by
    rw [div_le_div_iff₀ hApos (by norm_num)]
    linarith
  have hMR : (0 : ℝ) < M := by exact_mod_cast hM
  have hpRR : (0 : ℝ) < p := by exact_mod_cast hpR
  have hσ : 0 < (p : ℝ) / M := div_pos hpRR hMR
  have hwin : ∀ η, L < η → η < U →
      nearestIntDist (((p : ℝ) / M) * η + ((p : ℝ) * c / M)) ≤ 1 / A := by
    intro η h1 h2
    have h := hcov η h1 h2
    have e : (p : ℝ) * (((c : ℝ) + η) / M) = ((p : ℝ) / M) * η + ((p : ℝ) * c / M) := by
      field_simp
      try ring
    rwa [e] at h
  obtain ⟨n, hn⟩ := uniform_band hσ hθ hLU hwin
  have hz : (((n * M - p * c : ℤ)) : ℝ) = (n : ℝ) * M - (p : ℝ) * c := by push_cast; ring
  have hlow : (((n * M - p * c : ℤ)) : ℝ) - (M : ℝ) / A ≤ (p : ℝ) * L := by
    have h := hn L le_rfl hLU.le
    obtain ⟨h1, _⟩ := abs_le.mp h
    rw [hz]
    have h2 : (M : ℝ) * (-(1 / A)) ≤ (M : ℝ) * (((p : ℝ) / M) * L + ((p : ℝ) * c / M) - n) :=
      mul_le_mul_of_nonneg_left h1 hMR.le
    have h3 : (M : ℝ) * (((p : ℝ) / M) * L + ((p : ℝ) * c / M) - n) =
        (p : ℝ) * L + (p : ℝ) * c - n * M := by
      field_simp
    have h4 : (M : ℝ) * (-(1 / A)) = -((M : ℝ) / A) := by ring
    rw [h3, h4] at h2
    linarith
  have hup : (p : ℝ) * U ≤ (((n * M - p * c : ℤ)) : ℝ) + (M : ℝ) / A := by
    have h := hn U hLU.le le_rfl
    obtain ⟨_, h1⟩ := abs_le.mp h
    rw [hz]
    have h2 : (M : ℝ) * (((p : ℝ) / M) * U + ((p : ℝ) * c / M) - n) ≤ (M : ℝ) * (1 / A) :=
      mul_le_mul_of_nonneg_left h1 hMR.le
    have h3 : (M : ℝ) * (((p : ℝ) / M) * U + ((p : ℝ) * c / M) - n) =
        (p : ℝ) * U + (p : ℝ) * c - n * M := by
      field_simp
    have h4 : (M : ℝ) * (1 / A) = (M : ℝ) / A := by ring
    rw [h3, h4] at h2
    linarith
  have hMA1 : (M : ℝ) / A < 1 := by
    rw [div_lt_one hApos]; exact hMA
  have hpU : 0 < (p : ℝ) * U := mul_pos hpRR (lt_trans hL0 hLU)
  have hzneg : (-1 : ℝ) < (((n * M - p * c : ℤ)) : ℝ) := by linarith
  have hz0 : (0 : ℤ) ≤ n * M - p * c := by
    have : (-1 : ℤ) < n * M - p * c := by exact_mod_cast hzneg
    omega
  exact ⟨n * M - p * c, ⟨n, by ring⟩, hz0, hlow, hup⟩

theorem rescue_core {N M m p b : ℕ} (c k' : ℤ) (hMN : M ≤ N) (hN2 : N < 2 * M) (hM3 : 3 ≤ M)
    (hm : 2 ≤ m) (hmN : m + 1 ≤ N) (hp : 0 < p) (hN4 : 4 ≤ N)
    (hcop : IsCoprime (M : ℤ) c) (hbc : (b : ℤ) * c + 1 = (M : ℤ) * k')
    (hb1 : N + 1 ≤ b + M) (hbN : b ≤ N) (hbm : b < m * (N + 1 - M))
    (hcov : ∀ η : ℝ, 1 / (((N : ℝ) + 1) * m) < η → η < ((N + 1 - M : ℕ) : ℝ) / (((N : ℝ) + 1) * b) →
      (∃ x : ℕ, 1 ≤ x ∧ x ≤ N ∧ x ≠ M ∧
        nearestIntDist ((x : ℝ) * (((c : ℝ) + η) / M)) ≤ 1 / ((N : ℝ) + 1)) ∨
      nearestIntDist (((m * M : ℕ) : ℝ) * (((c : ℝ) + η) / M)) ≤ 1 / ((N : ℝ) + 1) ∨
      nearestIntDist ((p : ℝ) * (((c : ℝ) + η) / M)) ≤ 1 / ((N : ℝ) + 1)) :
    ∃ z : ℕ, z * b ≡ p [MOD M] ∧ m * (z * (N + 1)) ≤ p + m * M ∧
      (N + 1 - M) * p ≤ b * (z * (N + 1) + M) := by
  have hApos : (0 : ℝ) < (N : ℝ) + 1 := by positivity
  have hA4 : (4 : ℝ) ≤ (N : ℝ) + 1 := by
    have : (4 : ℝ) ≤ N := by exact_mod_cast hN4
    linarith
  have hMpos : 0 < M := by omega
  have hMR : (0 : ℝ) < M := by exact_mod_cast hMpos
  have hMA : (M : ℝ) < (N : ℝ) + 1 := by
    have : (M : ℝ) ≤ N := by exact_mod_cast hMN
    linarith
  have hbpos : 0 < b := by omega
  have hbR : (0 : ℝ) < b := by exact_mod_cast hbpos
  have hmR : (2 : ℝ) ≤ m := by exact_mod_cast hm
  have hmpos : (0 : ℝ) < m := by linarith
  have hmNR : (m : ℝ) + 1 ≤ N := by exact_mod_cast hmN
  have hsR : ((N + 1 - M : ℕ) : ℝ) = ((N : ℝ) + 1) - M := by
    rw [Nat.cast_sub (by omega)]; push_cast; ring
  have hsb : ((N + 1 - M : ℕ) : ℝ) ≤ b := by
    have : N + 1 - M ≤ b := by omega
    exact_mod_cast this
  have hbmR : (b : ℝ) < m * ((N + 1 - M : ℕ) : ℝ) := by exact_mod_cast hbm
  have hspos : (0 : ℝ) < ((N + 1 - M : ℕ) : ℝ) := by
    rw [hsR]; linarith
  obtain ⟨L, hL⟩ : ∃ L : ℝ, L = 1 / (((N : ℝ) + 1) * m) := ⟨_, rfl⟩
  obtain ⟨U, hU⟩ : ∃ U : ℝ, U = ((N + 1 - M : ℕ) : ℝ) / (((N : ℝ) + 1) * b) := ⟨_, rfl⟩
  have hL0 : 0 < L := by rw [hL]; positivity
  have hLU : L < U := by
    rw [hL, hU, div_lt_div_iff₀ (by positivity) (by positivity)]
    nlinarith
  have hUle : U * ((N : ℝ) + 1) ≤ 1 := by
    rw [hU]
    have : ((N + 1 - M : ℕ) : ℝ) / (((N : ℝ) + 1) * b) * ((N : ℝ) + 1) =
        ((N + 1 - M : ℕ) : ℝ) / b := by field_simp
    rw [this, div_le_one hbR]
    exact hsb
  have hcov' : ∀ η : ℝ, L < η → η < U →
      nearestIntDist ((p : ℝ) * (((c : ℝ) + η) / M)) ≤ 1 / ((N : ℝ) + 1) := by
    intro η h1 h2
    have hη0 : 0 < η := lt_trans hL0 h1
    have hηA : η * ((N : ℝ) + 1) < 1 := by
      have : η * ((N : ℝ) + 1) < U * ((N : ℝ) + 1) := mul_lt_mul_of_pos_right h2 hApos
      linarith
    have hηb : (b : ℝ) * η < 1 - (M : ℝ) / ((N : ℝ) + 1) := by
      have h3 : η < ((N + 1 - M : ℕ) : ℝ) / (((N : ℝ) + 1) * b) := by rw [← hU]; exact h2
      rw [lt_div_iff₀ (by positivity)] at h3
      have h4 : (1 : ℝ) - (M : ℝ) / ((N : ℝ) + 1) = ((N + 1 - M : ℕ) : ℝ) / ((N : ℝ) + 1) := by
        rw [hsR]; field_simp
      rw [h4, lt_div_iff₀ hApos]
      nlinarith
    rcases hcov η (by rw [hL] at h1; exact h1) (by rw [hU] at h2; exact h2) with ⟨x, hx1, hxN, hxM, hx⟩ | h | h
    · exfalso
      have := ret_far c k' η hMN hN2 hM3 hcop hbc hb1 hbN hx1 hxN hxM hη0 hηA hηb
      linarith
    · exfalso
      rw [nid_mul_mod m M c η hMpos] at h
      have hmη : 1 / ((N : ℝ) + 1) < (m : ℝ) * η := by
        have h5 : (m : ℝ) * L = 1 / ((N : ℝ) + 1) := by
          rw [hL]; field_simp
        rw [← h5]
        exact mul_lt_mul_of_pos_left h1 hmpos
      have hmη2 : (m : ℝ) * η < 1 - 1 / ((N : ℝ) + 1) := by
        have h6 : (m : ℝ) * η ≤ (m : ℝ) * (1 / ((N : ℝ) + 1)) :=
          mul_le_mul_of_nonneg_left (by
            have : η ≤ 1 / ((N : ℝ) + 1) := by
              rw [le_div_iff₀ hApos]; exact hηA.le
            exact this) hmpos.le
        have h7 : (1 : ℝ) - 1 / ((N : ℝ) + 1) = (N : ℝ) / ((N : ℝ) + 1) := by
          field_simp; ring
        rw [h7]
        have h8 : (m : ℝ) * (1 / ((N : ℝ) + 1)) = (m : ℝ) / ((N : ℝ) + 1) := by ring
        rw [h8] at h6
        have h9 : (m : ℝ) / ((N : ℝ) + 1) < (N : ℝ) / ((N : ℝ) + 1) :=
          div_lt_div_of_pos_right (by linarith) hApos
        linarith
      have hn := nid_gt_of_mem (by positivity) hmη hmη2
      linarith
    · exact h
  obtain ⟨z, hdvd, hz0, hz1, hz2⟩ := window_band (A := (N : ℝ) + 1) (M := M) (p := p) (c := c) L U
    hA4 hMpos hMA hp hL0 hLU hcov'
  obtain ⟨zn, hzn⟩ : ∃ zn : ℕ, (zn : ℤ) = z := ⟨z.toNat, Int.toNat_of_nonneg hz0⟩
  have hznR : (zn : ℝ) = (z : ℝ) := by rw [← hzn]; push_cast; ring
  rw [← hznR] at hz1 hz2
  refine ⟨zn, ?_, ?_, ?_⟩
  · rw [Nat.modEq_iff_dvd]
    obtain ⟨n', hn'⟩ := hdvd
    refine ⟨k' * p - n' * b, ?_⟩
    have e1 : ((p : ℕ) : ℤ) - ((zn * b : ℕ) : ℤ) = (p : ℤ) - (z * b) := by
      push_cast; rw [hzn]
    rw [e1]
    have e2 : (z : ℤ) = M * n' - p * c := by linarith
    rw [e2]
    have : (p : ℤ) - ((M : ℤ) * n' - p * c) * b = (M : ℤ) * (k' * p - n' * b) := by
      have := hbc
      linear_combination (p : ℤ) * hbc
    exact this
  · rw [hL] at hz1
    have h1 : ((zn : ℝ) - (M : ℝ) / ((N : ℝ) + 1)) * (((N : ℝ) + 1) * m) ≤
        (p : ℝ) * (1 / (((N : ℝ) + 1) * m)) * (((N : ℝ) + 1) * m) := by
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      exact hz1
    have h2 : (p : ℝ) * (1 / (((N : ℝ) + 1) * m)) * (((N : ℝ) + 1) * m) = p := by
      field_simp
    have h3 : ((zn : ℝ) - (M : ℝ) / ((N : ℝ) + 1)) * (((N : ℝ) + 1) * m) =
        (m : ℝ) * ((zn : ℝ) * ((N : ℝ) + 1)) - (m : ℝ) * M := by
      field_simp
    rw [h2, h3] at h1
    have h4 : (m : ℝ) * ((zn : ℝ) * ((N : ℝ) + 1)) ≤ p + m * M := by linarith
    exact_mod_cast h4
  · have h1 : (p : ℝ) * U * (((N : ℝ) + 1) * b) ≤
        ((zn : ℝ) + (M : ℝ) / ((N : ℝ) + 1)) * (((N : ℝ) + 1) * b) :=
      mul_le_mul_of_nonneg_right hz2 (by positivity)
    have h2 : (p : ℝ) * U * (((N : ℝ) + 1) * b) = (p : ℝ) * ((N + 1 - M : ℕ) : ℝ) := by
      rw [hU]; field_simp
    have h3 : ((zn : ℝ) + (M : ℝ) / ((N : ℝ) + 1)) * (((N : ℝ) + 1) * b) =
        (b : ℝ) * ((zn : ℝ) * ((N : ℝ) + 1) + M) := by
      field_simp
    rw [h2, h3] at h1
    have h4 : (((N + 1 - M : ℕ) : ℝ)) * p ≤ (b : ℝ) * ((zn : ℝ) * ((N : ℝ) + 1) + M) := by linarith
    exact_mod_cast h4

end Gap
end Sext6
end LRSpectrumFull
