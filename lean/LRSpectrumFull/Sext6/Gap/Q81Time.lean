import LRSpectrumFull.Sext6.Gap.MultiInst
import LRSpectrumFull.Sext6.Gap.OneOverR

/-!
# Q8.1, Theorem C: explicit times for `([1,N] \ {r1, r2}) ∪ {m1 r1, m2 r2}`, `gcd(r1, r2) = 1`  [2026-11-25]

Source: the accompanying notes on Zhang's Question 8.1 section 3, Lemmas 1 and 2 (the notes (part 2) section 3).
`N = k + 1` speeds, `N/2 < r1 < r2 ≤ N`, `m1, m2 ≥ 2`; the vector is `v2Fam k r1 r2 m1 m2` (MultiInst).

* `nid_residue_ge`   : generic residue estimate `1/N ≤ ‖v (c + η)/M‖` when `M ∤ v c` and `M ∤ v c + 1`
  (Lemma 1(a): the class `v c ≡ 0, -1 (mod M)` is the only one that can come close to an integer).
* `nid_mul_mod`, `nid_mul_blocker`, `inserted_pair` : the two inserted speeds at time `(c + η)/M`
  (Lemma 1(b), (c)): `‖a M t‖ = ‖a η‖`, `‖b x t‖ = ‖b/M - (b x/M) η‖` when `x c + 1 = M k'`.
* `retained_big`, `retained_small` : retained speeds at the time in modulus `r2` (blocker `r1`), resp. modulus `r1`
  (blockers `r2 - r1`, `r2`).
* `caseI_ML`  (m1 + 1 ≤ r2) and `caseI'_ML` (m2 + 1 ≤ r1) : `1/N ≤ ML`  (Lemma 2, Cases I and I').
Case II (both multipliers large) is in `Q81Core`.
No `sorry`, no `axiom`.

Convention: `N = k + 1` is the number of speeds of the vector `v : Fin (k+1) → ℤ`. Speeds are the moving runners; the runner at rest is not counted, so a vector of `N` speeds means `N + 1` runners and the Lonely Runner value is `1/(N+1)`.
Hypotheses: those of the individual statements (numerical bounds, structural conditions and, where named in the list above, window predicates such as `PrimeWin`, `CopWin`, `PrimeWindow7`, which later modules discharge for explicit ranges). The unproved predicates `DusartPi`, `LRCHyp`, `CopWinHyp` are not hypotheses of any statement in this module.
Axiom audit: covered by `Axioms8` (`#print axioms`; declarations not printed there are bricks of printed ones, so their axioms are bounded by the printed lines).
-/

namespace LRSpectrumFull
namespace Sext6
namespace Gap

theorem v2Fam_at1 {k r1 r2 m1 m2 : ℕ} (i : Fin (k + 1)) (hi : (i : ℕ) + 1 = r1) :
    v2Fam k r1 r2 m1 m2 i = ((m1 * r1 : ℕ) : ℤ) := by
  simp [v2Fam, hi]

theorem v2Fam_at2 {k r1 r2 m1 m2 : ℕ} (i : Fin (k + 1)) (hi1 : ¬ ((i : ℕ) + 1 = r1))
    (hi : (i : ℕ) + 1 = r2) : v2Fam k r1 r2 m1 m2 i = ((m2 * r2 : ℕ) : ℤ) := by
  simp only [v2Fam]
  rw [if_neg hi1, if_pos hi]

theorem v2Fam_at0 {k r1 r2 m1 m2 : ℕ} (i : Fin (k + 1)) (hi1 : ¬ ((i : ℕ) + 1 = r1))
    (hi2 : ¬ ((i : ℕ) + 1 = r2)) : v2Fam k r1 r2 m1 m2 i = (((i : ℕ) + 1 : ℕ) : ℤ) := by
  simp [v2Fam, hi1, hi2]

/-- A time at which every entry of `v2Fam` is at distance at least `c`. -/
theorem ML_v2Fam_ge {k N r1 r2 m1 m2 : ℕ} (hk : k + 1 = N) (c t : ℝ)
    (hret : ∀ x : ℕ, 1 ≤ x → x ≤ N → x ≠ r1 → x ≠ r2 → c ≤ nearestIntDist ((x : ℝ) * t))
    (h1 : c ≤ nearestIntDist (((m1 * r1 : ℕ) : ℝ) * t))
    (h2 : c ≤ nearestIntDist (((m2 * r2 : ℕ) : ℝ) * t)) :
    c ≤ ML (v2Fam k r1 r2 m1 m2) := by
  refine ML_ge_of_far _ c t ?_
  intro i
  by_cases hi1 : (i : ℕ) + 1 = r1
  · rw [v2Fam_at1 i hi1]
    simpa using h1
  · by_cases hi2 : (i : ℕ) + 1 = r2
    · rw [v2Fam_at2 i hi1 hi2]
      simpa using h2
    · rw [v2Fam_at0 i hi1 hi2]
      have hiN : (i : ℕ) < k + 1 := i.isLt
      have := hret ((i : ℕ) + 1) (by omega) (by omega) hi1 hi2
      simpa using this

/-- `z ∈ [1/N, 1 - 1/N]` gives `1/N ≤ ‖z‖`. -/
theorem nid_ge_inv {N : ℕ} {z : ℝ} (hN : 2 ≤ N) (h1 : 1 / (N : ℝ) ≤ z)
    (h2 : z ≤ 1 - 1 / (N : ℝ)) : 1 / (N : ℝ) ≤ nearestIntDist z := by
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hN1 : 0 < 1 / (N : ℝ) := by positivity
  exact nearestIntDist_ge (by linarith) (by linarith) h1 (by linarith)

/-- **Lemma 1(a).**  At `t = (c + η)/M`, a speed `v ≤ N` with `M ∤ v c` and `M ∤ v c + 1` is at distance
at least `1/N` from an integer, as soon as `N η ≤ 2 - M/N`. -/
theorem nid_residue_ge {N M v : ℕ} (c : ℤ) (η : ℝ) (hM : 0 < M) (hMN : M ≤ N) (hv : v ≤ N)
    (hη0 : 0 ≤ η) (hηN : (N : ℝ) * η ≤ 2 - (M : ℝ) / N)
    (h0 : ¬ ((M : ℤ) ∣ (v : ℤ) * c)) (h1 : ¬ ((M : ℤ) ∣ (v : ℤ) * c + 1)) :
    1 / (N : ℝ) ≤ nearestIntDist ((v : ℝ) * (((c : ℝ) + η) / M)) := by
  have hMpos : (0 : ℝ) < M := by exact_mod_cast hM
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (lt_of_lt_of_le hM hMN)
  have hM0 : (M : ℝ) ≠ 0 := hMpos.ne'
  have hMZ : (0 : ℤ) < M := by exact_mod_cast hM
  have hdec := Int.emod_add_mul_ediv ((v : ℤ) * c) (M : ℤ)
  have hy0 : 0 ≤ (v : ℤ) * c % (M : ℤ) := Int.emod_nonneg _ (by omega)
  have hy1 : (v : ℤ) * c % (M : ℤ) < M := Int.emod_lt_of_pos _ hMZ
  generalize (v : ℤ) * c % (M : ℤ) = y at hdec hy0 hy1
  generalize (v : ℤ) * c / (M : ℤ) = q at hdec
  have hy_ne0 : y ≠ 0 := by
    intro hy
    apply h0
    exact ⟨q, by rw [hy] at hdec; linarith⟩
  have hy_ne1 : y ≠ (M : ℤ) - 1 := by
    intro hy
    apply h1
    exact ⟨q + 1, by rw [hy] at hdec; linarith⟩
  have hy1' : 1 ≤ y := by omega
  have hy2' : y ≤ (M : ℤ) - 2 := by omega
  have hM3 : 3 ≤ M := by omega
  have hYR1 : (1 : ℝ) ≤ (y : ℝ) := by exact_mod_cast hy1'
  have hYR2 : (y : ℝ) ≤ (M : ℝ) - 2 := by
    have h : (y : ℝ) ≤ (((M : ℤ) - 2 : ℤ) : ℝ) := by exact_mod_cast hy2'
    simpa using h
  have hdecR : (y : ℝ) + (M : ℝ) * (q : ℝ) = (v : ℝ) * (c : ℝ) := by exact_mod_cast hdec
  have e : (v : ℝ) * (((c : ℝ) + η) / M) = ((y : ℝ) + (v : ℝ) * η) / M + (q : ℝ) := by
    field_simp
    linarith
  have hvη : (v : ℝ) * η ≤ (N : ℝ) * η :=
    mul_le_mul_of_nonneg_right (by exact_mod_cast hv) hη0
  have hvη0 : 0 ≤ (v : ℝ) * η := mul_nonneg (Nat.cast_nonneg _) hη0
  have hMN' : (M : ℝ) ≤ N := by exact_mod_cast hMN
  have hMdN : (M : ℝ) / N ≤ 1 := by
    rw [div_le_iff₀ hNpos]
    linarith
  have hz_lo : 1 / (N : ℝ) ≤ ((y : ℝ) + (v : ℝ) * η) / M := by
    rw [le_div_iff₀ hMpos]
    have h5 : 1 / (N : ℝ) * M = (M : ℝ) / N := by ring
    rw [h5]
    linarith
  have hz_hi : ((y : ℝ) + (v : ℝ) * η) / M ≤ 1 - 1 / (N : ℝ) := by
    rw [div_le_iff₀ hMpos]
    have h5 : (1 - 1 / (N : ℝ)) * M = M - (M : ℝ) / N := by ring
    rw [h5]
    linarith
  rw [e, nearestIntDist_add_int]
  exact nid_ge_inv (by omega) hz_lo hz_hi

/-- **Lemma 1(b).**  A multiple `a M` of the modulus: `‖a M t‖ = ‖a η‖`. -/
theorem nid_mul_mod (a M : ℕ) (c : ℤ) (η : ℝ) (hM : 0 < M) :
    nearestIntDist (((a * M : ℕ) : ℝ) * (((c : ℝ) + η) / M)) = nearestIntDist ((a : ℝ) * η) := by
  have hM0 : (M : ℝ) ≠ 0 := by exact_mod_cast hM.ne'
  have e : ((a * M : ℕ) : ℝ) * (((c : ℝ) + η) / M) = (a : ℝ) * η + (((a : ℤ) * c : ℤ) : ℝ) := by
    push_cast
    field_simp
    try ring
  rw [e, nearestIntDist_add_int]

/-- **Lemma 1(c).**  A multiple `b x` of a blocker `x` (`x c + 1 = M k'`):
`‖b x t‖ = ‖b/M - (b x/M) η‖`. -/
theorem nid_mul_blocker (b x M : ℕ) (c k' : ℤ) (η : ℝ) (hM : 0 < M)
    (hx : (x : ℤ) * c + 1 = (M : ℤ) * k') :
    nearestIntDist (((b * x : ℕ) : ℝ) * (((c : ℝ) + η) / M)) =
      nearestIntDist ((b : ℝ) / M - ((b : ℝ) * x / M) * η) := by
  have hM0 : (M : ℝ) ≠ 0 := by exact_mod_cast hM.ne'
  have hxR : (x : ℝ) * c + 1 = (M : ℝ) * k' := by exact_mod_cast hx
  have hb : (b : ℝ) * ((x : ℝ) * c + 1) = (b : ℝ) * ((M : ℝ) * k') := by rw [hxR]
  have e : ((b * x : ℕ) : ℝ) * (((c : ℝ) + η) / M) =
      -((b : ℝ) / M - ((b : ℝ) * x / M) * η) + (((b : ℤ) * k' : ℤ) : ℝ) := by
    push_cast
    field_simp
    linarith
  rw [e, nearestIntDist_add_int, nearestIntDist_neg]

/-- A retained blocker `u` (`u c + 1 = M k'`) is at distance at least `1/N` if `u η ≤ 1 - M/N`. -/
theorem nid_unit_blocker_ge {N M u : ℕ} (c k' : ℤ) (η : ℝ) (hN : 2 ≤ N) (hM2 : 2 ≤ M)
    (hMN : M ≤ N) (hη0 : 0 ≤ η) (hx : (u : ℤ) * c + 1 = (M : ℤ) * k')
    (hu : (u : ℝ) * η ≤ 1 - (M : ℝ) / N) :
    1 / (N : ℝ) ≤ nearestIntDist ((u : ℝ) * (((c : ℝ) + η) / M)) := by
  have hMpos : (0 : ℝ) < M := by exact_mod_cast (by omega : 0 < M)
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have h := nid_mul_blocker 1 u M c k' η (by omega) hx
  simp only [Nat.one_mul, Nat.cast_one, one_mul] at h
  rw [h]
  have hw : (1 : ℝ) / M - ((u : ℝ) / M) * η = (1 / (M : ℝ)) * (1 - (u : ℝ) * η) := by ring
  rw [hw]
  have hu0 : 0 < 1 / (M : ℝ) := by positivity
  have huη0 : 0 ≤ (u : ℝ) * η := mul_nonneg (Nat.cast_nonneg _) hη0
  have hM2R : (2 : ℝ) ≤ M := by exact_mod_cast hM2
  have hN2R : (2 : ℝ) ≤ N := by exact_mod_cast hN
  apply nid_ge_inv hN
  · have h3 : (1 / (M : ℝ)) * ((M : ℝ) / N) ≤ (1 / (M : ℝ)) * (1 - (u : ℝ) * η) :=
      mul_le_mul_of_nonneg_left (by linarith) hu0.le
    have h4 : (1 / (M : ℝ)) * ((M : ℝ) / N) = 1 / (N : ℝ) := by
      field_simp
      try ring
    linarith
  · have h3 : (1 / (M : ℝ)) * (1 - (u : ℝ) * η) ≤ (1 / (M : ℝ)) * 1 :=
      mul_le_mul_of_nonneg_left (by linarith) hu0.le
    have h4 : 1 / (M : ℝ) ≤ 1 / 2 := one_div_le_one_div_of_le (by norm_num) hM2R
    have h5 : 1 / (N : ℝ) ≤ 1 / 2 := one_div_le_one_div_of_le (by norm_num) hN2R
    linarith

/-- The two inserted speeds at the time `t = (c + η)/M`, `η = 1/(N a)`:
`a M` (multiple of the modulus) and `b x` (multiple of the blocker `x`), `b + 1 ≤ M`. -/
theorem inserted_pair {N M x a b : ℕ} (c k' : ℤ) (η : ℝ) (hη : η = 1 / ((N : ℝ) * a))
    (hN : 2 ≤ N) (hM2 : 2 ≤ M) (hMN : M ≤ N) (hxN : x ≤ N) (ha : 2 ≤ a) (hb : 2 ≤ b)
    (hbM : b + 1 ≤ M) (hx : (x : ℤ) * c + 1 = (M : ℤ) * k') :
    1 / (N : ℝ) ≤ nearestIntDist (((a * M : ℕ) : ℝ) * (((c : ℝ) + η) / M)) ∧
    1 / (N : ℝ) ≤ nearestIntDist (((b * x : ℕ) : ℝ) * (((c : ℝ) + η) / M)) := by
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hMpos : (0 : ℝ) < M := by exact_mod_cast (by omega : 0 < M)
  have haR : (2 : ℝ) ≤ a := by exact_mod_cast ha
  have hbR : (2 : ℝ) ≤ b := by exact_mod_cast hb
  have hapos : (0 : ℝ) < a := by linarith
  have hN0 : (N : ℝ) ≠ 0 := hNpos.ne'
  have ha0 : (a : ℝ) ≠ 0 := hapos.ne'
  have hη0 : 0 < η := by rw [hη]; positivity
  have hNη : (N : ℝ) * η = 1 / a := by
    rw [hη]
    field_simp
    try ring
  have hN2R : (2 : ℝ) ≤ N := by exact_mod_cast hN
  constructor
  · rw [nid_mul_mod a M c η (by omega)]
    have h1 : (a : ℝ) * η = 1 / N := by
      rw [hη]
      field_simp
      try ring
    rw [h1]
    have h5 : 1 / (N : ℝ) ≤ 1 / 2 := one_div_le_one_div_of_le (by norm_num) hN2R
    exact nid_ge_inv hN le_rfl (by linarith)
  · rw [nid_mul_blocker b x M c k' η (by omega) hx]
    have hxR : (x : ℝ) ≤ N := by exact_mod_cast hxN
    have hxη0 : 0 ≤ (x : ℝ) * η := mul_nonneg (Nat.cast_nonneg _) hη0.le
    have h1a : (1 : ℝ) / a ≤ 1 / 2 := one_div_le_one_div_of_le (by norm_num) haR
    have hxη : (x : ℝ) * η ≤ 1 / 2 := by
      have := mul_le_mul_of_nonneg_right hxR hη0.le
      linarith
    have hw : (b : ℝ) / M - ((b : ℝ) * x / M) * η =
        (1 / (M : ℝ)) * ((b : ℝ) * (1 - (x : ℝ) * η)) := by ring
    rw [hw]
    have hu0 : 0 < 1 / (M : ℝ) := by positivity
    have hMN' : (M : ℝ) ≤ N := by exact_mod_cast hMN
    have hbM' : (b : ℝ) + 1 ≤ M := by exact_mod_cast hbM
    have hMinv : 1 / (N : ℝ) ≤ 1 / (M : ℝ) := one_div_le_one_div_of_le hMpos hMN'
    have hbx1 : 1 ≤ (b : ℝ) * (1 - (x : ℝ) * η) := by
      nlinarith [mul_nonneg (sub_nonneg.mpr hbR) (by linarith : (0 : ℝ) ≤ 1 - (x : ℝ) * η)]
    have hbx2 : (b : ℝ) * (1 - (x : ℝ) * η) ≤ b := by
      nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ b) hxη0]
    apply nid_ge_inv hN
    · calc 1 / (N : ℝ) ≤ 1 / (M : ℝ) := hMinv
        _ = (1 / (M : ℝ)) * 1 := by ring
        _ ≤ (1 / (M : ℝ)) * ((b : ℝ) * (1 - (x : ℝ) * η)) :=
            mul_le_mul_of_nonneg_left hbx1 hu0.le
    · have h3 : (1 / (M : ℝ)) * ((b : ℝ) * (1 - (x : ℝ) * η)) ≤ (1 / (M : ℝ)) * ((M : ℝ) - 1) :=
        mul_le_mul_of_nonneg_left (by linarith) hu0.le
      have h4 : (1 / (M : ℝ)) * ((M : ℝ) - 1) = 1 - 1 / (M : ℝ) := by
        field_simp
        try ring
      linarith

/-- Retained speeds in modulus `r2` (blocker `r1`, removed). -/
theorem retained_big {N r1 r2 : ℕ} (hr1 : N < 2 * r1) (h12 : r1 < r2) (h2N : r2 ≤ N)
    (c k' : ℤ) (hc : (r1 : ℤ) * c + 1 = (r2 : ℤ) * k') (hcop : IsCoprime (r2 : ℤ) c)
    (η : ℝ) (hη0 : 0 ≤ η) (hηN : (N : ℝ) * η ≤ 2 - (r2 : ℝ) / N)
    (x : ℕ) (hx1 : 1 ≤ x) (hxN : x ≤ N) (hx1' : x ≠ r1) (hx2' : x ≠ r2) :
    1 / (N : ℝ) ≤ nearestIntDist ((x : ℝ) * (((c : ℝ) + η) / r2)) := by
  have hN2 : N < 2 * r2 := by omega
  have hr2pos : 0 < r2 := by omega
  apply nid_residue_ge c η hr2pos h2N hxN hη0 hηN
  · intro hd
    have h3 : (r2 : ℤ) ∣ (x : ℤ) := hcop.dvd_of_dvd_mul_right hd
    exact not_dvd_retained hN2 hx1 hxN hx2' (Int.natCast_dvd_natCast.mp h3)
  · intro hd
    have h4 : (r2 : ℤ) ∣ ((x : ℤ) - r1) * c := by
      have e : ((x : ℤ) - r1) * c = ((x : ℤ) * c + 1) - ((r1 : ℤ) * c + 1) := by ring
      rw [e]
      exact dvd_sub hd ⟨k', hc⟩
    have h5 : (r2 : ℤ) ∣ (x : ℤ) - r1 := hcop.dvd_of_dvd_mul_right h4
    have h6 : (x : ℤ) - r1 = 0 :=
      Int.eq_zero_of_abs_lt_dvd h5 (abs_lt.mpr ⟨by omega, by omega⟩)
    omega

/-- Retained speeds in modulus `r1` (blockers `u = r2 - r1` retained and `r2` removed). -/
theorem retained_small {N r1 r2 u : ℕ} (hr1 : N < 2 * r1) (h12 : r2 = r1 + u) (hu1 : 1 ≤ u)
    (h2N : r2 ≤ N) (c k' : ℤ) (hc : (u : ℤ) * c + 1 = (r1 : ℤ) * k')
    (hcop : IsCoprime (r1 : ℤ) c) (η : ℝ) (hη0 : 0 ≤ η)
    (hηN : (N : ℝ) * η ≤ 2 - (r1 : ℝ) / N) (hu : (u : ℝ) * η ≤ 1 - (r1 : ℝ) / N)
    (x : ℕ) (hx1 : 1 ≤ x) (hxN : x ≤ N) (hx1' : x ≠ r1) (hx2' : x ≠ r2) :
    1 / (N : ℝ) ≤ nearestIntDist ((x : ℝ) * (((c : ℝ) + η) / r1)) := by
  have hr1pos : 0 < r1 := by omega
  have hr1N : r1 ≤ N := by omega
  by_cases hdv : (r1 : ℤ) ∣ (x : ℤ) * c + 1
  · have h4 : (r1 : ℤ) ∣ ((x : ℤ) - u) * c := by
      have e : ((x : ℤ) - u) * c = ((x : ℤ) * c + 1) - ((u : ℤ) * c + 1) := by ring
      rw [e]
      exact dvd_sub hdv ⟨k', hc⟩
    have h5 : (r1 : ℤ) ∣ (x : ℤ) - u := hcop.dvd_of_dvd_mul_right h4
    rcases Nat.lt_or_ge x r2 with hlt | hge
    · have h6 : (x : ℤ) - u = 0 :=
        Int.eq_zero_of_abs_lt_dvd h5 (abs_lt.mpr ⟨by omega, by omega⟩)
      have hxu : x = u := by omega
      rw [hxu]
      exact nid_unit_blocker_ge c k' η (by omega) (by omega) hr1N hη0 hc hu
    · have h5' : (r1 : ℤ) ∣ (x : ℤ) - r2 := by
        have e : (x : ℤ) - r2 = ((x : ℤ) - u) - r1 := by
          rw [h12]
          push_cast
          ring
        rw [e]
        exact dvd_sub h5 dvd_rfl
      have h6 : (x : ℤ) - r2 = 0 :=
        Int.eq_zero_of_abs_lt_dvd h5' (abs_lt.mpr ⟨by omega, by omega⟩)
      omega
  · apply nid_residue_ge c η hr1pos hr1N hxN hη0 hηN
    · intro hd
      have h3 : (r1 : ℤ) ∣ (x : ℤ) := hcop.dvd_of_dvd_mul_right hd
      exact not_dvd_retained hr1 hx1 hxN hx1' (Int.natCast_dvd_natCast.mp h3)
    · exact hdv

/-- **Case I** (`m1 + 1 ≤ r2`): `1/N ≤ ML`, at the time `t = (c + 1/(N m2))/r2`, `c r1 ≡ -1 (mod r2)`. -/
theorem caseI_ML {k N r1 r2 m1 m2 : ℕ} (hk : k + 1 = N) (hr1 : N < 2 * r1) (h12 : r1 < r2)
    (h2N : r2 ≤ N) (hcop : Nat.Coprime r1 r2) (hm1 : 2 ≤ m1) (hm2 : 2 ≤ m2)
    (hm1r : m1 + 1 ≤ r2) : 1 / (N : ℝ) ≤ ML (v2Fam k r1 r2 m1 m2) := by
  have hN2 : 2 ≤ N := by omega
  obtain ⟨u, w, huw⟩ : IsCoprime (r1 : ℤ) (r2 : ℤ) := Nat.isCoprime_iff_coprime.mpr hcop
  have hc : (r1 : ℤ) * (-u) + 1 = (r2 : ℤ) * w := by linear_combination (-1 : ℤ) * huw
  have hcopc : IsCoprime (r2 : ℤ) (-u) := ⟨w, -(r1 : ℤ), by linear_combination huw⟩
  obtain ⟨η, hη⟩ : ∃ η : ℝ, η = 1 / ((N : ℝ) * m2) := ⟨_, rfl⟩
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hm2R : (2 : ℝ) ≤ m2 := by exact_mod_cast hm2
  have hη0 : 0 < η := by rw [hη]; positivity
  have hNη : (N : ℝ) * η = 1 / m2 := by
    have : (m2 : ℝ) ≠ 0 := by linarith
    rw [hη]
    field_simp
    try ring
  have hr2N : (r2 : ℝ) / N ≤ 1 := by
    rw [div_le_iff₀ hNpos]
    have : (r2 : ℝ) ≤ N := by exact_mod_cast h2N
    linarith
  have h1m : (1 : ℝ) / m2 ≤ 1 / 2 := one_div_le_one_div_of_le (by norm_num) hm2R
  obtain ⟨hp1, hp2⟩ := inserted_pair (N := N) (M := r2) (x := r1) (a := m2) (b := m1) (-u) w η hη
    hN2 (by omega) h2N (by omega) hm2 hm1 hm1r hc
  refine ML_v2Fam_ge hk (1 / (N : ℝ)) ((((-u : ℤ) : ℝ) + η) / (r2 : ℝ)) ?_ hp2 hp1
  intro x hx1 hxN hxr1 hxr2
  exact retained_big hr1 h12 h2N (-u) w hc hcopc η hη0.le (by linarith) x hx1 hxN hxr1 hxr2

/-- **Case I'** (`m2 + 1 ≤ r1`): `1/N ≤ ML`, in the modulus `r1`, blocker class of `u = r2 - r1`. -/
theorem caseI'_ML {k N r1 r2 m1 m2 : ℕ} (hk : k + 1 = N) (hr1 : N < 2 * r1) (h12 : r1 < r2)
    (h2N : r2 ≤ N) (hcop : Nat.Coprime r1 r2) (hm1 : 2 ≤ m1) (hm2 : 2 ≤ m2)
    (hm2r : m2 + 1 ≤ r1) : 1 / (N : ℝ) ≤ ML (v2Fam k r1 r2 m1 m2) := by
  have hN2 : 2 ≤ N := by omega
  obtain ⟨p, q, hpq⟩ : IsCoprime (r1 : ℤ) (r2 : ℤ) := Nat.isCoprime_iff_coprime.mpr hcop
  obtain ⟨u, hu⟩ : ∃ u : ℕ, r2 = r1 + u := ⟨r2 - r1, by omega⟩
  have hu1 : 1 ≤ u := by omega
  have huZ : (u : ℤ) = (r2 : ℤ) - r1 := by rw [hu]; push_cast; ring
  -- blocker equations in modulus r1, with c = -q
  have hcu : (u : ℤ) * (-q) + 1 = (r1 : ℤ) * (p + q) := by
    rw [huZ]; linear_combination (-1 : ℤ) * hpq
  have hcr2 : (r2 : ℤ) * (-q) + 1 = (r1 : ℤ) * p := by linear_combination (-1 : ℤ) * hpq
  have hcopc : IsCoprime (r1 : ℤ) (-q) := ⟨p, -(r2 : ℤ), by linear_combination hpq⟩
  obtain ⟨η, hη⟩ : ∃ η : ℝ, η = 1 / ((N : ℝ) * m1) := ⟨_, rfl⟩
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hm1R : (2 : ℝ) ≤ m1 := by exact_mod_cast hm1
  have hη0 : 0 < η := by rw [hη]; positivity
  have hNη : (N : ℝ) * η = 1 / m1 := by
    have : (m1 : ℝ) ≠ 0 := by linarith
    rw [hη]
    field_simp
    try ring
  have hr1N : (r1 : ℝ) / N ≤ 1 := by
    rw [div_le_iff₀ hNpos]
    have : (r1 : ℝ) ≤ N := by exact_mod_cast (by omega : r1 ≤ N)
    linarith
  have h1m : (1 : ℝ) / m1 ≤ 1 / 2 := one_div_le_one_div_of_le (by norm_num) hm1R
  have hηle : η ≤ 1 / (N : ℝ) := by
    rw [hη]
    apply one_div_le_one_div_of_le hNpos
    nlinarith
  have huN : (u : ℝ) ≤ (N : ℝ) - r1 := by
    have : r1 + u ≤ N := by omega
    have h2 : ((r1 + u : ℕ) : ℝ) ≤ N := by exact_mod_cast this
    push_cast at h2
    linarith
  have hu_bd : (u : ℝ) * η ≤ 1 - (r1 : ℝ) / N := by
    have h3 : (u : ℝ) * η ≤ ((N : ℝ) - r1) * η := mul_le_mul_of_nonneg_right huN hη0.le
    have h4 : ((N : ℝ) - r1) * η ≤ ((N : ℝ) - r1) * (1 / N) :=
      mul_le_mul_of_nonneg_left hηle (by
        have : (r1 : ℝ) ≤ N := by exact_mod_cast (by omega : r1 ≤ N)
        linarith)
    have h5 : ((N : ℝ) - r1) * (1 / N) = 1 - (r1 : ℝ) / N := by
      field_simp
      try ring
    linarith
  obtain ⟨hp1, hp2⟩ := inserted_pair (N := N) (M := r1) (x := r2) (a := m1) (b := m2) (-q) p η hη
    hN2 (by omega) (by omega) h2N hm1 hm2 hm2r hcr2
  refine ML_v2Fam_ge hk (1 / (N : ℝ)) ((((-q : ℤ) : ℝ) + η) / (r1 : ℝ)) ?_ hp1 hp2
  intro x hx1 hxN hxr1 hxr2
  exact retained_small hr1 hu hu1 h2N (-q) (p + q) hcu hcopc η hη0.le (by linarith) hu_bd x hx1
    hxN hxr1 hxr2

end Gap
end Sext6
end LRSpectrumFull
