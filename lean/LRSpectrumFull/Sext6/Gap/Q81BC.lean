import LRSpectrumFull.Sext6.Gap.Q81Core
import LRSpectrumFull.Sext6.Gap.Q81Band

/-!
# Q8.1, Theorem BC (coprime, one inserted speed a multiple of `lcm(r1, r2) = r1 r2`: not tight)  [2026-11-25]

Source: the accompanying notes on Zhang's Question 8.1 section 4 (Theorem BC), with Lemma R / Corollary R1
(`Q81Band`).  Setting: `N = k + 1`, `4 ≤ N`, `N < 2 r1`, `r1 < r2 ≤ N`, `gcd(r1, r2) = 1`;
the inserted speeds are `w = κ r1 r2` (`κ ≥ 1`) and `p ≥ N + 1` with `r1 ∤ p`, `r2 ∤ p`, placed at the slots `r1`, `r2`
in either order (`v2G k r1 r2 a b` with `{a, b} = {w, p}`).

* `theoremBC` : `1/(N+1) < ML (v2G ..)`, so the set is not tight.
Extra hypothesis relative to the prose: `p ≥ N + 1` (the other inserted speed is a NEW element, as in setting S);
the prose uses it at "z = 0 is impossible since p ≤ r < A" (case `k = 1`).
No `sorry`, no `axiom`.

Convention: `N = k + 1` is the number of speeds of the vector `v : Fin (k+1) → ℤ`. Speeds are the moving runners; the runner at rest is not counted, so a vector of `N` speeds means `N + 1` runners and the Lonely Runner value is `1/(N+1)`.
Hypotheses: those of the individual statements (numerical bounds, structural conditions and, where named in the list above, window predicates such as `PrimeWin`, `CopWin`, `PrimeWindow7`, which later modules discharge for explicit ranges). The unproved predicates `DusartPi`, `LRCHyp`, `CopWinHyp` are not hypotheses of any statement in this module.
Axiom audit: covered by `Axioms8` (`#print axioms`; declarations not printed there are bricks of printed ones, so their axioms are bounded by the printed lines).
-/

namespace LRSpectrumFull
namespace Sext6
namespace Gap

/-- The speed vector with arbitrary inserted speeds `a` (slot `r1`) and `b` (slot `r2`). -/
def v2G (k r1 r2 a b : ℕ) : Fin (k + 1) → ℤ := fun i =>
  if (i : ℕ) + 1 = r1 then (a : ℤ)
  else if (i : ℕ) + 1 = r2 then (b : ℤ) else (((i : ℕ) + 1 : ℕ) : ℤ)

theorem v2G_at1 {k r1 r2 a b : ℕ} (i : Fin (k + 1)) (hi : (i : ℕ) + 1 = r1) :
    v2G k r1 r2 a b i = (a : ℤ) := by
  simp only [v2G]
  rw [if_pos hi]

theorem v2G_at2 {k r1 r2 a b : ℕ} (i : Fin (k + 1)) (hi1 : ¬ ((i : ℕ) + 1 = r1))
    (hi : (i : ℕ) + 1 = r2) : v2G k r1 r2 a b i = (b : ℤ) := by
  simp only [v2G]
  rw [if_neg hi1, if_pos hi]

theorem v2G_at0 {k r1 r2 a b : ℕ} (i : Fin (k + 1)) (hi1 : ¬ ((i : ℕ) + 1 = r1))
    (hi2 : ¬ ((i : ℕ) + 1 = r2)) : v2G k r1 r2 a b i = (((i : ℕ) + 1 : ℕ) : ℤ) := by
  simp only [v2G]
  rw [if_neg hi1, if_neg hi2]

/-- If `ML v ≤ c` then at every time some speed is within `c` of an integer. -/
theorem exists_close_of_ML_le {k : ℕ} (v : Fin (k + 1) → ℤ) (c : ℝ) (h : ML v ≤ c) (t : ℝ) :
    ∃ i, nearestIntDist ((v i : ℝ) * t) ≤ c := by
  have hML : gap v t ≤ ML v := by
    unfold ML
    exact le_csSup (bddAbove_range_gap v) ⟨t, rfl⟩
  obtain ⟨i, _, hi⟩ := Finset.exists_mem_eq_inf' Finset.univ_nonempty
    (fun i => nearestIntDist ((v i : ℝ) * t))
  refine ⟨i, ?_⟩
  have h2 : gap v t = nearestIntDist ((v i : ℝ) * t) := hi
  rw [← h2]
  exact hML.trans h

/-- At a time where no retained speed is within `θ`, one of the two inserted speeds is. -/
theorem cov_disj {k N r1 r2 a b : ℕ} (hk : k + 1 = N) {θ : ℝ} (hle : ML (v2G k r1 r2 a b) ≤ θ)
    (t : ℝ)
    (hret : ∀ x : ℕ, 1 ≤ x → x ≤ N → x ≠ r1 → x ≠ r2 → θ < nearestIntDist ((x : ℝ) * t)) :
    nearestIntDist ((a : ℝ) * t) ≤ θ ∨ nearestIntDist ((b : ℝ) * t) ≤ θ := by
  obtain ⟨i, hi⟩ := exists_close_of_ML_le (v2G k r1 r2 a b) θ hle t
  by_cases hi1 : (i : ℕ) + 1 = r1
  · rw [v2G_at1 i hi1] at hi
    left
    simpa using hi
  · by_cases hi2 : (i : ℕ) + 1 = r2
    · rw [v2G_at2 i hi1 hi2] at hi
      right
      simpa using hi
    · rw [v2G_at0 i hi1 hi2] at hi
      exfalso
      have hiN : (i : ℕ) < k + 1 := i.isLt
      have h1 := hret ((i : ℕ) + 1) (by omega) (by omega) hi1 hi2
      rw [Int.cast_natCast] at hi
      exact absurd hi (not_le.mpr h1)

theorem cov_wp {k N r1 r2 κ p a b : ℕ} (hk : k + 1 = N) {θ : ℝ} (hle : ML (v2G k r1 r2 a b) ≤ θ)
    (t : ℝ) (hab : (a = κ * (r1 * r2) ∧ b = p) ∨ (a = p ∧ b = κ * (r1 * r2)))
    (hret : ∀ x : ℕ, 1 ≤ x → x ≤ N → x ≠ r1 → x ≠ r2 → θ < nearestIntDist ((x : ℝ) * t)) :
    nearestIntDist (((κ * (r1 * r2) : ℕ) : ℝ) * t) ≤ θ ∨ nearestIntDist ((p : ℝ) * t) ≤ θ := by
  have h := cov_disj hk hle t hret
  rcases hab with ⟨ha, hb⟩ | ⟨ha, hb⟩
  · rw [ha, hb] at h
    exact h
  · rw [ha, hb] at h
    exact h.symm

/-- Integer form of the band lemma. -/
theorem band_int {N M m p : ℕ} (c : ℤ) (hN : 4 ≤ N) (hM : 0 < M) (hm : 2 ≤ m) (hp : 0 < p)
    (hcov : ∀ η : ℝ, 0 < η → η ≤ 1 / ((N : ℝ) + 1) →
      nearestIntDist ((m : ℝ) * η) ≤ 1 / ((N : ℝ) + 1) ∨
      nearestIntDist ((p : ℝ) * (((c : ℝ) + η) / M)) ≤ 1 / ((N : ℝ) + 1)) :
    ∃ z : ℤ, (M : ℤ) ∣ z + (p : ℤ) * c ∧ (m : ℤ) * (z * ((N : ℤ) + 1) - M) ≤ p ∧
      (m ≤ N → (p : ℤ) ≤ z * ((N : ℤ) + 1) + M) ∧
      (N < m → (p : ℤ) * N ≤ m * (z * ((N : ℤ) + 1) + M)) := by
  have hN' : (4 : ℝ) ≤ N := by exact_mod_cast hN
  obtain ⟨z, hdiv, hb, hc⟩ := free_class_band hN' M m p c hM hm hp hcov
  have hmpos : (0 : ℝ) < m := by exact_mod_cast (by omega : 0 < m)
  have hm0 : (m : ℝ) ≠ 0 := hmpos.ne'
  refine ⟨z, hdiv, ?_, ?_, ?_⟩
  · exact_mod_cast hb
  · intro hmN
    have h1 : (1 : ℝ) ≤ N / m := by
      rw [le_div_iff₀ hmpos]
      have : (m : ℝ) ≤ N := by exact_mod_cast hmN
      linarith
    rw [min_eq_right h1, mul_one] at hc
    exact_mod_cast hc
  · intro hNm
    have h1 : (N : ℝ) / m ≤ 1 := by
      rw [div_le_iff₀ hmpos]
      have : (N : ℝ) < m := by exact_mod_cast hNm
      linarith
    rw [min_eq_left h1] at hc
    have h2 : (p : ℝ) * N ≤ m * ((z : ℝ) * ((N : ℝ) + 1) + M) := by
      calc (p : ℝ) * N = (p : ℝ) * (N / m) * m := by
            field_simp
        _ ≤ ((z : ℝ) * ((N : ℝ) + 1) + M) * m := mul_le_mul_of_nonneg_right hc hmpos.le
        _ = m * ((z : ℝ) * ((N : ℝ) + 1) + M) := by ring
    exact_mod_cast h2

/-- Corollary R1 (`m ≤ N`): `z = 1`. -/
theorem z_one {m M p z N : ℤ} (hm : 3 ≤ m) (hM0 : 0 < M) (hMN : M ≤ N) (hp : N + 1 ≤ p)
    (b : m * (z * (N + 1) - M) ≤ p) (c : p ≤ z * (N + 1) + M) : z = 1 := by
  have hz1 : 1 ≤ z := by
    by_contra h
    have h0 : z ≤ 0 := by omega
    have : z * (N + 1) ≤ 0 := by
      nlinarith [mul_nonneg (neg_nonneg.mpr h0) (by omega : (0 : ℤ) ≤ N + 1)]
    linarith
  by_contra hne
  have h2 : 2 ≤ z := by omega
  have h3 : (m - 1) * (z * (N + 1)) ≤ (m + 1) * M := by nlinarith
  have h4 : (m - 1) * (2 * (N + 1)) ≤ (m - 1) * (z * (N + 1)) := by
    refine mul_le_mul_of_nonneg_left ?_ (by omega)
    nlinarith [mul_nonneg (sub_nonneg.mpr h2) (by omega : (0 : ℤ) ≤ N + 1)]
  have h5 : (m + 1) * M ≤ (m + 1) * N := mul_le_mul_of_nonneg_left hMN (by omega)
  nlinarith [mul_nonneg (by omega : (0 : ℤ) ≤ m - 3) (by omega : (0 : ℤ) ≤ N + 1)]

/-- Corollary R1 (`m > N`): `z = 1` (the case `z = 0` is excluded by the hypothesis `z ≠ 0`). -/
theorem z_one2 {m M p z N : ℤ} (hm : N + 1 ≤ m) (hM0 : 0 < M) (hMN : M ≤ N) (hN : 4 ≤ N)
    (hp : N + 1 ≤ p) (hz0 : z ≠ 0)
    (b : m * (z * (N + 1) - M) ≤ p) (c : p * N ≤ m * (z * (N + 1) + M)) : z = 1 := by
  have hmpos : 0 < m := by omega
  have hz1 : 1 ≤ z := by
    by_contra h
    have hzn : z ≤ -1 := by omega
    have h1 : z * (N + 1) ≤ -(N + 1) := by
      nlinarith [mul_nonneg (by omega : (0 : ℤ) ≤ -1 - z) (by omega : (0 : ℤ) ≤ N + 1)]
    have h2 : 0 < p * N := mul_pos (by omega) (by omega)
    have h3 : m * (z * (N + 1) + M) < 0 := by
      apply mul_neg_of_pos_of_neg hmpos
      linarith
    linarith
  by_contra hne
  have h2 : 2 ≤ z := by omega
  have h5 := mul_le_mul_of_nonneg_left b (show (0 : ℤ) ≤ N by omega)
  have h6 : m * (N * (z * (N + 1) - M)) ≤ m * (z * (N + 1) + M) := by nlinarith [h5, c]
  have h7 : N * (z * (N + 1) - M) ≤ z * (N + 1) + M := le_of_mul_le_mul_left h6 hmpos
  have h8 : 2 * (N + 1) * (N - 1) ≤ z * (N + 1) * (N - 1) := by
    nlinarith [mul_nonneg (mul_nonneg (sub_nonneg.mpr h2) (show (0 : ℤ) ≤ N + 1 by omega))
      (show (0 : ℤ) ≤ N - 1 by omega)]
  have h9 : M * (N + 1) ≤ N * (N + 1) := mul_le_mul_of_nonneg_right hMN (by omega)
  nlinarith [mul_nonneg (show (0 : ℤ) ≤ N - 4 by omega) (show (0 : ℤ) ≤ N by omega)]

/-- Arithmetic of the case `κ = 1`: both classes give `z = 1`, forcing `r1 = N - 1`, `r2 = N`, `p = 2 r2`. -/
theorem arith_k1 {N r1 r2 p z1 z2 m2 m1 : ℤ} (hN : 4 ≤ N) (hr1 : N < 2 * r1) (h12 : r1 < r2)
    (h2N : r2 ≤ N) (hp : N + 1 ≤ p) (hm2 : m2 = r1) (hm1 : m1 = r2)
    (b2 : m2 * (z2 * (N + 1) - r2) ≤ p) (c2 : p ≤ z2 * (N + 1) + r2)
    (b1 : m1 * (z1 * (N + 1) - r1) ≤ p) (c1 : p ≤ z1 * (N + 1) + r1) : p = 2 * r2 := by
  rw [hm2] at b2
  rw [hm1] at b1
  have hz2 : z2 = 1 := z_one (m := r1) (M := r2) (by omega) (by omega) h2N hp b2 c2
  have hz1 : z1 = 1 := z_one (m := r2) (M := r1) (by omega) (by omega) (by omega) hp b1 c1
  rw [hz2] at b2 c2
  rw [hz1] at b1 c1
  by_cases hs : r1 = N - 1
  · have hr2 : r2 = N := by omega
    rw [hs, hr2] at b1
    rw [hs] at c1
    rw [hr2]
    linarith
  · exfalso
    have hr1le : r1 ≤ N - 2 := by omega
    have e1 : (r1 + 1) * (N + 1 - r1) ≤ r2 * (N + 1 - r1) :=
      mul_le_mul_of_nonneg_right (by omega) (by omega)
    have e2 : 3 * r1 ≤ r1 * (N + 1 - r1) := by
      have := mul_le_mul_of_nonneg_left (show (3 : ℤ) ≤ N + 1 - r1 by omega)
        (show (0 : ℤ) ≤ r1 by omega)
      linarith
    nlinarith

/-- Arithmetic of the case `κ ≥ 2`: contradiction. -/
theorem arith_k2 {N r1 r2 κ p z1 z2 : ℤ} (hN : 4 ≤ N) (hr1 : N < 2 * r1) (h12 : r1 < r2)
    (h2N : r2 ≤ N) (hκ : 2 ≤ κ) (hp : N + 1 ≤ p) (hz2 : z2 ≠ 0) (hz1 : z1 ≠ 0)
    (b2 : κ * r1 * (z2 * (N + 1) - r2) ≤ p) (c2 : p * N ≤ κ * r1 * (z2 * (N + 1) + r2))
    (b1 : κ * r2 * (z1 * (N + 1) - r1) ≤ p) (c1 : p * N ≤ κ * r2 * (z1 * (N + 1) + r1)) :
    False := by
  have hm2 : N + 1 ≤ κ * r1 := by nlinarith
  have hm1 : N + 1 ≤ κ * r2 := by nlinarith
  have hz2' : z2 = 1 := z_one2 hm2 (by omega) h2N hN hp hz2 b2 c2
  have hz1' : z1 = 1 := z_one2 hm1 (by omega) (by omega) hN hp hz1 b1 c1
  rw [hz2'] at b2 c2
  rw [hz1'] at b1 c1
  have hκr2 : 0 < κ * r2 := by nlinarith
  have d1 : N * (N + 1 - r1) ≤ N + 1 + r1 := by
    have h1 : κ * r2 * (N * (N + 1 - r1)) ≤ κ * r2 * (N + 1 + r1) := by
      have := mul_le_mul_of_nonneg_left b1 (show (0 : ℤ) ≤ N by omega)
      nlinarith [this, c1]
    exact le_of_mul_le_mul_left h1 hκr2
  have hs : r1 = N - 1 := by
    by_contra hne
    have h3 : (3 : ℤ) ≤ N + 1 - r1 := by omega
    nlinarith [mul_le_mul_of_nonneg_left h3 (show (0 : ℤ) ≤ N by omega)]
  have hr2 : r2 = N := by omega
  rw [hs, hr2] at b1
  rw [hs, hr2] at c2
  have hκpos : 0 < κ := by omega
  have h := mul_le_mul_of_nonneg_right b1 (show (0 : ℤ) ≤ N by omega)
  nlinarith [h, c2, mul_pos hκpos (show (0 : ℤ) < N + 1 by omega)]

/-- **Theorem BC.**  `N = k + 1`, `4 ≤ N`, `N < 2 r1`, `r1 < r2 ≤ N`, `gcd(r1, r2) = 1`, `κ ≥ 1`, `p ≥ N + 1`,
`r1 ∤ p`, `r2 ∤ p`; the inserted speeds `{a, b} = {κ r1 r2, p}`.  Then `ML > 1/(N+1)`. -/
theorem theoremBC {k N r1 r2 κ p a b : ℕ} (hk : k + 1 = N) (h4 : 4 ≤ N) (hr1 : N < 2 * r1)
    (h12 : r1 < r2) (h2N : r2 ≤ N) (hcop : Nat.Coprime r1 r2) (hκ : 1 ≤ κ) (hpN : N + 1 ≤ p)
    (hp1 : ¬ r1 ∣ p) (hp2 : ¬ r2 ∣ p)
    (hab : (a = κ * (r1 * r2) ∧ b = p) ∨ (a = p ∧ b = κ * (r1 * r2))) :
    1 / ((N : ℝ) + 1) < ML (v2G k r1 r2 a b) := by
  by_contra hcon
  have hle : ML (v2G k r1 r2 a b) ≤ 1 / ((N : ℝ) + 1) := not_lt.mp hcon
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hN1 : (0 : ℝ) < (N : ℝ) + 1 := by linarith
  have hθN : 1 / ((N : ℝ) + 1) < 1 / (N : ℝ) := one_div_lt_one_div_of_lt hNpos (by linarith)
  have hηN_of : ∀ η : ℝ, η ≤ 1 / ((N : ℝ) + 1) → (N : ℝ) * η ≤ 1 := by
    intro η hη
    have h1 : (N : ℝ) * η ≤ (N : ℝ) * (1 / ((N : ℝ) + 1)) :=
      mul_le_mul_of_nonneg_left hη hNpos.le
    have h2 : (N : ℝ) * (1 / ((N : ℝ) + 1)) ≤ 1 := by
      rw [mul_one_div, div_le_iff₀ hN1]
      linarith
    linarith
  have hη_of : ∀ η : ℝ, η ≤ 1 / ((N : ℝ) + 1) → η ≤ 1 / (N : ℝ) := fun η h =>
    h.trans (one_div_le_one_div_of_le hNpos (by linarith))
  obtain ⟨u, w, huw⟩ : IsCoprime (r1 : ℤ) (r2 : ℤ) := Nat.isCoprime_iff_coprime.mpr hcop
  have hr1ge : 3 ≤ r1 := by omega
  have hr2ge : 4 ≤ r2 := by omega
  -- class C2: modulus r2, blocker r1
  have hc2 : (r1 : ℤ) * (-u) + 1 = (r2 : ℤ) * w := by linear_combination (-1 : ℤ) * huw
  have hcopc2 : IsCoprime (r2 : ℤ) (-u) := ⟨w, -(r1 : ℤ), by linear_combination huw⟩
  have hcov2 : ∀ η : ℝ, 0 < η → η ≤ 1 / ((N : ℝ) + 1) →
      nearestIntDist (((κ * r1 : ℕ) : ℝ) * η) ≤ 1 / ((N : ℝ) + 1) ∨
      nearestIntDist ((p : ℝ) * ((((-u : ℤ) : ℝ) + η) / (r2 : ℝ))) ≤ 1 / ((N : ℝ) + 1) := by
    intro η hη0 hη1
    have hr2N : (r2 : ℝ) / N ≤ 1 := by
      rw [div_le_iff₀ hNpos]
      have : (r2 : ℝ) ≤ N := by exact_mod_cast h2N
      linarith
    have hηN : (N : ℝ) * η ≤ 2 - (r2 : ℝ) / N := by linarith [hηN_of η hη1]
    have hdisj := cov_wp hk hle ((((-u : ℤ) : ℝ) + η) / (r2 : ℝ)) hab (by
      intro x hx1 hxN hxr1 hxr2
      exact lt_of_lt_of_le hθN
        (retained_big hr1 h12 h2N (-u) w hc2 hcopc2 η hη0.le hηN x hx1 hxN hxr1 hxr2))
    rcases hdisj with h | h
    · left
      have e : κ * (r1 * r2) = (κ * r1) * r2 := by ring
      rw [e, nid_mul_mod (κ * r1) r2 (-u) η (by omega)] at h
      exact h
    · right
      exact h
  -- class C1: modulus r1, blockers r2 - r1 (retained) and r2 (removed)
  obtain ⟨d, hd⟩ : ∃ d : ℕ, r2 = r1 + d := ⟨r2 - r1, by omega⟩
  have hd1 : 1 ≤ d := by omega
  have hdZ : (d : ℤ) = (r2 : ℤ) - r1 := by
    rw [hd]
    push_cast
    ring
  have hcu : (d : ℤ) * (-w) + 1 = (r1 : ℤ) * (u + w) := by
    rw [hdZ]
    linear_combination (-1 : ℤ) * huw
  have hcopc1 : IsCoprime (r1 : ℤ) (-w) := ⟨u, -(r2 : ℤ), by linear_combination huw⟩
  have hcov1 : ∀ η : ℝ, 0 < η → η ≤ 1 / ((N : ℝ) + 1) →
      nearestIntDist (((κ * r2 : ℕ) : ℝ) * η) ≤ 1 / ((N : ℝ) + 1) ∨
      nearestIntDist ((p : ℝ) * ((((-w : ℤ) : ℝ) + η) / (r1 : ℝ))) ≤ 1 / ((N : ℝ) + 1) := by
    intro η hη0 hη1
    have hr1R : (r1 : ℝ) ≤ N := by exact_mod_cast (by omega : r1 ≤ N)
    have hr1N : (r1 : ℝ) / N ≤ 1 := by
      rw [div_le_iff₀ hNpos]
      linarith
    have hηN : (N : ℝ) * η ≤ 2 - (r1 : ℝ) / N := by linarith [hηN_of η hη1]
    have hdle : (d : ℝ) ≤ (N : ℝ) - r1 := by
      have h2 : ((r1 + d : ℕ) : ℝ) ≤ N := by exact_mod_cast (by omega : r1 + d ≤ N)
      push_cast at h2
      linarith
    have hu : (d : ℝ) * η ≤ 1 - (r1 : ℝ) / N := by
      have h3 : (d : ℝ) * η ≤ ((N : ℝ) - r1) * η := mul_le_mul_of_nonneg_right hdle hη0.le
      have h4 : ((N : ℝ) - r1) * η ≤ ((N : ℝ) - r1) * (1 / N) :=
        mul_le_mul_of_nonneg_left (hη_of η hη1) (by linarith)
      have h5 : ((N : ℝ) - r1) * (1 / N) = 1 - (r1 : ℝ) / N := by
        have hN0 : (N : ℝ) ≠ 0 := hNpos.ne'
        field_simp
        try ring
      linarith
    have hdisj := cov_wp hk hle ((((-w : ℤ) : ℝ) + η) / (r1 : ℝ)) hab (by
      intro x hx1 hxN hxr1 hxr2
      exact lt_of_lt_of_le hθN
        (retained_small hr1 hd hd1 h2N (-w) (u + w) hcu hcopc1 η hη0.le hηN hu x hx1 hxN hxr1
          hxr2))
    rcases hdisj with h | h
    · left
      have e : κ * (r1 * r2) = (κ * r2) * r1 := by ring
      rw [e, nid_mul_mod (κ * r2) r1 (-w) η (by omega)] at h
      exact h
    · right
      exact h
  -- the two bands
  obtain ⟨z2, hdiv2, b2, c2a, c2b⟩ := band_int (N := N) (M := r2) (m := κ * r1) (p := p) (-u) h4
    (by omega) (by nlinarith) (by omega) hcov2
  obtain ⟨z1, hdiv1, b1, c1a, c1b⟩ := band_int (N := N) (M := r1) (m := κ * r2) (p := p) (-w) h4
    (by omega) (by nlinarith) (by omega) hcov1
  have hN4 : (4 : ℤ) ≤ N := by exact_mod_cast h4
  have hr1Z : (N : ℤ) < 2 * r1 := by exact_mod_cast hr1
  have h12Z : (r1 : ℤ) < r2 := by exact_mod_cast h12
  have h2NZ : (r2 : ℤ) ≤ N := by exact_mod_cast h2N
  have hpZ : (N : ℤ) + 1 ≤ p := by exact_mod_cast hpN
  rcases Nat.lt_or_ge κ 2 with hκ2 | hκ2
  · -- κ = 1
    have hκ1 : κ = 1 := by omega
    have hm2 : ((κ * r1 : ℕ) : ℤ) = r1 := by rw [hκ1]; simp
    have hm1 : ((κ * r2 : ℕ) : ℤ) = r2 := by rw [hκ1]; simp
    have hmN2 : κ * r1 ≤ N := by rw [hκ1]; omega
    have hmN1 : κ * r2 ≤ N := by rw [hκ1]; omega
    have hres := arith_k1 (N := (N : ℤ)) (r1 := (r1 : ℤ)) (r2 := (r2 : ℤ)) (p := (p : ℤ))
      (z1 := z1) (z2 := z2) (m2 := ((κ * r1 : ℕ) : ℤ)) (m1 := ((κ * r2 : ℕ) : ℤ)) hN4 hr1Z h12Z
      h2NZ hpZ hm2 hm1 b2 (c2a hmN2) b1 (c1a hmN1)
    have h2 : (r2 : ℤ) ∣ (p : ℤ) := ⟨2, by linarith⟩
    exact hp2 (Int.natCast_dvd_natCast.mp h2)
  · -- κ ≥ 2
    have hmN2 : N < κ * r1 := by nlinarith
    have hmN1 : N < κ * r2 := by nlinarith
    have hz2 : z2 ≠ 0 := by
      intro h0
      rw [h0] at hdiv2
      have h3 : (r2 : ℤ) ∣ (p : ℤ) * (-u) := by simpa using hdiv2
      exact hp2 (Int.natCast_dvd_natCast.mp (hcopc2.dvd_of_dvd_mul_right h3))
    have hz1 : z1 ≠ 0 := by
      intro h0
      rw [h0] at hdiv1
      have h3 : (r1 : ℤ) ∣ (p : ℤ) * (-w) := by simpa using hdiv1
      exact hp1 (Int.natCast_dvd_natCast.mp (hcopc1.dvd_of_dvd_mul_right h3))
    have hκZ : (2 : ℤ) ≤ κ := by exact_mod_cast hκ2
    have b2' := b2
    have c2' := c2b hmN2
    have b1' := b1
    have c1' := c1b hmN1
    push_cast at b2' c2' b1' c1'
    exact arith_k2 (N := (N : ℤ)) (r1 := (r1 : ℤ)) (r2 := (r2 : ℤ)) (κ := (κ : ℤ)) (p := (p : ℤ))
      (z1 := z1) (z2 := z2) hN4 hr1Z h12Z h2NZ hκZ hpZ hz2 hz1 b2' c2' b1' c1'

end Gap
end Sext6
end LRSpectrumFull
