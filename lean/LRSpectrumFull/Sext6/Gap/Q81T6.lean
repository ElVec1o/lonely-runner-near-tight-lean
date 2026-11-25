import LRSpectrumFull.Sext6.Gap.Q81T5

/-!
# Q8.1, Theorem T (exact tightness criterion for `gcd(r1, r2) > 1`)  [2026-11-25]

Source: the accompanying notes on Zhang's Question 8.1 section 4 (Theorem T).
Setting: `N = k + 1`, `4 ≤ N`, `N < 2 r1`, `r1 < r2 ≤ N`, `1 < gcd(r1, r2)`, `m1, m2 ≥ 2`, `V = v2Fam k r1 r2 m1 m2`.
Tight means `ML V ≤ 1/(N+1)` (every time some speed is within `1/(N+1)` of an integer).
A *failing unit* of the entry `r_i` (own multiplier `m_i`) is `b` coprime to `r_i` with `N + 1 - r_i ≤ b ≤ N`, `b < m_i (N + 1 - r_i)`;
it is *rescued* by `w_j = m_j r_j` if `∃ z ≥ 0` with `z b ≡ w_j (mod r_i)`, `m_i (z A - r_i) ≤ w_j`, `(A - r_i) w_j ≤ b (z A + r_i)`, `A = N + 1`.
* `class_cover_vec`, `class_cover_any` : the covering of one class `t = (c + η)/M` by the speeds of an abstract vector.
* `theoremT_if`  : all failing units of both entries rescued gives tight (no bound on `m_i` needed).
* `theoremT`     : for `m_i + 1 ≤ N`: tight iff all failing units of both entries are rescued.
No `sorry`, no `axiom`.

Convention: `N = k + 1` is the number of speeds of the vector `v : Fin (k+1) → ℤ`. Speeds are the moving runners; the runner at rest is not counted, so a vector of `N` speeds means `N + 1` runners and the Lonely Runner value is `1/(N+1)`.
Hypotheses: those of the individual statements (numerical bounds, structural conditions and, where named in the list above, window predicates such as `PrimeWin`, `CopWin`, `PrimeWindow7`, which later modules discharge for explicit ranges). The unproved predicates `DusartPi`, `LRCHyp`, `CopWinHyp` are not hypotheses of any statement in this module.
Axiom audit: covered by `Axioms22` (`#print axioms`; declarations not printed there are bricks of printed ones, so their axioms are bounded by the printed lines).
-/

namespace LRSpectrumFull
namespace Sext6
namespace Gap

theorem class_cover_vec {k N M m p R : ℕ} (v : Fin (k + 1) → ℤ)
    (hret : ∀ x : ℕ, 1 ≤ x → x ≤ N → x ≠ M → x ≠ R → ∃ i, v i = (x : ℤ))
    (hown : ∃ i, v i = ((m * M : ℕ) : ℤ)) (hpv : ∃ i, v i = (p : ℤ))
    (hMN : M ≤ N) (hN2 : N < 2 * M) (hM3 : 3 ≤ M) (hRN : N < 2 * R) (hg : 1 < Nat.gcd M R)
    (hm : 2 ≤ m)
    (hresc : ∀ b : ℕ, Nat.Coprime b M → N + 1 ≤ b + M → b ≤ N → b < m * (N + 1 - M) →
      ∃ z : ℕ, z * b ≡ p [MOD M] ∧ m * (z * (N + 1)) ≤ p + m * M ∧
        (N + 1 - M) * p ≤ b * (z * (N + 1) + M))
    (c : ℤ) (η : ℝ) (hη0 : 0 ≤ η) (hη1 : η * ((N : ℝ) + 1) ≤ 1) :
    ∃ i, nearestIntDist ((v i : ℝ) * (((c : ℝ) + η) / M)) ≤ 1 / ((N : ℝ) + 1) := by
  by_cases hcop : IsCoprime (M : ℤ) c
  · obtain ⟨b, hb1, hbN, k', hbc⟩ := exists_b c (by omega) hMN hcop
    have hbcop : Nat.Coprime b M := by
      have : IsCoprime (b : ℤ) (M : ℤ) := ⟨-c, k', by linear_combination (-1 : ℤ) * hbc⟩
      exact Nat.isCoprime_iff_coprime.mp this
    have hbM : b ≠ M := by
      intro h
      have h2 : Nat.gcd b M = 1 := hbcop
      rw [h, Nat.gcd_self] at h2
      omega
    have hbR : b ≠ R := by
      intro h
      have h2 : Nat.gcd b M = 1 := hbcop
      rw [h, Nat.gcd_comm] at h2
      omega
    rcases class_cover (N := N) (M := M) (m := m) (p := p) (b := b) c k' η hMN hN2 hM3 hm hη0 hη1
      hbc hb1 hbN (hresc b hbcop hb1 hbN) with h | h | h
    · obtain ⟨i, hi⟩ := hret b (by omega) hbN hbM hbR
      exact ⟨i, by rw [hi]; simpa using h⟩
    · obtain ⟨i, hi⟩ := hown
      exact ⟨i, by rw [hi]; simpa using h⟩
    · obtain ⟨i, hi⟩ := hpv
      exact ⟨i, by rw [hi]; simpa using h⟩
  · have hg1 : 1 < Int.gcd c (M : ℤ) := by
      have h1 : Int.gcd (M : ℤ) c ≠ 1 := fun h => hcop (Int.isCoprime_iff_gcd_eq_one.mpr h)
      have h2 : Int.gcd (M : ℤ) c ≠ 0 := by
        intro h
        rw [Int.gcd_eq_zero_iff] at h
        omega
      rw [Int.gcd_comm]
      omega
    obtain ⟨x, hx1, hx2, hx⟩ := nonunit_cover (N := N) c η (by omega) hη0 hη1 hg1
    obtain ⟨i, hi⟩ := hret x hx1 (by omega) (by omega) (by omega)
    exact ⟨i, by rw [hi]; simpa using hx⟩

theorem class_cover_any {k N M m p R : ℕ} (v : Fin (k + 1) → ℤ)
    (hret : ∀ x : ℕ, 1 ≤ x → x ≤ N → x ≠ M → x ≠ R → ∃ i, v i = (x : ℤ))
    (hown : ∃ i, v i = ((m * M : ℕ) : ℤ)) (hpv : ∃ i, v i = (p : ℤ))
    (hMN : M ≤ N) (hN2 : N < 2 * M) (hM3 : 3 ≤ M) (hRN : N < 2 * R) (hg : 1 < Nat.gcd M R)
    (hm : 2 ≤ m)
    (hresc : ∀ b : ℕ, Nat.Coprime b M → N + 1 ≤ b + M → b ≤ N → b < m * (N + 1 - M) →
      ∃ z : ℕ, z * b ≡ p [MOD M] ∧ m * (z * (N + 1)) ≤ p + m * M ∧
        (N + 1 - M) * p ≤ b * (z * (N + 1) + M))
    (t : ℝ) (j : ℤ) (hj : |(M : ℝ) * t - j| ≤ 1 / ((N : ℝ) + 1)) :
    ∃ i, nearestIntDist ((v i : ℝ) * t) ≤ 1 / ((N : ℝ) + 1) := by
  have hApos : (0 : ℝ) < (N : ℝ) + 1 := by positivity
  have hMR : (0 : ℝ) < M := by exact_mod_cast (by omega : 0 < M)
  have hη1 : |(M : ℝ) * t - j| * ((N : ℝ) + 1) ≤ 1 := by
    have h := mul_le_mul_of_nonneg_right hj hApos.le
    have e : 1 / ((N : ℝ) + 1) * ((N : ℝ) + 1) = 1 := by field_simp
    linarith
  by_cases h0 : 0 ≤ (M : ℝ) * t - j
  · have hη1' : ((M : ℝ) * t - j) * ((N : ℝ) + 1) ≤ 1 := by
      rw [abs_of_nonneg h0] at hη1
      exact hη1
    obtain ⟨i, hi⟩ := class_cover_vec (m := m) (p := p) (R := R) v hret hown hpv hMN hN2 hM3 hRN hg hm
      hresc j ((M : ℝ) * t - j) h0 hη1'
    refine ⟨i, ?_⟩
    have e : (((j : ℝ) + ((M : ℝ) * t - j)) / M) = t := by field_simp; ring
    rw [e] at hi
    exact hi
  · push Not at h0
    have hη1' : (-((M : ℝ) * t - j)) * ((N : ℝ) + 1) ≤ 1 := by
      rw [abs_of_neg h0] at hη1
      exact hη1
    obtain ⟨i, hi⟩ := class_cover_vec (m := m) (p := p) (R := R) v hret hown hpv hMN hN2 hM3 hRN hg hm
      hresc (-j) (-((M : ℝ) * t - j)) (by linarith) hη1'
    refine ⟨i, ?_⟩
    have e : ((((-j : ℤ) : ℝ) + (-((M : ℝ) * t - j))) / M) = -t := by
      push_cast; field_simp; ring
    rw [e] at hi
    have e2 : (v i : ℝ) * (-t) = -((v i : ℝ) * t) := by ring
    rw [e2, nearestIntDist_neg] at hi
    exact hi

theorem theoremT_if {k N r1 r2 m1 m2 : ℕ} (hk : k + 1 = N) (hN4 : 4 ≤ N)
    (hr1 : N < 2 * r1) (h12 : r1 < r2) (h2N : r2 ≤ N) (hg : 1 < Nat.gcd r1 r2)
    (hm1 : 2 ≤ m1) (hm2 : 2 ≤ m2)
    (H1 : ∀ b : ℕ, Nat.Coprime b r1 → N + 1 ≤ b + r1 → b ≤ N → b < m1 * (N + 1 - r1) →
      ∃ z : ℕ, z * b ≡ m2 * r2 [MOD r1] ∧ m1 * (z * (N + 1)) ≤ m2 * r2 + m1 * r1 ∧
        (N + 1 - r1) * (m2 * r2) ≤ b * (z * (N + 1) + r1))
    (H2 : ∀ b : ℕ, Nat.Coprime b r2 → N + 1 ≤ b + r2 → b ≤ N → b < m2 * (N + 1 - r2) →
      ∃ z : ℕ, z * b ≡ m1 * r1 [MOD r2] ∧ m2 * (z * (N + 1)) ≤ m1 * r1 + m2 * r2 ∧
        (N + 1 - r2) * (m1 * r1) ≤ b * (z * (N + 1) + r2)) :
    ML (v2Fam k r1 r2 m1 m2) ≤ 1 / ((N : ℝ) + 1) := by
  apply ML_le_of_cover
  intro t
  obtain ⟨j, kk, hk0, hkN, habs⟩ := Real.exists_int_int_abs_mul_sub_le t (n := N) (by omega)
  obtain ⟨q, hq⟩ : ∃ q : ℕ, (q : ℤ) = kk := ⟨kk.toNat, Int.toNat_of_nonneg hk0.le⟩
  rw [← hq] at habs hkN hk0
  have habs' : |(q : ℝ) * t - j| ≤ 1 / ((N : ℝ) + 1) := by simpa using habs
  have hq1 : 1 ≤ q := by omega
  have hqN : q ≤ N := by omega
  have hrN : ∀ x : ℕ, 1 ≤ x → x ≤ N → x ≠ r1 → x ≠ r2 →
      ∃ i, v2Fam k r1 r2 m1 m2 i = (x : ℤ) := fun x hx1 hxN hx2 hx3 =>
    v2Fam_ret x hx1 (by omega) ⟨hx2, hx3⟩
  have hi1 : ∃ i : Fin (k + 1), v2Fam k r1 r2 m1 m2 i = ((m1 * r1 : ℕ) : ℤ) :=
    ⟨⟨r1 - 1, by omega⟩, v2Fam_at1 _ (by simp; omega)⟩
  have hi2 : ∃ i : Fin (k + 1), v2Fam k r1 r2 m1 m2 i = ((m2 * r2 : ℕ) : ℤ) :=
    ⟨⟨r2 - 1, by omega⟩, v2Fam_at2 _ (by simp; omega) (by simp; omega)⟩
  by_cases hq1' : q = r1
  · subst hq1'
    exact class_cover_any (m := m1) (p := m2 * r2) (R := r2) (M := q) _
      (fun x hx1 hxN hxM hxR => hrN x hx1 hxN hxM hxR) hi1 hi2 (by omega) hr1 (by omega) (by omega) hg
      hm1 H1 t j habs'
  · by_cases hq2' : q = r2
    · subst hq2'
      exact class_cover_any (m := m2) (p := m1 * r1) (R := r1) (M := q) _
        (fun x hx1 hxN hxM hxR => hrN x hx1 hxN hxR hxM) hi2 hi1 h2N (by omega) (by omega)
        (by omega) (by rw [Nat.gcd_comm]; exact hg) hm2 H2 t j habs'
    · obtain ⟨i, hi⟩ := hrN q hq1 hqN hq1' hq2'
      refine ⟨i, ?_⟩
      rw [hi]
      have := nearestIntDist_le_dist ((q : ℝ) * t) j
      have e : (((q : ℤ) : ℝ)) = (q : ℝ) := by simp
      rw [e]
      exact this.trans habs'

/-- **Theorem T** (`gcd(r1, r2) > 1`, `m_i + 1 ≤ N`): `V` is tight iff every failing unit of both entries is rescued by the other inserted speed. -/
theorem theoremT {k N r1 r2 m1 m2 : ℕ} (hk : k + 1 = N) (hN4 : 4 ≤ N)
    (hr1 : N < 2 * r1) (h12 : r1 < r2) (h2N : r2 ≤ N) (hg : 1 < Nat.gcd r1 r2)
    (hm1 : 2 ≤ m1) (hm2 : 2 ≤ m2) (hm1N : m1 + 1 ≤ N) (hm2N : m2 + 1 ≤ N) :
    ML (v2Fam k r1 r2 m1 m2) ≤ 1 / ((N : ℝ) + 1) ↔
      ((∀ b : ℕ, Nat.Coprime b r1 → N + 1 ≤ b + r1 → b ≤ N → b < m1 * (N + 1 - r1) →
        ∃ z : ℕ, z * b ≡ m2 * r2 [MOD r1] ∧ m1 * (z * (N + 1)) ≤ m2 * r2 + m1 * r1 ∧
          (N + 1 - r1) * (m2 * r2) ≤ b * (z * (N + 1) + r1)) ∧
      (∀ b : ℕ, Nat.Coprime b r2 → N + 1 ≤ b + r2 → b ≤ N → b < m2 * (N + 1 - r2) →
        ∃ z : ℕ, z * b ≡ m1 * r1 [MOD r2] ∧ m2 * (z * (N + 1)) ≤ m1 * r1 + m2 * r2 ∧
          (N + 1 - r2) * (m1 * r1) ≤ b * (z * (N + 1) + r2))) :=
  ⟨fun h => theoremT_only_if hk hN4 hr1 h12 h2N hm1 hm2 hm1N hm2N h,
   fun ⟨H1, H2⟩ => theoremT_if hk hN4 hr1 h12 h2N hg hm1 hm2 H1 H2⟩

end Gap
end Sext6
end LRSpectrumFull
