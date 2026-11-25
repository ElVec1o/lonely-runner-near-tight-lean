import LRSpectrumFull.Sext6.Gap.LinLMeas

/-!
# Theorem L (linear robustness), module 2: the per-speed total  [2026-11-25]

Source: the accompanying notes on Theorem L, Lemmas 4 and 5 (crude constant 18; the lattice identity is not used here).

* `cop_card_le_two` : pairwise coprime numbers `≥ B` dividing a nonzero `M` with `|M| < B^3`: at most two.
* `zero_forces`     : `w = e r` with positive coverage forces `D = 2N-1`.
* `small_total`     : for a non-oscillating speed `w > N`, the total bad measure over a pairwise coprime
                      family of windows is at most `18 · (window length)`.
No `sorry`, no `axiom`.

Convention: `N` is a natural number; `w` a natural number speed `> N`; `F` a finite set of moduli.
Hypotheses: those of the individual statements.  Axiom audit: `Axioms26`.
-/

namespace LRSpectrumFull
namespace Sext6
namespace Gap
namespace LinL

open MeasureTheory Function

/-- **Lemma 4.** -/
theorem cop_card_le_two {T : Finset ℕ} (hT : (T : Set ℕ).Pairwise Nat.Coprime) {B : ℕ} (hB1 : 1 ≤ B)
    (hB : ∀ D ∈ T, B ≤ D) {M : ℤ} (hM0 : M ≠ 0) (hdvd : ∀ D ∈ T, (D : ℤ) ∣ M)
    (hMlt : M.natAbs < B ^ 3) : T.card ≤ 2 := by
  by_contra h
  push Not at h
  have hcopZ : (T : Set ℕ).Pairwise (IsCoprime on fun D : ℕ => (D : ℤ)) :=
    fun x hx y hy hxy => Nat.isCoprime_iff_coprime.mpr (hT hx hy hxy)
  have h1 := Finset.prod_dvd_of_coprime hcopZ hdvd
  have h1' : ((∏ D ∈ T, D : ℕ) : ℤ) ∣ M := by rw [Nat.cast_prod]; exact h1
  have h2 : (∏ D ∈ T, D) ∣ M.natAbs := Int.natCast_dvd.mp h1'
  have h3 : (∏ D ∈ T, D) ≤ M.natAbs := Nat.le_of_dvd (Int.natAbs_pos.mpr hM0) h2
  have h4 : B ^ T.card ≤ ∏ D ∈ T, D := Finset.pow_card_le_prod T (fun D => D) B hB
  have h5 : B ^ 3 ≤ B ^ T.card := Nat.pow_le_pow_right hB1 h
  exact absurd (h5.trans (h4.trans h3)) (not_le.mpr hMlt)

/-- A zero case `w = e r` with positive coverage forces `D = 2N - 1`. -/
theorem zero_forces {N r w D : ℕ} {e : ℤ} (hr1 : 1 ≤ r) (hr2 : r + 2 ≤ N) (hw : N < w)
    (hwe : (w : ℤ) = e * r) (h : |e| * (N : ℤ) ^ 2 < D * N + w) : 2 * N ≤ D + 1 := by
  by_contra hcon
  push Not at hcon
  have hr1' : (1 : ℤ) ≤ r := by exact_mod_cast hr1
  have hr2' : (r : ℤ) + 2 ≤ N := by exact_mod_cast hr2
  have hw' : (N : ℤ) + 1 ≤ w := by exact_mod_cast hw
  have he2 : 2 ≤ e := by
    by_contra h2
    push Not at h2
    have h3 : e * (r : ℤ) ≤ 1 * r := mul_le_mul_of_nonneg_right (by omega) (by linarith)
    linarith
  have habs : |e| = e := abs_of_nonneg (by linarith)
  rw [habs, hwe] at h
  have hD : (D : ℤ) + 2 ≤ 2 * N := by
    have : D + 2 ≤ 2 * N := by omega
    exact_mod_cast this
  have hN0 : (0 : ℤ) ≤ N := by linarith
  have hNr : (0 : ℤ) ≤ (N : ℤ) ^ 2 - r := by nlinarith
  have h1 : e * ((N : ℤ) ^ 2 - r) < D * N := by linarith
  have h2 : 2 * ((N : ℤ) ^ 2 - r) ≤ e * ((N : ℤ) ^ 2 - r) := by
    nlinarith [mul_nonneg (sub_nonneg.mpr he2) hNr]
  have h3 : (D : ℤ) * N ≤ (2 * N - 2) * N := by
    apply mul_le_mul_of_nonneg_right _ hN0
    linarith
  nlinarith

/-- **Lemma 5 (crude form).** -/
theorem small_total {N r w : ℕ} (hN : 10 ≤ N) (hr1 : 1 ≤ r) (hr2 : r + 2 ≤ N) (hw : N < w)
    (hsm : 2 * (w : ℝ) ≤ (2 * (N : ℝ) - 1) * N * (N - 2))
    (F : Finset ℕ) (hF : ∀ D ∈ F, N + 1 + r ≤ D ∧ D + 1 ≤ 2 * N)
    (hcop : (F : Set ℕ).Pairwise Nat.Coprime) (a b : ℕ → ℤ)
    (hab : ∀ D ∈ F, a D * (r : ℤ) + b D * (D : ℤ) = 1) :
    ∑ D ∈ F, badMeas N w ((a D : ℝ) / D - lwd N) ((a D : ℝ) / D + lwd N) ≤ 18 * (2 * lwd N) := by
  classical
  have hNR : (10 : ℝ) ≤ N := by exact_mod_cast hN
  have hNpos : (0 : ℝ) < N := by linarith
  have hd0 : 0 < lwd N := lwd_pos (by omega)
  set m : ℕ → ℝ := fun D => badMeas N w ((a D : ℝ) / D - lwd N) ((a D : ℝ) / D + lwd N) with hm
  have hm0 : ∀ D, 0 ≤ m D := fun D => badMeas_nonneg _ _ _ _
  have hm1 : ∀ D, m D ≤ 2 * lwd N := by
    intro D
    have := badMeas_le_len N w (lo := (a D : ℝ) / D - lwd N) (hi := (a D : ℝ) / D + lwd N)
      (by linarith)
    simp only [hm]
    linarith
  obtain ⟨P, hPdef⟩ : ∃ P : Finset ℕ, P = F.filter (fun D => 0 < m D) := ⟨_, rfl⟩
  have hPF : ∀ D ∈ P, D ∈ F ∧ 0 < m D := by
    intro D hD
    rw [hPdef] at hD
    exact Finset.mem_filter.mp hD
  have hsumP : ∑ D ∈ F, m D = ∑ D ∈ P, m D := by
    rw [hPdef]
    exact (Finset.sum_filter_of_ne (fun D _ h => lt_of_le_of_ne (hm0 D) (Ne.symm h))).symm
  have hdata : ∀ D ∈ P, ∃ e : ℤ, (D : ℤ) ∣ (w : ℤ) - e * r ∧ |e| * (N : ℤ) ^ 2 < D * N + w ∧
      m D ≤ 2 / ((N : ℝ) * w) := by
    intro D hD
    obtain ⟨hDF, hDpos⟩ := hPF D hD
    exact arc_data (a D) (b D) (hab D hDF) hN (by have := (hF D hDF).1; omega) (hF D hDF).2 hw hsm
      hDpos
  choose! e he using hdata
  obtain ⟨q, hq⟩ : ∃ q : ℕ, q = w / N ^ 2 := ⟨_, rfl⟩
  have hwq : w < N ^ 2 * (q + 1) := by rw [hq]; exact Nat.lt_mul_div_succ w (by positivity)
  have hw3 : w < N ^ 3 := by
    have : (w : ℝ) < (N : ℝ) ^ 3 := by
      nlinarith [mul_pos hNpos hNpos, hsm]
    exact_mod_cast this
  have hqN : q < N := by
    rw [hq]
    exact Nat.div_lt_of_lt_mul (by calc w < N ^ 3 := hw3
      _ = N ^ 2 * N := by ring)
  have he_le : ∀ D ∈ P, |e D| ≤ (q : ℤ) + 2 := by
    intro D hD
    have h1 := (he D hD).2.1
    have hDF := (hPF D hD).1
    have hDle := (hF D hDF).2
    have h2 : (D : ℤ) * N ≤ 2 * (N : ℤ) ^ 2 := by
      have : (D : ℤ) ≤ 2 * N := by exact_mod_cast (by omega : D ≤ 2 * N)
      nlinarith
    have h3 : (w : ℤ) < (N : ℤ) ^ 2 * ((q : ℤ) + 1) := by exact_mod_cast hwq
    have h4 : |e D| * (N : ℤ) ^ 2 < ((q : ℤ) + 3) * (N : ℤ) ^ 2 := by nlinarith
    have h5 : |e D| < (q : ℤ) + 3 := lt_of_mul_lt_mul_right h4 (by positivity)
    omega
  obtain ⟨Z, hZdef⟩ : ∃ Z : Finset ℕ, Z = P.filter (fun D => (w : ℤ) = e D * r) := ⟨_, rfl⟩
  obtain ⟨Y, hYdef⟩ : ∃ Y : Finset ℕ, Y = P.filter (fun D => ¬ ((w : ℤ) = e D * r)) := ⟨_, rfl⟩
  have hZmem : ∀ D ∈ Z, D ∈ P ∧ (w : ℤ) = e D * r := by
    intro D hD
    rw [hZdef] at hD
    exact Finset.mem_filter.mp hD
  have hYmem : ∀ D ∈ Y, D ∈ P ∧ ¬ ((w : ℤ) = e D * r) := by
    intro D hD
    rw [hYdef] at hD
    exact Finset.mem_filter.mp hD
  have hPcard : P.card = Z.card + Y.card := by
    rw [hZdef, hYdef]
    exact (Finset.card_filter_add_card_filter_not (s := P) (fun D => (w : ℤ) = e D * r)).symm
  have hZsub : Z ⊆ {2 * N - 1} := by
    intro D hD
    obtain ⟨hDP, hwe⟩ := hZmem D hD
    have hDF := (hPF D hDP).1
    have h1 := zero_forces hr1 hr2 hw hwe (he D hDP).2.1
    have h2 := (hF D hDF).2
    simp only [Finset.mem_singleton]
    omega
  have hZcard : Z.card ≤ 1 := (Finset.card_le_card hZsub).trans (by simp)
  have hfib : ∀ e0 ∈ Y.image e, (Y.filter (fun D => e D = e0)).card ≤ 2 := by
    intro e0 he0
    obtain ⟨D0, hD0Y, rfl⟩ := Finset.mem_image.mp he0
    obtain ⟨hD0P, hD0n⟩ := hYmem D0 hD0Y
    have hTsub : (Y.filter (fun D => e D = e D0)) ⊆ F := by
      intro D hD
      exact (hPF D (hYmem D (Finset.mem_filter.mp hD).1).1).1
    refine cop_card_le_two (B := N + 2) (M := (w : ℤ) - e D0 * r) (hcop.mono (by exact_mod_cast hTsub))
      (by omega) ?_ ?_ ?_ ?_
    · intro D hD
      have := (hF D (hTsub hD)).1
      omega
    · intro h
      apply hD0n
      linarith
    · intro D hD
      obtain ⟨hDY, hDe⟩ := Finset.mem_filter.mp hD
      have := (he D (hYmem D hDY).1).1
      rw [hDe] at this
      exact this
    · have h1 := he_le D0 hD0P
      have hqN' : (q : ℤ) + 2 ≤ N + 1 := by
        have : q + 1 ≤ N := hqN
        have : (q : ℤ) + 1 ≤ N := by exact_mod_cast this
        linarith
      have hr1' : (1 : ℤ) ≤ r := by exact_mod_cast hr1
      have hr2' : (r : ℤ) + 2 ≤ N := by exact_mod_cast hr2
      have hw3' : (w : ℤ) < (N : ℤ) ^ 3 := by exact_mod_cast hw3
      have hN0 : (0 : ℤ) ≤ N := by linarith
      have hM1 : |(w : ℤ) - e D0 * r| ≤ w + |e D0| * r := by
        rw [abs_le]
        have a1 := neg_abs_le (e D0)
        have a2 := le_abs_self (e D0)
        have a3 : (0 : ℤ) ≤ r := by linarith
        constructor
        · nlinarith [mul_le_mul_of_nonneg_right a2 a3, (Nat.cast_nonneg w : (0 : ℤ) ≤ w)]
        · nlinarith [mul_le_mul_of_nonneg_right a1 a3]
      have hM2 : |e D0| * r ≤ (N + 1 : ℤ) * (N - 2) := by
        have a3 : (0 : ℤ) ≤ r := by linarith
        have a4 : |e D0| ≤ (N : ℤ) + 1 := by linarith
        have := mul_le_mul a4 (by linarith : (r : ℤ) ≤ N - 2) a3 (by linarith)
        exact this
      have hM3 : |(w : ℤ) - e D0 * r| < ((N + 2 : ℕ) ^ 3 : ℕ) := by
        push_cast
        nlinarith
      have : (((w : ℤ) - e D0 * r).natAbs : ℤ) < (((N + 2) ^ 3 : ℕ) : ℤ) := by
        rw [Int.natCast_natAbs]
        exact hM3
      exact_mod_cast this
  have himg : Y.image e ⊆ Finset.Icc (-((q : ℤ) + 2)) ((q : ℤ) + 2) := by
    intro x hx
    obtain ⟨D, hD, rfl⟩ := Finset.mem_image.mp hx
    exact Finset.mem_Icc.mpr (abs_le.mp (he_le D (hYmem D hD).1))
  have hIcard : (Finset.Icc (-((q : ℤ) + 2)) ((q : ℤ) + 2)).card = 2 * q + 5 := by
    rw [Int.card_Icc]
    omega
  have hYcard : Y.card ≤ 2 * (Y.image e).card := Finset.card_le_mul_card_image Y 2 hfib
  have hPbound : P.card ≤ 4 * q + 10 := by
    rcases Z.eq_empty_or_nonempty with hZe | ⟨D0, hD0Z⟩
    · have h2 : (Y.image e).card ≤ 2 * q + 5 := (Finset.card_le_card himg).trans hIcard.le
      rw [hPcard, hZe]
      simp only [Finset.card_empty]
      omega
    · obtain ⟨hD0P, hZ0⟩ := hZmem D0 hD0Z
      have he0 : e D0 ∈ Finset.Icc (-((q : ℤ) + 2)) ((q : ℤ) + 2) :=
        Finset.mem_Icc.mpr (abs_le.mp (he_le D0 hD0P))
      have hnot : e D0 ∉ Y.image e := by
        intro h
        obtain ⟨D, hD, hDe⟩ := Finset.mem_image.mp h
        obtain ⟨_, hnw⟩ := hYmem D hD
        apply hnw
        rw [hDe]
        exact hZ0
      have hsub : Y.image e ⊆ (Finset.Icc (-((q : ℤ) + 2)) ((q : ℤ) + 2)).erase (e D0) := by
        intro x hx
        exact Finset.mem_erase.mpr ⟨fun h => hnot (h ▸ hx), himg hx⟩
      have h2 := Finset.card_le_card hsub
      rw [Finset.card_erase_of_mem he0, hIcard] at h2
      rw [hPcard]
      omega
  rw [hsumP]
  by_cases hcase : w ≤ 2 * N ^ 2
  · have hq2 : q ≤ 2 := by
      rw [hq]
      exact Nat.div_le_of_le_mul (by linarith)
    have hP18 : (P.card : ℝ) ≤ 18 := by exact_mod_cast (by omega : P.card ≤ 18)
    calc ∑ D ∈ P, m D ≤ ∑ D ∈ P, 2 * lwd N := Finset.sum_le_sum (fun D _ => hm1 D)
      _ = P.card * (2 * lwd N) := by simp
      _ ≤ 18 * (2 * lwd N) := by nlinarith
  · push Not at hcase
    have hqR : (q : ℝ) ≤ w / (N : ℝ) ^ 2 := by rw [hq]; have := Nat.cast_div_le (α := ℝ) (m := w) (n := N ^ 2); push_cast at this; exact this
    have hPR : (P.card : ℝ) ≤ 4 * ((w : ℝ) / (N : ℝ) ^ 2) + 10 := by
      have : (P.card : ℝ) ≤ 4 * q + 10 := by exact_mod_cast hPbound
      linarith
    have hwR : (0 : ℝ) < w := by exact_mod_cast (by omega : 0 < w)
    have hcaseR : 2 * (N : ℝ) ^ 2 < w := by exact_mod_cast hcase
    have hfinal : (4 * ((w : ℝ) / (N : ℝ) ^ 2) + 10) * (2 / ((N : ℝ) * w)) ≤ 18 * (2 * lwd N) := by
      have e1 : (4 * ((w : ℝ) / (N : ℝ) ^ 2) + 10) * (2 / ((N : ℝ) * w)) =
          8 / (N : ℝ) ^ 3 + 20 / ((N : ℝ) * w) := by
        field_simp
        ring
      have e2 : 20 / ((N : ℝ) * w) ≤ 10 / (N : ℝ) ^ 3 := by
        rw [div_le_div_iff₀ (by positivity) (by positivity)]
        nlinarith [mul_pos hNpos hNpos, mul_pos (mul_pos hNpos hNpos) hNpos]
      have hX : (0 : ℝ) < (2 * (N : ℝ) - 1) * (N : ℝ) ^ 2 := by
        have a1 : (0 : ℝ) < 2 * N - 1 := by linarith
        positivity
      have e3 : 18 * (2 * lwd N) = 36 / ((2 * (N : ℝ) - 1) * (N : ℝ) ^ 2) := by
        unfold lwd; ring
      have e4 : 18 / (N : ℝ) ^ 3 ≤ 36 / ((2 * (N : ℝ) - 1) * (N : ℝ) ^ 2) := by
        rw [div_le_div_iff₀ (by positivity) hX]
        nlinarith [mul_pos (mul_pos hNpos hNpos) hNpos, mul_pos hNpos hNpos]
      have e5 : 8 / (N : ℝ) ^ 3 + 10 / (N : ℝ) ^ 3 = 18 / (N : ℝ) ^ 3 := by ring
      rw [e1, e3]
      linarith
    calc ∑ D ∈ P, m D ≤ ∑ D ∈ P, 2 / ((N : ℝ) * w) := Finset.sum_le_sum (fun D hD => (he D hD).2.2)
      _ = P.card * (2 / ((N : ℝ) * w)) := by simp
      _ ≤ (4 * ((w : ℝ) / (N : ℝ) ^ 2) + 10) * (2 / ((N : ℝ) * w)) :=
          mul_le_mul_of_nonneg_right hPR (by positivity)
      _ ≤ 18 * (2 * lwd N) := hfinal

/-- The per-speed total bound with constant `C`, as a hypothesis predicate of the assembly. -/
def SmallTot (C N r : ℕ) : Prop :=
  10 ≤ N → 1 ≤ r → r + 2 ≤ N → ∀ w : ℕ, N < w →
    2 * (w : ℝ) ≤ (2 * (N : ℝ) - 1) * N * (N - 2) →
    ∀ F : Finset ℕ, (∀ D ∈ F, N + 1 + r ≤ D ∧ D + 1 ≤ 2 * N) →
      (F : Set ℕ).Pairwise Nat.Coprime → ∀ a b : ℕ → ℤ,
      (∀ D ∈ F, a D * (r : ℤ) + b D * (D : ℤ) = 1) →
      ∑ D ∈ F, badMeas N w ((a D : ℝ) / D - lwd N) ((a D : ℝ) / D + lwd N) ≤ C * (2 * lwd N)

/-- Stage A: constant 18. -/
theorem smallTot_18 (N r : ℕ) : SmallTot 18 N r := by
  intro hN hr1 hr2 w hw hsm F hF hcop a b hab
  have := small_total hN hr1 hr2 hw hsm F hF hcop a b hab
  exact_mod_cast this

end LinL
end Gap
end Sext6
end LRSpectrumFull
