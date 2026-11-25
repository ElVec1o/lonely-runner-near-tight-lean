import LRSpectrumFull.Sext6.Gap.LinLCount
import LRSpectrumFull.Sext6.Gap.LinLLattice

/-!
# Theorem L (linear robustness), module 6: the per-speed total with constant 8  [2026-11-25]

Source: the accompanying notes on Theorem L, Lemma 5(ii) (Stage B).  The per-modulus bound `m(D) ≤ lam(2σ, d, -eσ)`
(arc position moved to the lattice `σ ℤ`, `σ = 1/(w(2N-1))`) and the lattice identity give

  `∑_{D ∈ F} badMeas ≤ 8 · (2 lwd N)`

for a non-oscillating speed `w` and a pairwise coprime family of windows (at most two moduli per value `e`).
* `small_total8` : the bound.  * `smallTot_8` : it as the predicate `SmallTot 8 N r`.
No `sorry`, no `axiom`.

Convention: `N` natural number; `w` a natural number speed `> N`.
Hypotheses: those of the individual statements.  Axiom audit: `Axioms26`.
-/

namespace LRSpectrumFull
namespace Sext6
namespace Gap
namespace LinL

open MeasureTheory Function

/-- **Lemma 5(ii).** -/
theorem small_total8 {N r w : ℕ} (hN : 10 ≤ N) (hr1 : 1 ≤ r) (hr2 : r + 2 ≤ N) (hw : N < w)
    (hsm : 2 * (w : ℝ) ≤ (2 * (N : ℝ) - 1) * N * (N - 2))
    (F : Finset ℕ) (hF : ∀ D ∈ F, N + 1 + r ≤ D ∧ D + 1 ≤ 2 * N)
    (hcop : (F : Set ℕ).Pairwise Nat.Coprime) (a b : ℕ → ℤ)
    (hab : ∀ D ∈ F, a D * (r : ℤ) + b D * (D : ℤ) = 1) :
    ∑ D ∈ F, badMeas N w ((a D : ℝ) / D - lwd N) ((a D : ℝ) / D + lwd N) ≤ 8 * (2 * lwd N) := by
  classical
  have hNR : (10 : ℝ) ≤ N := by exact_mod_cast hN
  have hNpos : (0 : ℝ) < N := by linarith
  have hd0 : 0 < lwd N := lwd_pos (by omega)
  have hwR : (0 : ℝ) < w := by exact_mod_cast (by omega : 0 < w)
  set m : ℕ → ℝ := fun D => badMeas N w ((a D : ℝ) / D - lwd N) ((a D : ℝ) / D + lwd N) with hm
  have hm0 : ∀ D, 0 ≤ m D := fun D => badMeas_nonneg _ _ _ _
  obtain ⟨P, hPdef⟩ : ∃ P : Finset ℕ, P = F.filter (fun D => 0 < m D) := ⟨_, rfl⟩
  have hPF : ∀ D ∈ P, D ∈ F ∧ 0 < m D := by
    intro D hD
    rw [hPdef] at hD
    exact Finset.mem_filter.mp hD
  have hsumP : ∑ D ∈ F, m D = ∑ D ∈ P, m D := by
    rw [hPdef]
    exact (Finset.sum_filter_of_ne (fun D _ h => lt_of_le_of_ne (hm0 D) (Ne.symm h))).symm
  have hdata : ∀ D ∈ P, ∃ e : ℤ, (D : ℤ) ∣ (w : ℤ) - e * r ∧ |e| * (N : ℤ) ^ 2 < D * N + w ∧
      m D ≤ 2 / ((N : ℝ) * w) ∧
      m D ≤ lam (1 / ((N : ℝ) * w)) (lwd N) (-(e : ℝ) / ((w : ℝ) * D)) := by
    intro D hD
    obtain ⟨hDF, hDpos⟩ := hPF D hD
    exact arc_data' (a D) (b D) (hab D hDF) hN (by have := (hF D hDF).1; omega) (hF D hDF).2 hw hsm
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
  -- fibres of `e` on `P` have at most two elements
  have hfib : ∀ e0 ∈ P.image e, (P.filter (fun D => e D = e0)).card ≤ 2 := by
    intro e0 he0
    obtain ⟨D0, hD0P, rfl⟩ := Finset.mem_image.mp he0
    by_cases hz : (w : ℤ) = e D0 * r
    · have hsub : P.filter (fun D => e D = e D0) ⊆ {2 * N - 1} := by
        intro D hD
        obtain ⟨hDP, hDe⟩ := Finset.mem_filter.mp hD
        have hDF := (hPF D hDP).1
        have h1 := zero_forces hr1 hr2 hw (by rw [hDe]; exact hz) (he D hDP).2.1
        have h2 := (hF D hDF).2
        simp only [Finset.mem_singleton]
        omega
      exact (Finset.card_le_card hsub).trans (by simp)
    · have hTsub : (P.filter (fun D => e D = e D0)) ⊆ F := by
        intro D hD
        exact (hPF D (Finset.mem_filter.mp hD).1).1
      refine cop_card_le_two (B := N + 2) (M := (w : ℤ) - e D0 * r) (hcop.mono (by exact_mod_cast hTsub))
        (by omega) ?_ ?_ ?_ ?_
      · intro D hD
        have := (hF D (hTsub hD)).1
        omega
      · intro h
        apply hz
        linarith
      · intro D hD
        obtain ⟨hDY, hDe⟩ := Finset.mem_filter.mp hD
        have := (he D hDY).1
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
  -- move each arc to the lattice
  set σ : ℝ := 1 / ((w : ℝ) * (2 * (N : ℝ) - 1)) with hσ
  have h2N : (0 : ℝ) < 2 * (N : ℝ) - 1 := by linarith
  have hσpos : 0 < σ := by rw [hσ]; positivity
  have hρ : 1 / ((N : ℝ) * w) ≤ 2 * σ := by
    rw [hσ, div_le_iff₀ (by positivity)]
    have e1 : 2 * (1 / ((w : ℝ) * (2 * (N : ℝ) - 1))) * ((N : ℝ) * w) =
        2 * N / (2 * (N : ℝ) - 1) := by
      field_simp
    rw [e1, le_div_iff₀ h2N]
    nlinarith
  have hperD : ∀ D ∈ P, m D ≤ lam (2 * σ) (lwd N) (-(e D : ℝ) * σ) := by
    intro D hD
    have hDF := (hPF D hD).1
    have hDle := (hF D hDF).2
    have hD0 : (0 : ℝ) < D := by
      have := (hF D hDF).1
      exact_mod_cast (by omega : 0 < D)
    have hDR : (D : ℝ) ≤ 2 * N - 1 := by
      have : (D : ℝ) + 1 ≤ 2 * N := by exact_mod_cast hDle
      linarith
    have hκ : 1 ≤ (2 * (N : ℝ) - 1) / D := by rw [le_div_iff₀ hD0]; linarith
    have hpos' : (2 * (N : ℝ) - 1) / D * (-(e D : ℝ) * σ) = -(e D : ℝ) / ((w : ℝ) * D) := by
      rw [hσ]
      field_simp
    calc m D ≤ lam (1 / ((N : ℝ) * w)) (lwd N) (-(e D : ℝ) / ((w : ℝ) * D)) := (he D hD).2.2.2
      _ = lam (1 / ((N : ℝ) * w)) (lwd N) ((2 * (N : ℝ) - 1) / D * (-(e D : ℝ) * σ)) := by
          rw [hpos']
      _ ≤ lam (1 / ((N : ℝ) * w)) (lwd N) (-(e D : ℝ) * σ) := lam_scale_le hκ _ _ _
      _ ≤ lam (2 * σ) (lwd N) (-(e D : ℝ) * σ) := lam_mono_rho _ _ hρ
  have hH0 : ∀ e' : ℤ, 0 ≤ lam (2 * σ) (lwd N) (-(e' : ℝ) * σ) := fun e' => lam_nonneg _ _ _
  rw [hsumP]
  calc ∑ D ∈ P, m D ≤ ∑ D ∈ P, lam (2 * σ) (lwd N) (-(e D : ℝ) * σ) :=
        Finset.sum_le_sum hperD
    _ = ∑ e' ∈ P.image e, (P.filter (fun D => e D = e')).card • lam (2 * σ) (lwd N) (-(e' : ℝ) * σ) :=
        Finset.sum_comp (fun e' : ℤ => lam (2 * σ) (lwd N) (-(e' : ℝ) * σ)) e
    _ ≤ ∑ e' ∈ P.image e, 2 • lam (2 * σ) (lwd N) (-(e' : ℝ) * σ) := by
        apply Finset.sum_le_sum
        intro e' he'
        exact smul_le_smul_of_nonneg_right (hfib e' he') (hH0 e')
    _ = 2 * ∑ e' ∈ P.image e, lam (2 * σ) (lwd N) (-(e' : ℝ) * σ) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro e' _
        simp [nsmul_eq_mul]
    _ ≤ 2 * (8 * lwd N) := by
        have := lam_lattice_sum hσpos hd0.le (P.image e)
        linarith
    _ = 8 * (2 * lwd N) := by ring

/-- Stage B: constant 8. -/
theorem smallTot_8 (N r : ℕ) : SmallTot 8 N r := by
  intro hN hr1 hr2 w hw hsm F hF hcop a b hab
  have := small_total8 hN hr1 hr2 hw hsm F hF hcop a b hab
  exact_mod_cast this

end LinL
end Gap
end Sext6
end LRSpectrumFull

