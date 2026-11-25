import LRSpectrumFull.Sext6.Gap.OneRL2

/-!
# One-entry deletion `B = [N] \ {r}`, part 5: the exact one-entry value with the sharper threshold  [2026-11-25]

Source: the accompanying notes on the one-entry deletion (Plan 3), Theorem V1.

* `D1Spec D r D1`, `d1Fam`, `spec_d1Fam` : `D1` is the least integer `> D` coprime to `r` (it exists).
* `one_entry_value_aux`  : `K_eq` for the base `[N] \ {r}` with the exact `L2` of `L2_delB` and the exact size
                           `L d M = 2 N`: for `D ∣ w` with `2 N ≤ w + vμ` and `vμ D ≤ Δ w`,
                           `ML ([N]_{r → w}) = 2 w / (D (w + vμ))`.
* `one_entry_value_thr`  : the same with `vμ = min (2r) (D - 2r)` and `Δ = D1 - D` if `D1 ≤ N + 2r`, `Δ = 2N + 2 - D` otherwise.
* `one_entry_value_2N2`  : every multiple `w` of `D` with `w ≥ 2 N^2` satisfies the hypotheses (threshold `2 N^2` instead of
                           the generic `2 N^3` of `one_entry_value`).
* `one_entry_value_2N2_dFam` : with `D = dFam N r`, `D1 = d1Fam D r`.
The two thresholds are `w ≥ 2N - vμ` and `w ≥ ⌈vμ D / Δ⌉` (as `vμ D ≤ Δ w`); their maximum is at most `2 N^2`.
No `sorry`, no `axiom`.

Convention: `N` is the size of the ambient interval `[N]` (`DSpec N r D`, `IsB N r v`): the deletion of `r` leaves `N - 1` distinct speeds, and `k` is not linked to `N` in the `IsB` statements (repetitions and any order are allowed). `bFam k r` lists `[N] \ {r}` and has `k + 1 = N - 1` entries when `N = k + 2`; `wFam (k+1) r w` has `k + 2 = N` entries. Speeds are the moving runners; the runner at rest is not counted, so a vector of `N` speeds means `N + 1` runners and the Lonely Runner value is `1/(N+1)`.
Hypotheses: those of the individual statements. The unproved predicates `DusartPi`, `LRCHyp`, `CopWinHyp` are not hypotheses of any statement in this module.
Axiom audit: covered by `Axioms21`.
-/

namespace LRSpectrumFull
namespace Sext6
namespace Gap

/-- `D1` is the least integer `> D` coprime to `r`. -/
structure D1Spec (D r D1 : ℕ) : Prop where
  hlt : D < D1
  hcop : Nat.Coprime D1 r
  hmin : ∀ b : ℕ, D < b → Nat.Coprime b r → D1 ≤ b

noncomputable def d1Fam (D r : ℕ) : ℕ := sInf {b : ℕ | D < b ∧ Nat.Coprime b r}

theorem spec_d1Fam {D r : ℕ} (hr : 1 ≤ r) (hcop : Nat.Coprime D r) : D1Spec D r (d1Fam D r) := by
  have hne : ({b : ℕ | D < b ∧ Nat.Coprime b r}).Nonempty :=
    ⟨D + 1 * r, by omega, (Nat.coprime_add_mul_right_left D r 1).mpr hcop⟩
  have hmem := Nat.sInf_mem hne
  exact ⟨hmem.1, hmem.2, fun b h1 h2 => Nat.sInf_le ⟨h1, h2⟩⟩

theorem one_entry_value_aux {k N r D D1 w vm : ℕ} (hk : k + 2 = N) (hS : DSpec N r D)
    (hS1 : D1Spec D r D1)
    (hV1 : ∀ p : ℝ, gap (bFam k r) p = 2 / (D : ℝ) →
      (∃ i : Fin (k + 1), ∃ n : ℤ, (vm : ℝ) ≤ (bFam k r i : ℝ) ∧
          (bFam k r i : ℝ) * p = n + 2 / (D : ℝ)) ∧
      (∃ j : Fin (k + 1), ∃ m : ℤ, (vm : ℝ) ≤ (bFam k r j : ℝ) ∧
          (bFam k r j : ℝ) * p = m - 2 / (D : ℝ)))
    (hV2 : ∃ t0 : ℝ, gap (bFam k r) t0 = 2 / (D : ℝ) ∧
      ((∀ i (m : ℤ), (bFam k r i : ℝ) * t0 = m - 2 / (D : ℝ) → (bFam k r i : ℝ) ≤ (vm : ℝ)) ∨
       (∀ i (n : ℤ), (bFam k r i : ℝ) * t0 = n + 2 / (D : ℝ) → (bFam k r i : ℝ) ≤ (vm : ℝ))))
    (hvm0 : 0 < vm) (hDw : D ∣ w) (hw1 : 2 * N ≤ w + vm)
    (hw2 : vm * D ≤ (if D1 ≤ N + 2 * r then D1 - D else 2 * N + 2 - D) * w) :
    ML (wFam (k + 1) r w) = 2 * (w : ℝ) / ((D : ℝ) * ((w : ℝ) + (vm : ℝ))) := by
  have hr := hS.hr
  have hN2 := hS.hN
  have hN3 := hS.hN3
  have hD1 := hS.hD1
  have hD1lt := hS1.hlt
  have hB := isB_bFam hk hr hN2
  have hDpos : (0 : ℝ) < D := by exact_mod_cast (by omega : 0 < D)
  have hDne : (D : ℝ) ≠ 0 := hDpos.ne'
  have hML : ML (bFam k r) = 2 / (D : ℝ) := ML_eq_two_div hS _ hB
  have hL0 : (0 : ℝ) < 2 / (D : ℝ) := div_pos (by norm_num) hDpos
  have hL1 : 2 / (D : ℝ) < 1 / 2 := by
    rw [div_lt_div_iff₀ hDpos (by norm_num)]
    have : (4 : ℝ) < D := by exact_mod_cast (by omega : 4 < D)
    linarith
  have hvpos : ∀ i, 0 < bFam k r i := fun i => by have := (hB.sub i).1; omega
  have hM : ∀ i, bFam k r i ≤ (N : ℤ) := fun i => (hB.sub i).2.1
  have hwpos' : 0 < w := by
    by_contra hw0
    have hw0' : w = 0 := by omega
    have hpos : 0 < vm * D := Nat.mul_pos hvm0 (by omega)
    rw [hw0', Nat.mul_zero] at hw2
    omega
  have hwpos : (0 : ℤ) < (w : ℤ) := by exact_mod_cast hwpos'
  have hwR0 : (0 : ℝ) < (w : ℝ) := by exact_mod_cast hwpos'
  have hvmR : (0 : ℝ) ≤ (vm : ℝ) := Nat.cast_nonneg vm
  have hWV : (0 : ℝ) < (w : ℝ) + (vm : ℝ) := by linarith
  have hWVne : (w : ℝ) + (vm : ℝ) ≠ 0 := hWV.ne'
  -- `w p ∈ ℤ` at every equality time
  obtain ⟨s, hs⟩ := hDw
  have hwR : ((w : ℤ) : ℝ) = (D : ℝ) * (s : ℝ) := by exact_mod_cast hs
  have hDw' : ∀ p, gap (bFam k r) p = 2 / (D : ℝ) → ∃ z : ℤ, ((w : ℤ) : ℝ) * p = z := by
    intro p hp
    obtain ⟨K, hK, hpK⟩ := eqtime_classify hS _ hB p hp
    have e1 : ((w : ℤ) : ℝ) * ((K : ℝ) / D) = (s : ℝ) * K := by
      rw [hwR]
      calc (D : ℝ) * s * (K / D) = s * K * ((D : ℝ) / D) := by ring
        _ = s * K := by rw [div_self hDne, mul_one]
    rcases hpK with h | h
    · refine ⟨(s : ℤ) * K, ?_⟩
      rw [h, e1]
      norm_cast
    · refine ⟨-((s : ℤ) * K), ?_⟩
      have e2 : ((w : ℤ) : ℝ) * (-((K : ℝ) / D)) = -(((w : ℤ) : ℝ) * ((K : ℝ) / D)) := by ring
      rw [h, e2, e1]
      norm_cast
  -- the equality time as `a / D`
  obtain ⟨t0, ht0, hext0⟩ := hV2
  obtain ⟨K, hK, hpK⟩ := eqtime_classify hS _ hB t0 ht0
  obtain ⟨a, ha⟩ : ∃ a : ℤ, t0 = (a : ℝ) / D := by
    rcases hpK with h | h
    · exact ⟨K, h⟩
    · exact ⟨-K, by rw [h]; push_cast; ring⟩
  subst ha
  have key := K_eq (bFam k r) hvpos (N : ℤ) hM (w : ℤ) hwpos (2 / (D : ℝ)) (vm : ℝ)
    (if D1 ≤ N + 2 * r then 2 / (D1 : ℝ) else 1 / ((N : ℝ) + 1)) hML.symm hL0 hL1
    (by exact_mod_cast hvm0) hV1
    (fun p hp hlt => L2_delB hS hS1.hlt hS1.hmin (bFam k r) hB p hp hlt) hDw' D (by omega) a 2
    (by simp) ht0 hext0
    (by
      have e : (2 / (D : ℝ)) * (D : ℝ) = 2 := by field_simp
      rw [e]
      have h2 : (2 * N : ℝ) ≤ (w : ℝ) + (vm : ℝ) := by exact_mod_cast hw1
      push_cast
      linarith)
    (by
      have hwR' : ((w : ℤ) : ℝ) = (w : ℝ) := by norm_cast
      rw [hwR']
      have e1 : (w : ℝ) * (2 / (D : ℝ)) / ((w : ℝ) + (vm : ℝ)) =
          2 * (w : ℝ) / ((D : ℝ) * ((w : ℝ) + (vm : ℝ))) := by
        field_simp
      rw [e1]
      have hDWV : (0 : ℝ) < (D : ℝ) * ((w : ℝ) + (vm : ℝ)) := mul_pos hDpos hWV
      split_ifs with h
      · have hD1R : (0 : ℝ) < D1 := by exact_mod_cast (by omega : 0 < D1)
        rw [div_le_div_iff₀ hD1R hDWV]
        have h6 : vm * D ≤ (D1 - D) * w := by rw [if_pos h] at hw2; exact hw2
        have h7 : ((vm * D : ℕ) : ℝ) ≤ (((D1 - D) * w : ℕ) : ℝ) := by exact_mod_cast h6
        rw [Nat.cast_mul, Nat.cast_mul, Nat.cast_sub (show D ≤ D1 by omega)] at h7
        nlinarith
      · have hN1 : (0 : ℝ) < (N : ℝ) + 1 := by positivity
        rw [div_le_div_iff₀ hN1 hDWV]
        have h6 : vm * D ≤ (2 * N + 2 - D) * w := by rw [if_neg h] at hw2; exact hw2
        have h7 : ((vm * D : ℕ) : ℝ) ≤ (((2 * N + 2 - D) * w : ℕ) : ℝ) := by exact_mod_cast h6
        rw [Nat.cast_mul, Nat.cast_mul,
          Nat.cast_sub (show D ≤ 2 * N + 2 by have := hS.le_two_N; omega)] at h7
        push_cast at h7
        nlinarith)
  have hcong := ML_wFam_eq_snoc (w := w) hk hr hN2
  rw [hcong, key]
  have hwR' : ((w : ℤ) : ℝ) = (w : ℝ) := by norm_cast
  rw [hwR']
  field_simp

/-- **Exact one-entry value, Theorem V1 of the notes.**  `D1` the least integer `> D` coprime to `r`,
`vμ = min (2r) (D - 2r)`, `Δ = D1 - D` if `D1 ≤ N + 2r`, `Δ = 2N + 2 - D` otherwise.  For `D ∣ w` with
`w ≥ 2N - vμ` and `vμ D ≤ Δ w`: `ML ([N]_{r → w}) = 2 w / (D (w + vμ))`. -/
theorem one_entry_value_thr {k N r D D1 w : ℕ} (hk : k + 2 = N) (hS : DSpec N r D)
    (hS1 : D1Spec D r D1) (hDw : D ∣ w) (hw1 : 2 * N ≤ w + min (2 * r) (D - 2 * r))
    (hw2 : min (2 * r) (D - 2 * r) * D ≤
      (if D1 ≤ N + 2 * r then D1 - D else 2 * N + 2 - D) * w) :
    ML (wFam (k + 1) r w) =
      2 * (w : ℝ) / ((D : ℝ) * ((w : ℝ) + ((min (2 * r) (D - 2 * r) : ℕ) : ℝ))) := by
  have hB := isB_bFam hk hS.hr hS.hN
  have hD1 := hS.hD1
  have hN2 := hS.hN
  have hr := hS.hr
  exact one_entry_value_aux hk hS hS1 (fun p hp => V1_holds hS (bFam k r) hB p hp)
    (V2_holds hS (bFam k r) hB) (by omega) hDw hw1 hw2

/-- **Exact one-entry value for `w ≥ 2 N^2`** (every multiple of `D`). -/
theorem one_entry_value_2N2 {k N r D D1 w : ℕ} (hk : k + 2 = N) (hS : DSpec N r D)
    (hS1 : D1Spec D r D1) (hDw : D ∣ w) (hw : 2 * N ^ 2 ≤ w) :
    ML (wFam (k + 1) r w) =
      2 * (w : ℝ) / ((D : ℝ) * ((w : ℝ) + ((min (2 * r) (D - 2 * r) : ℕ) : ℝ))) := by
  have hr := hS.hr
  have hN2 := hS.hN
  have hN3 := hS.hN3
  have hD1 := hS.hD1
  have hD2 : D ≤ 2 * N := hS.le_two_N
  apply one_entry_value_thr hk hS hS1 hDw
  · have : 2 * N ≤ 2 * N ^ 2 := by nlinarith
    omega
  · have hm : min (2 * r) (D - 2 * r) ≤ N := by omega
    have hmD : min (2 * r) (D - 2 * r) * D ≤ N * (2 * N) := Nat.mul_le_mul hm hD2
    have hΔ : 1 ≤ (if D1 ≤ N + 2 * r then D1 - D else 2 * N + 2 - D) := by
      have := hS1.hlt
      split_ifs <;> omega
    have h1 : 1 * w ≤ (if D1 ≤ N + 2 * r then D1 - D else 2 * N + 2 - D) * w :=
      Nat.mul_le_mul hΔ (le_refl w)
    rw [one_mul] at h1
    have h2 : N * (2 * N) = 2 * N ^ 2 := by ring
    exact le_trans hmD (le_trans (le_of_eq h2) (le_trans hw h1))

/-- The same with `D = dFam N r` and `D1 = d1Fam D r`. -/
theorem one_entry_value_2N2_dFam {k N r w : ℕ} (hk : k + 2 = N) (hN3 : 3 ≤ N) (hr : 1 ≤ r)
    (hrN : 2 * r ≤ N) (hDw : dFam N r ∣ w) (hw : 2 * N ^ 2 ≤ w) :
    ML (wFam (k + 1) r w) =
      2 * (w : ℝ) / ((dFam N r : ℝ) *
        ((w : ℝ) + ((min (2 * r) (dFam N r - 2 * r) : ℕ) : ℝ))) :=
  one_entry_value_2N2 hk (spec_dFam hr hrN hN3)
    (spec_d1Fam hr (spec_dFam hr hrN hN3).hcop) hDw hw

end Gap
end Sext6
end LRSpectrumFull
