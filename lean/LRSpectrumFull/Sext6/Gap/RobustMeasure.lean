import LRSpectrumFull.NearestIntLipschitz
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Data.Int.Interval
import Mathlib.Tactic

/-!
# Theorem S: the large speeds (Lemma M)  [2026-11-25]

Source: the accompanying notes on Theorem S (Lemma M and the last paragraph of section 3).

* `measure_bad_le`   : for integers `N ≥ 2`, `u ≥ 1` and `a ≤ b`, the set of `t ∈ [a,b]` with
                       `‖u t‖ < 1/N` has Lebesgue measure at most `2 (b-a)/N + 4/(N u)`.
* `exists_good_point`: if the sum of these bounds over a finite set `U` of speeds is `< b - a`, some
                       `t ∈ [a,b]` has `‖u t‖ ≥ 1/N` for every `u ∈ U`.

Design note.  The bad set of `u` is covered by the open intervals `((c - 1/N)/u, (c + 1/N)/u)` with
`c` in the integer interval `[⌈u a - 1/N⌉, ⌊u b + 1/N⌋]`; only `measure_biUnion_finset_le` and
`Real.volume_Ioo` are used (no integrals, no a.e. statements).
No `sorry`, no `axiom`.

Convention: No speed vector is involved in this module (number theory or real analysis); `N` denotes a natural number, the size of the ambient interval `[1,N]`.
Hypotheses: those of the individual statements (numerical bounds, structural conditions and, where named in the list above, window predicates such as `PrimeWin`, `CopWin`, `PrimeWindow7`, which later modules discharge for explicit ranges). The unproved predicates `DusartPi`, `LRCHyp`, `CopWinHyp` are not hypotheses of any statement in this module.
Axiom audit: covered by `Axioms7` (first); every later audit module imports this module (`#print axioms`; declarations not printed there are bricks of printed ones, so their axioms are bounded by the printed lines).
-/

namespace LRSpectrumFull
namespace Sext6
namespace Gap

open MeasureTheory

/-- The bad set of the speed `u` on `[a,b]` is covered by `≤ u(b-a) + 2` thin intervals. -/
theorem bad_subset (a b : ℝ) (N u : ℕ) (hN : 2 ≤ N) (hu : 1 ≤ u) :
    {t : ℝ | t ∈ Set.Icc a b ∧ nearestIntDist ((u : ℝ) * t) < 1 / (N : ℝ)} ⊆
      ⋃ c ∈ Finset.Icc ⌈(u : ℝ) * a - 1 / (N : ℝ)⌉ ⌊(u : ℝ) * b + 1 / (N : ℝ)⌋,
        Set.Ioo (((c : ℝ) - 1 / (N : ℝ)) / u) (((c : ℝ) + 1 / (N : ℝ)) / u) := by
  intro t ht
  obtain ⟨⟨hat, htb⟩, hlt⟩ := ht
  have huR : (0 : ℝ) < u := by exact_mod_cast hu
  obtain ⟨n, hn⟩ := nearestIntDist_eq_abs ((u : ℝ) * t)
  rw [hn] at hlt
  obtain ⟨hlo, hhi⟩ := abs_lt.mp hlt
  have h1 : (u : ℝ) * a ≤ (u : ℝ) * t := mul_le_mul_of_nonneg_left hat huR.le
  have h2 : (u : ℝ) * t ≤ (u : ℝ) * b := mul_le_mul_of_nonneg_left htb huR.le
  simp only [Set.mem_iUnion, Finset.mem_Icc]
  refine ⟨n, ⟨?_, ?_⟩, ?_, ?_⟩
  · exact Int.ceil_le.mpr (by linarith)
  · exact Int.le_floor.mpr (by linarith)
  · rw [div_lt_iff₀ huR]; linarith
  · rw [lt_div_iff₀ huR]; linarith

/-- Number of integers in `[⌈x⌉, ⌊y⌋]` is at most `y - x + 1` (for `x ≤ y + 1`). -/
theorem card_Icc_ceil_floor_le (x y : ℝ) (hxy : 0 ≤ y - x + 1) :
    (((Finset.Icc ⌈x⌉ ⌊y⌋).card : ℕ) : ℝ) ≤ y - x + 1 := by
  rw [Int.card_Icc]
  by_cases h : 0 ≤ ⌊y⌋ + 1 - ⌈x⌉
  · have h1 : (((⌊y⌋ + 1 - ⌈x⌉).toNat : ℕ) : ℤ) = ⌊y⌋ + 1 - ⌈x⌉ := Int.toNat_of_nonneg h
    have h2 : (((⌊y⌋ + 1 - ⌈x⌉).toNat : ℕ) : ℝ) = ((⌊y⌋ : ℤ) : ℝ) + 1 - ((⌈x⌉ : ℤ) : ℝ) := by
      have h5 := congrArg (Int.cast : ℤ → ℝ) h1
      push_cast at h5
      linarith
    rw [h2]
    have h3 := Int.floor_le y
    have h4 := Int.le_ceil x
    linarith
  · have h1 : (⌊y⌋ + 1 - ⌈x⌉).toNat = 0 := Int.toNat_of_nonpos (by omega)
    rw [h1]
    simpa using hxy

/-- **Lemma M.** The bad set of `u` on `[a, b]` has measure `≤ 2 (b-a)/N + 4/(N u)`. -/
theorem measure_bad_le (a b : ℝ) (hab : a ≤ b) (N u : ℕ) (hN : 2 ≤ N) (hu : 1 ≤ u) :
    volume {t : ℝ | t ∈ Set.Icc a b ∧ nearestIntDist ((u : ℝ) * t) < 1 / (N : ℝ)} ≤
      ENNReal.ofReal (2 * (b - a) / N + 4 / (N * u)) := by
  have huR : (0 : ℝ) < u := by exact_mod_cast hu
  have hNR : (2 : ℝ) ≤ N := by exact_mod_cast hN
  have hNpos : (0 : ℝ) < N := by linarith
  have hNne : (N : ℝ) ≠ 0 := hNpos.ne'
  have hune : (u : ℝ) ≠ 0 := huR.ne'
  set I := Finset.Icc ⌈(u : ℝ) * a - 1 / (N : ℝ)⌉ ⌊(u : ℝ) * b + 1 / (N : ℝ)⌋ with hI
  have hlen : ∀ c : ℤ, volume (Set.Ioo (((c : ℝ) - 1 / (N : ℝ)) / u) (((c : ℝ) + 1 / (N : ℝ)) / u)) =
      ENNReal.ofReal (2 / (N * u)) := by
    intro c
    rw [Real.volume_Ioo]
    congr 1
    first
      | (field_simp; done)
      | (field_simp; ring)
  have h1 := measure_mono (μ := volume) (bad_subset a b N u hN hu)
  have h2 := measure_biUnion_finset_le (μ := volume) I
    (fun c : ℤ => Set.Ioo (((c : ℝ) - 1 / (N : ℝ)) / u) (((c : ℝ) + 1 / (N : ℝ)) / u))
  have h3 : ∑ c ∈ I, volume (Set.Ioo (((c : ℝ) - 1 / (N : ℝ)) / u) (((c : ℝ) + 1 / (N : ℝ)) / u)) =
      ENNReal.ofReal ((I.card : ℝ) * (2 / (N * u))) := by
    simp only [hlen, Finset.sum_const, nsmul_eq_mul]
    rw [ENNReal.ofReal_mul (p := (I.card : ℝ)) (Nat.cast_nonneg _), ENNReal.ofReal_natCast]
  have hcard : (I.card : ℝ) ≤ (u : ℝ) * (b - a) + 2 := by
    have := card_Icc_ceil_floor_le ((u : ℝ) * a - 1 / (N : ℝ)) ((u : ℝ) * b + 1 / (N : ℝ)) (by
      have : (0 : ℝ) ≤ (u : ℝ) * (b - a) := mul_nonneg huR.le (by linarith)
      have h5 : 1 / (N : ℝ) ≤ 1 := by
        rw [div_le_one hNpos]; linarith
      have h6 : 0 ≤ 1 / (N : ℝ) := by positivity
      linarith)
    have h5 : 1 / (N : ℝ) ≤ 1 / 2 := one_div_le_one_div_of_le (by norm_num) hNR
    rw [hI]
    linarith
  have hq : (0 : ℝ) ≤ 2 / (N * u) := by positivity
  have h4 : (I.card : ℝ) * (2 / (N * u)) ≤ 2 * (b - a) / N + 4 / (N * u) := by
    calc (I.card : ℝ) * (2 / (N * u)) ≤ ((u : ℝ) * (b - a) + 2) * (2 / (N * u)) :=
          mul_le_mul_of_nonneg_right hcard hq
      _ = 2 * (b - a) / N + 4 / (N * u) := by
          first
            | (field_simp; done)
            | (field_simp; ring)
  calc volume {t : ℝ | t ∈ Set.Icc a b ∧ nearestIntDist ((u : ℝ) * t) < 1 / (N : ℝ)}
      ≤ volume (⋃ c ∈ I, Set.Ioo (((c : ℝ) - 1 / (N : ℝ)) / u) (((c : ℝ) + 1 / (N : ℝ)) / u)) := h1
    _ ≤ ∑ c ∈ I, volume (Set.Ioo (((c : ℝ) - 1 / (N : ℝ)) / u) (((c : ℝ) + 1 / (N : ℝ)) / u)) := h2
    _ = ENNReal.ofReal ((I.card : ℝ) * (2 / (N * u))) := h3
    _ ≤ ENNReal.ofReal (2 * (b - a) / N + 4 / (N * u)) := ENNReal.ofReal_le_ofReal h4

/-- **Counting/measure step for the large speeds.**  If `Σ_{u ∈ U} (2 (b-a)/N + 4/(N u)) < b - a`
there is `t ∈ [a, b]` with `‖u t‖ ≥ 1/N` for every `u ∈ U`. -/
theorem exists_good_point (a b : ℝ) (hab : a < b) (N : ℕ) (hN : 2 ≤ N) (U : Finset ℕ)
    (hU : ∀ u ∈ U, 1 ≤ u)
    (hsum : ∑ u ∈ U, (2 * (b - a) / N + 4 / (N * (u : ℝ))) < b - a) :
    ∃ t ∈ Set.Icc a b, ∀ u ∈ U, 1 / (N : ℝ) ≤ nearestIntDist ((u : ℝ) * t) := by
  by_contra hcon
  push Not at hcon
  have hNR : (2 : ℝ) ≤ N := by exact_mod_cast hN
  have hNpos : (0 : ℝ) < N := by linarith
  have hcover : Set.Icc a b ⊆ ⋃ u ∈ U,
      {t : ℝ | t ∈ Set.Icc a b ∧ nearestIntDist ((u : ℝ) * t) < 1 / (N : ℝ)} := by
    intro t ht
    obtain ⟨u, hu, hlt⟩ := hcon t ht
    simp only [Set.mem_iUnion]
    exact ⟨u, hu, ht, hlt⟩
  have h1 : volume (Set.Icc a b) ≤ ∑ u ∈ U,
      volume {t : ℝ | t ∈ Set.Icc a b ∧ nearestIntDist ((u : ℝ) * t) < 1 / (N : ℝ)} :=
    (measure_mono hcover).trans (measure_biUnion_finset_le U _)
  have h2 : ∑ u ∈ U, volume {t : ℝ | t ∈ Set.Icc a b ∧ nearestIntDist ((u : ℝ) * t) < 1 / (N : ℝ)} ≤
      ∑ u ∈ U, ENNReal.ofReal (2 * (b - a) / N + 4 / (N * (u : ℝ))) :=
    Finset.sum_le_sum (fun u hu => measure_bad_le a b hab.le N u hN (hU u hu))
  have hnn : ∀ u ∈ U, 0 ≤ 2 * (b - a) / (N : ℝ) + 4 / ((N : ℝ) * (u : ℝ)) := by
    intro u hu
    have h5 : 0 ≤ 2 * (b - a) / (N : ℝ) := by
      apply div_nonneg <;> linarith
    have h6 : 0 ≤ 4 / ((N : ℝ) * (u : ℝ)) := by positivity
    linarith
  rw [Real.volume_Icc] at h1
  rw [← ENNReal.ofReal_sum_of_nonneg hnn] at h2
  have h3 := h1.trans h2
  have hsnn : 0 ≤ ∑ u ∈ U, (2 * (b - a) / (N : ℝ) + 4 / ((N : ℝ) * (u : ℝ))) :=
    Finset.sum_nonneg hnn
  have h4 := (ENNReal.ofReal_le_ofReal_iff hsnn).mp h3
  linarith

end Gap
end Sext6
end LRSpectrumFull
