import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Data.Int.Interval
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import LRSpectrumFull.NearestIntLipschitz

/-!
# Q8.1, Theorem C, Case II: the counting lemma (existence of a good offset `η`)  [2026-11-25]

Source: the accompanying notes on Zhang's Question 8.1 section 3, Lemma 3 (measure bound).
Pure real analysis, no speed vectors:

* `vol_le_sum_len`   : a set covered by finitely many open intervals has volume at most the sum of lengths.
* `bad_set_one_vol`  : `{x ∈ (0,E] : ‖a x‖ < τ}` has volume at most `τ/a + (a E + τ)(2τ/a)`.
* `bad_set_two_vol`  : `{x ∈ (0,E] : ‖x0 - α x‖ < τ}` has volume at most `(α E + 2τ + 1)(2τ/α)`.
* `good_eta_exists`  : if the two bounds sum to less than `E`, some `η ∈ (0,E]` has `τ ≤ ‖a η‖` and
  `τ ≤ ‖x0 - α η‖`.
No `sorry`, no `axiom`.

Convention: No speed vector is involved in this module (number theory or real analysis); `N` denotes a natural number, the size of the ambient interval `[1,N]`.
Hypotheses: those of the individual statements (numerical bounds, structural conditions and, where named in the list above, window predicates such as `PrimeWin`, `CopWin`, `PrimeWindow7`, which later modules discharge for explicit ranges). The unproved predicates `DusartPi`, `LRCHyp`, `CopWinHyp` are not hypotheses of any statement in this module.
Axiom audit: covered by `Axioms8` (`#print axioms`; declarations not printed there are bricks of printed ones, so their axioms are bounded by the printed lines).
-/

namespace LRSpectrumFull
namespace Sext6
namespace Gap

open MeasureTheory

/-- A set inside a finite union of open intervals has volume at most the sum of their lengths. -/
theorem vol_le_sum_len {ι : Type*} (s : Finset ι) (l u : ι → ℝ) (hlu : ∀ i ∈ s, l i ≤ u i)
    (B : Set ℝ) (hB : B ⊆ ⋃ i ∈ s, Set.Ioo (l i) (u i)) :
    volume B ≤ ENNReal.ofReal (∑ i ∈ s, (u i - l i)) := by
  calc volume B ≤ volume (⋃ i ∈ s, Set.Ioo (l i) (u i)) := measure_mono hB
    _ ≤ ∑ i ∈ s, volume (Set.Ioo (l i) (u i)) := measure_biUnion_finset_le s _
    _ = ∑ i ∈ s, ENNReal.ofReal (u i - l i) := by
        refine Finset.sum_congr rfl (fun i _ => ?_)
        exact Real.volume_Ioo
    _ = ENNReal.ofReal (∑ i ∈ s, (u i - l i)) :=
        (ENNReal.ofReal_sum_of_nonneg (fun i hi => sub_nonneg.mpr (hlu i hi))).symm

/-- First bad set: the times where the multiple-of-the-modulus speed `a` is close to an integer. -/
theorem bad_set_one_vol {τ E a : ℝ} (hτ0 : 0 < τ) (hτ1 : τ ≤ 1) (hE : 0 < E) (ha : 0 < a) :
    volume {x : ℝ | x ∈ Set.Ioc 0 E ∧ nearestIntDist (a * x) < τ} ≤
      ENNReal.ofReal (τ / a + (a * E + τ) * (2 * τ / a)) := by
  have hKnn : 0 ≤ a * E + τ := by positivity
  set K : ℕ := ⌊a * E + τ⌋₊ with hK
  have hKle : (K : ℝ) ≤ a * E + τ := Nat.floor_le hKnn
  let l : ℕ → ℝ := fun k => if k = 0 then 0 else ((k : ℝ) - τ) / a
  let u : ℕ → ℝ := fun k => ((k : ℝ) + τ) / a
  have hsub : {x : ℝ | x ∈ Set.Ioc 0 E ∧ nearestIntDist (a * x) < τ} ⊆
      ⋃ k ∈ Finset.range (K + 1), Set.Ioo (l k) (u k) := by
    intro x hx
    obtain ⟨⟨hx0, hxE⟩, hx2⟩ := hx
    obtain ⟨n, hn⟩ := nearestIntDist_eq_abs (a * x)
    rw [hn] at hx2
    obtain ⟨hab1, hab2⟩ := abs_lt.mp hx2
    have hax0 : 0 < a * x := mul_pos ha hx0
    have haxE : a * x ≤ a * E := mul_le_mul_of_nonneg_left hxE ha.le
    have hnR : (-1 : ℝ) < (n : ℝ) := by linarith
    have hn1 : (-1 : ℤ) < n := by exact_mod_cast hnR
    have hn0 : 0 ≤ n := by omega
    obtain ⟨k, hk⟩ : ∃ k : ℕ, (k : ℝ) = (n : ℝ) :=
      ⟨n.toNat, by exact_mod_cast Int.toNat_of_nonneg hn0⟩
    have hkK : k ≤ K := by
      apply Nat.le_floor
      rw [hk]
      linarith
    rw [Set.mem_iUnion₂]
    refine ⟨k, Finset.mem_range.mpr (Nat.lt_succ_of_le hkK), ?_⟩
    by_cases hk0 : k = 0
    · have hl : l k = 0 := by simp [l, hk0]
      have hu : u k = ((k : ℝ) + τ) / a := rfl
      rw [hl, hu]
      refine ⟨hx0, ?_⟩
      rw [lt_div_iff₀ ha]
      linarith
    · have hl : l k = ((k : ℝ) - τ) / a := by simp [l, hk0]
      have hu : u k = ((k : ℝ) + τ) / a := rfl
      rw [hl, hu]
      constructor
      · rw [div_lt_iff₀ ha]
        linarith
      · rw [lt_div_iff₀ ha]
        linarith
  have hsum : ∑ k ∈ Finset.range (K + 1), (u k - l k) = (K : ℝ) * (2 * τ / a) + τ / a := by
    rw [Finset.sum_range_succ']
    have h1 : ∀ i ∈ Finset.range K, u (i + 1) - l (i + 1) = 2 * τ / a := by
      intro i _
      have hne : i + 1 ≠ 0 := Nat.succ_ne_zero i
      simp only [u, l, hne, if_false]
      push_cast
      ring
    rw [Finset.sum_congr rfl h1, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    have h0 : u 0 - l 0 = τ / a := by simp [u, l]
    rw [h0]
  have hbound : ∑ k ∈ Finset.range (K + 1), (u k - l k) ≤ τ / a + (a * E + τ) * (2 * τ / a) := by
    rw [hsum]
    have : (K : ℝ) * (2 * τ / a) ≤ (a * E + τ) * (2 * τ / a) :=
      mul_le_mul_of_nonneg_right hKle (by positivity)
    linarith
  have hlu : ∀ k ∈ Finset.range (K + 1), l k ≤ u k := by
    intro k _
    by_cases hk0 : k = 0
    · have hl : l k = 0 := by simp [l, hk0]
      rw [hl]
      exact div_nonneg (by positivity) ha.le
    · have hl : l k = ((k : ℝ) - τ) / a := by simp [l, hk0]
      rw [hl]
      exact div_le_div_of_nonneg_right (by linarith) ha.le
  exact (vol_le_sum_len _ l u hlu _ hsub).trans (ENNReal.ofReal_le_ofReal hbound)

/-- Second bad set: the times where the blocker-multiple speed is close to an integer. -/
theorem bad_set_two_vol {τ E α x0 : ℝ} (hτ0 : 0 < τ) (hE : 0 < E) (hα : 0 < α) :
    volume {x : ℝ | x ∈ Set.Ioc 0 E ∧ nearestIntDist (x0 - α * x) < τ} ≤
      ENNReal.ofReal ((α * E + 2 * τ + 1) * (2 * τ / α)) := by
  let lo : ℤ := ⌈x0 - α * E - τ⌉
  let hi : ℤ := ⌊x0 + τ⌋
  let l : ℤ → ℝ := fun n => (x0 - (n : ℝ) - τ) / α
  let u : ℤ → ℝ := fun n => (x0 - (n : ℝ) + τ) / α
  have hsub : {x : ℝ | x ∈ Set.Ioc 0 E ∧ nearestIntDist (x0 - α * x) < τ} ⊆
      ⋃ n ∈ Finset.Icc lo hi, Set.Ioo (l n) (u n) := by
    intro x hx
    obtain ⟨⟨hx0, hxE⟩, hx2⟩ := hx
    obtain ⟨n, hn⟩ := nearestIntDist_eq_abs (x0 - α * x)
    rw [hn] at hx2
    obtain ⟨hab1, hab2⟩ := abs_lt.mp hx2
    have hax0 : 0 < α * x := mul_pos hα hx0
    have haxE : α * x ≤ α * E := mul_le_mul_of_nonneg_left hxE hα.le
    rw [Set.mem_iUnion₂]
    refine ⟨n, ?_, ?_⟩
    · rw [Finset.mem_Icc]
      constructor
      · apply Int.ceil_le.mpr
        linarith
      · apply Int.le_floor.mpr
        linarith
    · show l n < x ∧ x < u n
      constructor
      · show (x0 - (n : ℝ) - τ) / α < x
        rw [div_lt_iff₀ hα]
        linarith
      · show x < (x0 - (n : ℝ) + τ) / α
        rw [lt_div_iff₀ hα]
        linarith
  have hlu : ∀ n ∈ Finset.Icc lo hi, l n ≤ u n := by
    intro n _
    show (x0 - (n : ℝ) - τ) / α ≤ (x0 - (n : ℝ) + τ) / α
    exact div_le_div_of_nonneg_right (by linarith) hα.le
  have hlen : ∀ n : ℤ, u n - l n = 2 * τ / α := by
    intro n
    show (x0 - (n : ℝ) + τ) / α - (x0 - (n : ℝ) - τ) / α = 2 * τ / α
    ring
  have hsum : ∑ n ∈ Finset.Icc lo hi, (u n - l n) =
      ((Finset.Icc lo hi).card : ℝ) * (2 * τ / α) := by
    rw [Finset.sum_congr rfl (fun n _ => hlen n), Finset.sum_const, nsmul_eq_mul]
  have hcard : (((Finset.Icc lo hi).card : ℕ) : ℝ) ≤ α * E + 2 * τ + 1 := by
    have hfl : ((hi : ℤ) : ℝ) ≤ x0 + τ := Int.floor_le (x0 + τ)
    have hce : x0 - α * E - τ ≤ ((lo : ℤ) : ℝ) := Int.le_ceil (x0 - α * E - τ)
    rw [Int.card_Icc]
    by_cases hz : 0 ≤ hi + 1 - lo
    · have h1 : (((hi + 1 - lo).toNat : ℕ) : ℤ) = hi + 1 - lo := Int.toNat_of_nonneg hz
      have h2 : (((hi + 1 - lo).toNat : ℕ) : ℝ) = (hi : ℝ) + 1 - (lo : ℝ) := by
        have h3 : ((((hi + 1 - lo).toNat : ℕ) : ℤ) : ℝ) = ((hi + 1 - lo : ℤ) : ℝ) := by
          rw [h1]
        push_cast at h3
        exact h3
      rw [h2]
      linarith
    · have h1 : (hi + 1 - lo).toNat = 0 := Int.toNat_of_nonpos (by omega)
      rw [h1]
      have : 0 ≤ α * E := by positivity
      simp only [Nat.cast_zero]
      linarith
  have hbound : ∑ n ∈ Finset.Icc lo hi, (u n - l n) ≤ (α * E + 2 * τ + 1) * (2 * τ / α) := by
    rw [hsum]
    have h0 : (0 : ℝ) ≤ 2 * τ / α := by positivity
    exact mul_le_mul_of_nonneg_right hcard h0
  exact (vol_le_sum_len _ l u hlu _ hsub).trans (ENNReal.ofReal_le_ofReal hbound)

/-- **Good offset.**  If the two bad-set bounds add up to less than `E`, some `η ∈ (0,E]` avoids both. -/
theorem good_eta_exists {τ E a α x0 : ℝ} (hτ0 : 0 < τ) (hτ1 : τ ≤ 1) (hE : 0 < E) (ha : 0 < a)
    (hα : 0 < α)
    (hfin : τ / a + (a * E + τ) * (2 * τ / a) + (α * E + 2 * τ + 1) * (2 * τ / α) < E) :
    ∃ η : ℝ, 0 < η ∧ η ≤ E ∧ τ ≤ nearestIntDist (a * η) ∧ τ ≤ nearestIntDist (x0 - α * η) := by
  by_contra hcon
  push Not at hcon
  have hsub : Set.Ioc (0 : ℝ) E ⊆
      {x : ℝ | x ∈ Set.Ioc 0 E ∧ nearestIntDist (a * x) < τ} ∪
      {x : ℝ | x ∈ Set.Ioc 0 E ∧ nearestIntDist (x0 - α * x) < τ} := by
    intro x hx
    by_cases h1 : nearestIntDist (a * x) < τ
    · exact Or.inl ⟨hx, h1⟩
    · exact Or.inr ⟨hx, hcon x hx.1 hx.2 (not_lt.mp h1)⟩
  have h1 := bad_set_one_vol (E := E) (a := a) hτ0 hτ1 hE ha
  have h2 := bad_set_two_vol (E := E) (α := α) (x0 := x0) hτ0 hE hα
  have hb1 : 0 ≤ τ / a + (a * E + τ) * (2 * τ / a) := by positivity
  have hb2 : 0 ≤ (α * E + 2 * τ + 1) * (2 * τ / α) := by positivity
  have hvol : volume (Set.Ioc (0 : ℝ) E) ≤
      ENNReal.ofReal (τ / a + (a * E + τ) * (2 * τ / a)) +
        ENNReal.ofReal ((α * E + 2 * τ + 1) * (2 * τ / α)) :=
    (measure_mono hsub).trans ((measure_union_le _ _).trans (add_le_add h1 h2))
  rw [Real.volume_Ioc, sub_zero, ← ENNReal.ofReal_add hb1 hb2] at hvol
  have := (ENNReal.ofReal_le_ofReal_iff (add_nonneg hb1 hb2)).mp hvol
  linarith

end Gap
end Sext6
end LRSpectrumFull
