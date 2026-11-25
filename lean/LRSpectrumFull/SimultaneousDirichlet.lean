/-
# Multi-dimensional simultaneous Dirichlet approximation (geometry-of-numbers tool)

Mathlib has the one-dimensional Dirichlet theorem (`Real.exists_int_int_abs_mul_sub_le`) but NOT the
simultaneous (multi-coordinate) version. This file supplies it:

  for `v : Fin k → ℝ` and `n > 0`, there is `0 < q ≤ n^k` with `‖q·vᵢ‖ < 1/n` for all `i`,

where `‖·‖` is the distance to the nearest integer (`nearestIntDist`). Classical pigeonhole: the
`n^k + 1` sample times `0,1,…,n^k` map into the `n^k` floor-cells of `[0,1)^k`, so two collide; their
difference `q` is a simultaneous near-return. Foundational homogeneous brick of the geometry-of-
numbers route toward the Lonely Runner coordinate bound; candidate for upstreaming to Mathlib.
Axiom-clean. -/
import LRSpectrumFull.NearestInteger
import Mathlib.NumberTheory.DiophantineApproximation.Basic

namespace LRSpectrumFull

open Finset Int

/-- **Simultaneous Dirichlet approximation.** For reals `v₀,…,v_{k-1}` and `n > 0`, some integer
`q` with `0 < q ≤ n^k` simultaneously approximates: `‖q·vᵢ‖ < 1/n` for every `i`. -/
theorem exists_simultaneous_nid_lt {k : ℕ} (v : Fin k → ℝ) {n : ℕ} (hn : 0 < n) :
    ∃ q : ℤ, 0 < q ∧ q ≤ (n : ℤ) ^ k ∧ ∀ i, nearestIntDist (v i * q) < 1 / (n : ℝ) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hcelllt : ∀ (m : ℤ) (i : Fin k), ⌊(n : ℝ) * Int.fract (v i * m)⌋ < (n : ℤ) := by
    intro m i
    have h1 : (n : ℝ) * Int.fract (v i * m) < n := by
      have := Int.fract_lt_one (v i * (m : ℝ)); nlinarith
    exact Int.floor_lt.mpr (by exact_mod_cast h1)
  have hcellge : ∀ (m : ℤ) (i : Fin k), 0 ≤ ⌊(n : ℝ) * Int.fract (v i * m)⌋ :=
    fun m i => Int.floor_nonneg.mpr (mul_nonneg hnR.le (Int.fract_nonneg _))
  let g : ℤ → (Fin k → Fin n) := fun m i =>
    ⟨(⌊(n : ℝ) * Int.fract (v i * m)⌋).toNat, by
      have h1 := hcelllt m i; have h2 := hcellge m i; omega⟩
  have hcardpi : Fintype.card (Fin k → Fin n) = n ^ k := by simp [Fintype.card_pi]
  have hcard : (univ : Finset (Fin k → Fin n)).card < (Icc (0 : ℤ) ((n : ℤ) ^ k)).card := by
    rw [card_univ, hcardpi, Int.card_Icc, sub_zero,
      show ((n : ℤ) ^ k + 1) = (((n ^ k + 1 : ℕ)) : ℤ) by push_cast; ring, Int.toNat_natCast]
    omega
  obtain ⟨a, ha, b, hb, hab, hgab⟩ :=
    Finset.exists_ne_map_eq_of_card_lt_of_maps_to (t := (univ : Finset (Fin k → Fin n)))
      hcard (fun m _ => mem_univ (g m))
  obtain ⟨ha0, ha1⟩ := mem_Icc.mp ha
  obtain ⟨hb0, hb1⟩ := mem_Icc.mp hb
  -- floors agree coordinatewise (from the cell collision)
  have hfloor : ∀ i, ⌊(n : ℝ) * Int.fract (v i * a)⌋ = ⌊(n : ℝ) * Int.fract (v i * b)⌋ := by
    intro i
    have h := congrFun hgab i
    simp only [g, Fin.mk.injEq] at h
    have h1 := hcellge a i; have h2 := hcellge b i; omega
  -- the simultaneous near-return holds for q = b - a; pick the positive direction
  have hmain : ∀ c d : ℤ, (∀ i, ⌊(n : ℝ) * Int.fract (v i * c)⌋ = ⌊(n : ℝ) * Int.fract (v i * d)⌋) →
      ∀ i, nearestIntDist (v i * ((d - c : ℤ) : ℝ)) < 1 / (n : ℝ) := by
    intro c d hcd i
    have hclose : |Int.fract (v i * c) - Int.fract (v i * d)| < 1 / (n : ℝ) := by
      have hlt1 : |(n : ℝ) * Int.fract (v i * c) - (n : ℝ) * Int.fract (v i * d)| < 1 :=
        abs_sub_lt_one_of_floor_eq_floor (hcd i)
      rw [← mul_sub, abs_mul, abs_of_pos hnR] at hlt1
      rw [lt_div_iff₀ hnR]; linarith [hlt1]
    have heq : |v i * ((d - c : ℤ) : ℝ) - ((⌊v i * (d : ℝ)⌋ - ⌊v i * (c : ℝ)⌋ : ℤ) : ℝ)|
        = |Int.fract (v i * c) - Int.fract (v i * d)| := by
      have hcast : v i * ((d - c : ℤ) : ℝ) - ((⌊v i * (d : ℝ)⌋ - ⌊v i * (c : ℝ)⌋ : ℤ) : ℝ)
          = -(Int.fract (v i * c) - Int.fract (v i * d)) := by
        simp only [Int.fract]; push_cast; ring
      rw [hcast, abs_neg]
    have hle := nearestIntDist_le_dist (v i * ((d - c : ℤ) : ℝ)) (⌊v i * (d : ℝ)⌋ - ⌊v i * (c : ℝ)⌋)
    rw [heq] at hle
    exact lt_of_le_of_lt hle hclose
  rcases lt_or_gt_of_ne hab with h | h
  · exact ⟨b - a, by omega, by omega, hmain a b hfloor⟩
  · exact ⟨a - b, by omega, by omega, hmain b a (fun i => (hfloor i).symm)⟩

end LRSpectrumFull
