/-
# Mathlib-upstream package: simultaneous Dirichlet approximation

Mathlib has the one-dimensional Dirichlet theorem (`Real.exists_int_int_abs_mul_sub_le`,
`Real.exists_nat_abs_mul_sub_round_le`) but NOT the simultaneous (multi-coordinate) version. This
file restates our `exists_simultaneous_nid_lt` in **Mathlib-idiomatic form** — using `round`, exactly
matching the shape of Mathlib's 1-D `exists_nat_abs_mul_sub_round_le` — so it is ready to upstream:

  `exists_simultaneous_abs_mul_sub_round_lt`:
     for `ξ : Fin k → ℝ` and `n > 0`, some `0 < q ≤ n^k` has `|ξᵢ·q − round(ξᵢ·q)| < 1/n` for all `i`.

The bridge is `Mathlib.abs_sub_round_eq_min : |x − round x| = min (fract x) (1 − fract x)`, which is
exactly our `nearestIntDist`. Axiom-clean; PR-ready (for an actual PR the proof would be inlined to
remove the `nearestIntDist` indirection). -/
import LRSpectrumFull.SimultaneousDirichlet

namespace LRSpectrumFull

open Finset

/-- **Simultaneous Dirichlet approximation (Mathlib-idiomatic, `round` form).** For reals
`ξ₀,…,ξ_{k-1}` and `n > 0`, there is an integer `q` with `0 < q ≤ n^k` such that every `ξᵢ·q` is
within `1/n` of the nearest integer: `|ξᵢ·q − round(ξᵢ·q)| < 1/n`. The multi-dimensional companion
of Mathlib's `Real.exists_nat_abs_mul_sub_round_le`. -/
theorem exists_simultaneous_abs_mul_sub_round_lt {k : ℕ} (ξ : Fin k → ℝ) {n : ℕ} (hn : 0 < n) :
    ∃ q : ℤ, 0 < q ∧ q ≤ (n : ℤ) ^ k ∧ ∀ i, |ξ i * q - round (ξ i * q)| < 1 / (n : ℝ) := by
  obtain ⟨q, hq0, hq1, hq⟩ := exists_simultaneous_nid_lt ξ hn
  refine ⟨q, hq0, hq1, fun i => ?_⟩
  have hqi := hq i
  unfold nearestIntDist at hqi
  rwa [← abs_sub_round_eq_min] at hqi

end LRSpectrumFull
