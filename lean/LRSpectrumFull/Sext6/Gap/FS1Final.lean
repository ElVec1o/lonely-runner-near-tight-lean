import LRSpectrumFull.Sext6.Gap.FS1
import LRSpectrumFull.Sext6.Gap.FinalCore

/-!
# Theorem FS1, ALL `N ≥ 14`, no hypothesis  [2026-11-25]

`FS1_of_OE` (FS1.lean) takes the one-entry lower bound OE-low as a hypothesis.  `FinalCore.OE_low_unconditional` is
OE-low for every `N ≥ 14` (sieve blocks below `10^5`, Chebyshev's 30-combination above), so plugging it in gives
Theorem FS1 for every `N ≥ 14` with no `DusartPi` argument.

* `FS1_unconditional`       : Theorem FS1 (branches A, B1, B2), `N ≥ 14`.
* `FS1_shape_unconditional` : Fan-Sun shape `ML ≥ 1/N` or `ML = σ/(σ N + κ)`, `1 ≤ κ`, `2 κ ≤ N`.
No `sorry`, no `axiom`.

Convention: `N = k + 1` is the number of speeds of the vector `v : Fin (k+1) → ℤ`. Speeds are the moving runners; the runner at rest is not counted, so a vector of `N` speeds means `N + 1` runners and the Lonely Runner value is `1/(N+1)`.
Hypotheses: No hypothesis predicate occurs; the hypotheses are `k + 1 = N`, `14 ≤ N`, `1 ≤ r ≤ N`, `N < w`.
Axiom audit: covered by `Axioms16` (`#print axioms`; declarations not printed there are bricks of printed ones, so their axioms are bounded by the printed lines).
-/

namespace LRSpectrumFull
namespace Sext6
namespace Gap

/-- **Theorem FS1, all `N ≥ 14`, no hypothesis.** -/
theorem FS1_unconditional {k N r w : ℕ} (hk : k + 1 = N) (hN : 14 ≤ N)
    (hr1 : 1 ≤ r) (hrN : r ≤ N) (hw : N < w) :
    1 / (N : ℝ) ≤ ML (wFam k r w) ∨
    (N < 2 * r ∧ ∃ m : ℕ, 2 ≤ m ∧ w = m * r ∧
      (ML (wFam k r w) = 1 / ((N : ℝ) + 1) ∨
       ∃ κ : ℕ, 1 ≤ κ ∧ 2 * κ ≤ N ∧ ML (wFam k r w) = (m : ℝ) / ((m * N + κ : ℕ) : ℝ))) :=
  FS1_of_OE hk hN (fun _ _ h1 h2 h3 => OE_low_unconditional hk hN h1 h2 h3) hr1 hrN hw

/-- **Fan-Sun shape, all `N ≥ 14`, no hypothesis.** -/
theorem FS1_shape_unconditional {k N r w : ℕ} (hk : k + 1 = N) (hN : 14 ≤ N)
    (hr1 : 1 ≤ r) (hrN : r ≤ N) (hw : N < w) :
    1 / (N : ℝ) ≤ ML (wFam k r w) ∨
      ∃ σ κ : ℕ, 1 ≤ σ ∧ 1 ≤ κ ∧ 2 * κ ≤ N ∧
        ML (wFam k r w) = (σ : ℝ) / ((σ * N + κ : ℕ) : ℝ) :=
  FS1_shape_of_OE hk hN (fun _ _ h1 h2 h3 => OE_low_unconditional hk hN h1 h2 h3) hr1 hrN hw

end Gap
end Sext6
end LRSpectrumFull
