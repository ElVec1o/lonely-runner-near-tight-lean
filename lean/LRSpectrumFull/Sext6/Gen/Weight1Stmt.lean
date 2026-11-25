/-
# Gen/Weight1Stmt: statement of the weight-1 lemma  

Statement only (`def ... : Prop`, no proof); the proof is `Gen/Weight1.lean` (`weight1_holds : Weight1Statement`).

Weight-1 lemma.  `v : Fin (k+1) -> Z` distinct positive speeds, `q >= 2`, all speeds except `v e` are multiples
of `q`, `gcd (v e) q = 1`, and `Sext6.LRC k` (k distinct positive speeds have `ML >= 1/(k+1)`).  Then
`ML v >= min (1/(k+1)) ((q-1)/(2q))`.
Proof sketch: `a_j = v_j / q` are k distinct positive integers; take `s0` with `gap a s0` near `ML a`; the times
`(s0+n)/q` leave `||v_j t||` unchanged for the multiples, and `n` can be chosen (coprimality) so that
`||v_e t|| >= (q-1)/(2q)`.  The condition for `ML > tau` is `tau < 1/(k+1)` and `tau < (q-1)/(2q)`
(i.e. `1 - 2 tau > 1/q`; fails for q = 2 when tau >= 1/4, so N = 3 is NOT covered).
-/
import LRSpectrumFull.Sext6.Height

namespace LRSpectrumFull
namespace Sext6

def Weight1Statement : Prop :=
  ∀ (k q : ℕ), 1 ≤ k → 2 ≤ q → Sext6.LRC k →
    ∀ v : Fin (k + 1) → ℤ, Function.Injective v → (∀ i, 0 < v i) →
      ∀ e : Fin (k + 1), (∀ i, i ≠ e → (q : ℤ) ∣ v i) → IsCoprime (v e) (q : ℤ) →
        min ((1 : ℝ) / ((k : ℝ) + 1)) (((q : ℝ) - 1) / (2 * (q : ℝ))) ≤ ML v

end Sext6
end LRSpectrumFull
