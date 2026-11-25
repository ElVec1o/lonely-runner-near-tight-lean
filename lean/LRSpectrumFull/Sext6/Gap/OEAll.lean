import LRSpectrumFull.Sext6.Gap.OEFin
import LRSpectrumFull.Sext6.Gap.OEPrimeBlocks
import LRSpectrumFull.Sext6.Gap.OEPrimeDusart

/-!
# Theorem OE-low, all `N ≥ 14`  [2026-11-24]

`OE_low_all`: for `N ≥ 14`, `1 ≤ r`, `2 r ≤ N`, `w > N`:  `1/N ≤ ML ([N] \ {r} ∪ {w})`,
with the single hypothesis `DusartPi` (Dusart's explicit prime-counting bounds, needed only for `N > 10^5`).

* `primeWindow7_small`  : `79 ≤ N ≤ 10^5 → PrimeWindow7 N` (32 sieve blocks, unconditional).
* `primeWindow7_all`    : `DusartPi → 79 ≤ N → PrimeWindow7 N`.
* `OE_low_fin`          : `14 ≤ N ≤ 78` (kernel-checked certificate tables, unconditional).
* `OE_low_upto`         : `14 ≤ N ≤ 10^5`, UNCONDITIONAL.
* `OE_low_all`          : all `N ≥ 14`, hypothesis `DusartPi`.
No `sorry`, no `axiom`.

Convention: `N = k + 1` is the number of entries (speeds) of the one-entry vector `wFam k r w = ([1,N] \ {r}) ∪ {w}`. Speeds are the moving runners; the runner at rest is not counted, so a vector of `N` speeds means `N + 1` runners and the Lonely Runner value is `1/(N+1)`.
Hypotheses: `DusartPi` (Dusart's explicit prime-counting bounds, an imported statement carried as a `Prop` hypothesis, never an axiom) is a hypothesis only of the declarations whose statements mention it; the unconditional, `_small`, `_upto` and table statements do not use it.
Axiom audit: covered by `Axioms6` (first); every later audit module imports this module (`#print axioms`; declarations not printed there are bricks of printed ones, so their axioms are bounded by the printed lines).
-/

namespace LRSpectrumFull
namespace Sext6
namespace Gap

theorem primeWindow7_all (hD : DusartPi) {N : ℕ} (h79 : 79 ≤ N) : PrimeWindow7 N := by
  by_cases h : N ≤ 100000
  · exact primeWindow7_small h79 h
  · exact primeWindow7_of_dusart hD (by omega)

/-- **Theorem OE-low, unconditional for `14 ≤ N ≤ 10^5`.** -/
theorem OE_low_upto {k N r w : ℕ} (hk : k + 1 = N) (hN : 14 ≤ N) (hNb : N ≤ 100000)
    (hr1 : 1 ≤ r) (hr : 2 * r ≤ N) (hw : N < w) : 1 / (N : ℝ) ≤ ML (wFam k r w) := by
  by_cases h78 : N ≤ 78
  · exact OE_low_fin hk hN h78 hr1 hr hw
  · exact OE_low_of_window hk hN (primeWindow7_small (by omega) hNb) hr1 hr hw

/-- **Theorem OE-low, all `N ≥ 14`**, hypothesis `DusartPi` (used only for `N > 10^5`). -/
theorem OE_low_all (hD : DusartPi) {k N r w : ℕ} (hk : k + 1 = N) (hN : 14 ≤ N)
    (hr1 : 1 ≤ r) (hr : 2 * r ≤ N) (hw : N < w) : 1 / (N : ℝ) ≤ ML (wFam k r w) := by
  by_cases h78 : N ≤ 78
  · exact OE_low_fin hk hN h78 hr1 hr hw
  · exact OE_low_of_window hk hN (primeWindow7_all hD (by omega)) hr1 hr hw

end Gap
end Sext6
end LRSpectrumFull
