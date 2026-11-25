import LRSpectrumFull.Sext6.Gap.All
import LRSpectrumFull.Sext6.K313.Final

/-!
# `Sext6.Release`: umbrella for the verification of everything that is released

This module contains no declaration. It imports

* `Sext6.Gap.All`: the 28 axiom-audit modules of `Sext6/Gap` (value formula, one-entry bounds, insertion estimates, ...);
* `Sext6.K313.Final`: `TheoremA_unconditional`, the classification of six distinct positive integers with
  `ML ≤ 1/7` as the dilations `c · (1, …, 6)`, with no hypothesis (it prints its `#print axioms`).

One command checks everything:

    lake build LRSpectrumFull.Sext6.Release

The closure of `K313.Final` contains the five-speed development (`LRC5`, `L5S5.FiveSpeedFinal3`) and the 16 clean-prime
certificates `K313.P313 .. K313.P467`; it is by far the larger part of the cost (see the repository README).
`Sext6.Gap.All` alone is the cheap check.

Convention: `N` counts speeds (moving runners); the runner at rest is not counted. `TheoremA` is about `Fin 6`, six speeds,
seven runners including the one at rest, and the threshold `1/7` is the Lonely Runner value `1/(N+1)` for `N = 6`.
-/
