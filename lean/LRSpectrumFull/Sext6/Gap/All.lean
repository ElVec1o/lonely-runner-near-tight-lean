import LRSpectrumFull.Sext6.Gap.Axioms
import LRSpectrumFull.Sext6.Gap.Axioms2
import LRSpectrumFull.Sext6.Gap.Axioms3
import LRSpectrumFull.Sext6.Gap.Axioms4
import LRSpectrumFull.Sext6.Gap.Axioms5
import LRSpectrumFull.Sext6.Gap.Axioms6
import LRSpectrumFull.Sext6.Gap.Axioms7
import LRSpectrumFull.Sext6.Gap.Axioms8
import LRSpectrumFull.Sext6.Gap.Axioms9
import LRSpectrumFull.Sext6.Gap.Axioms10
import LRSpectrumFull.Sext6.Gap.Axioms12
import LRSpectrumFull.Sext6.Gap.Axioms13
import LRSpectrumFull.Sext6.Gap.Axioms14
import LRSpectrumFull.Sext6.Gap.Axioms15
import LRSpectrumFull.Sext6.Gap.Axioms16
import LRSpectrumFull.Sext6.Gap.Axioms17
import LRSpectrumFull.Sext6.Gap.Axioms18
import LRSpectrumFull.Sext6.Gap.Axioms19
import LRSpectrumFull.Sext6.Gap.Axioms20
import LRSpectrumFull.Sext6.Gap.Axioms21
import LRSpectrumFull.Sext6.Gap.Axioms22
import LRSpectrumFull.Sext6.Gap.Axioms23
import LRSpectrumFull.Sext6.Gap.Axioms24
import LRSpectrumFull.Sext6.Gap.Axioms25
import LRSpectrumFull.Sext6.Gap.Axioms26
import LRSpectrumFull.Sext6.Gap.Cheb30Axioms
import LRSpectrumFull.Sext6.Gap.CopWinAxioms11
import LRSpectrumFull.Sext6.Gap.MultiAxioms

/-!
# `Sext6.Gap.All`: umbrella for the one-command verification of the `Gap` library

This module contains no declaration. It imports the 28 axiom-audit modules of `Sext6/Gap`; together their
import closure is all 349 modules of `Sext6/Gap` (other than this one), 12 modules of the base development (`MaxLoneliness`,
`NearestInteger`, `NearestIntCont`, `NearestIntLipschitz`, `FarSet`, `Subtorus`, `SquareWave`, `OddRelation`,
`OddRelationBound`, `DValue`, `Delta2Boundary`, `Delta2Circle`) and their Mathlib imports. One command therefore builds and checks everything:

    lake build LRSpectrumFull.Sext6.Gap.All

Each audit module prints `#print axioms` for the headline statements it covers; a successful build means that
every module of the closure compiled and printed no `sorryAx` line. The expected printouts show only the
standard axioms `propext`, `Classical.choice`, `Quot.sound` (some lines show a subset).

What the audit modules cover (details are in the header of each module):

* `Axioms`, `Axioms2`, `Axioms3`: Theorem V (value formula for `[N]` with one entry replaced by `m r`), its corollaries,
  the primorial family and the family value `G(N)` with its asymptotics.
* `Axioms4`, `MultiAxioms`, `Axioms8`: the witness lemma, the `1/r` case, the multi-entry value, the coprime two-entry modification.
* `Axioms5`, `Axioms6`, `Axioms7`, `Axioms9`, `Axioms10`, `CopWinAxioms11`, `Cheb30Axioms`, `Axioms12`, `Axioms17`, `Axioms18`:
  the one-entry lower bound `ML ≥ 1/N` for `N ≥ 14` and its `k`-robust versions (prime windows, sieve blocks,
  Chebyshev's 30-combination); `Axioms12` and `Axioms17`, `Axioms18` are the hypothesis-free forms.
* `Axioms13`, `Axioms16`: Proposition 1.3 and the Fan-Sun shape of the one-entry values (Theorem FS1); `Axioms16` is the
  form for every `N ≥ 14` without hypothesis, `Axioms13` the form that takes the one-entry bound or `DusartPi` as hypothesis.
* `Axioms21`: the `L2` bound for the one-entry deletion, the sharper exact one-entry value and Proposition G.
* `Axioms22`: Question 8.1: Theorem C for `N = 4..9` and uniform (`theoremC_unif`), and Theorem T (the `Q81S*`, `Q81T*` modules).
* `Axioms23`: the two-entry sandwich (lower and upper bounds, `TwoE*`) and the necessity statement for the multi-entry value (`MultiNec*`).
* `Axioms24`, `Axioms25`: Theorem X, the window family `([N] \ {r}) ∪ W` (`ThmX*`); `Axioms25` covers the window size `φ(r)`, the
  exceptional-`N` bounds `ℓ*(r)` and the growth of the exceptional ratio `N/k` (`ThmXPhi`, `ThmXLast`, `ThmXGrow`).
* `Axioms26`: Theorem L, linear robustness: moduli families of size `18k+1` and `8k+1`, and `theoremS_linear` (`LinL*`).
* `Axioms14`, `Axioms15`, `Axioms19`, `Axioms20`: the value formula `ML(v, w) = w ML(v)/(w + vμ)` for large `w`
  (Theorem K*), the one-entry deletion `[N] \ {r}` and the single-speed insertion estimates.

Convention: `N` counts speeds (moving runners); the runner at rest is not counted, so `N` speeds are `N + 1` runners and
the Lonely Runner value is `1/(N+1)`. In the vector form `v : Fin (k+1) → ℤ` one has `N = k + 1`. Individual modules say
where `N`, `k` are unlinked (multi-entry, one-entry deletion `DSpec`/`IsB`, robust statements).

Hypotheses: none are assumed by this module. The imported statement `DusartPi` (explicit prime-counting bounds) and the
predicates `LRCHyp`, `CopWinHyp` occur only as explicit hypotheses of the statements that name them, never as axioms;
the hypothesis-free forms are the `*_unconditional`, `*_upto` and table statements.

The theorem about six speeds (`TheoremA_unconditional`) is not in this closure; it lives in `Sext6.K313.Final`, and
`Sext6.Release` imports both.
-/
