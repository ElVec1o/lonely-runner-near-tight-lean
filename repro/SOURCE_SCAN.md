# Checks run on the shipped files at packaging time (25 November 2026)

Observed means the command was run and its output read.

## Import closure (observed)

* The import closure of `LRSpectrumFull.Sext6.Release` in the development tree has 18,946 modules; that of `LRSpectrumFull.L5S5.FiveSpeedFinal4` (the closure of the five-speed archive) has 17,598. Release closure minus archive closure: 1,349 modules; the archive closure minus the Release closure: 1 module (`FiveSpeedFinal4` itself).
* This repository ships those 1,349 modules and the 4 modules `Sext6/Gen/{TwoDir,Height,Weight1Stmt,Weight1}` (they import only modules of the Release closure): 1,353 modules.
* Every `import LRSpectrumFull.*` of every shipped module resolves to a shipped module or to a module of the archive's closure (2,626 import edges, 0 unresolved). No shipped module is also in the archive's closure. None of the 1,353 paths is among the 9,496 module paths of the archive (compared with the archive's file list from the GitHub API, git blob hashes).
* The 9,496 archive modules that exist locally were compared by git blob hash with the archive: 9,465 identical, 31 different (comments only, edited for the archive's release).

## Source scan (observed): `sorry`, axioms and the like

After deleting comments and docstrings (nested block comments, line comments, strings kept), the tokens `sorry`, `sorryAx`, `admit`, `axiom`, `native_decide`, `unsafe`, `implemented_by`, `extern`, `opaque`, `ofReduceBool` occur in none of the 1,353 modules. The token `partial` occurs in four audit modules (`Gap/Axioms12`, `Axioms16`, `Axioms17`, `Axioms18`): a meta-level `partial def depClosure`, used only for the reachability test of `DusartPi`.

## Private-material scan (observed)

Patterns over all files of this repository at the time of the scan (1,430 files): `/Users/`, `private/`, `INVENTION`, `NEXT_BIG`, e-mail addresses, `ghp_`, `gho_`, `sk-`, `token`, `secret`, `password`, `api key`, model names (`Sonnet`, `Opus`, `Fable`, `Haiku`), `seat`, `Rule N`, `CLAUDE.md`, `STATE.md`, `PROOF.md`, `.md`: no hit, except the author's name in `README.md`, `LICENSE.md` and `CITATION.cff`. Before the edits below there were hits in 12 files (paths of private working notes in docstrings, "task n, T2 seat", "[STATUS: UNBUILT ...]").

## Edited files (11; comments and docstrings only)

For each edited file the text with comments and docstrings deleted is identical to that of the development tree (checked by script at packaging time).

| file | change |
|---|---|
| `Sext6/Box.lean`, `Sext6/Height.lean`, `Sext6/T2Core.lean`, `Sext6/Prime111.lean` | working labels (task number, seat) removed from the header; in `Prime111` a reference to a private note and to private logs replaced by "per-prime search outputs (not shipped)" |
| `Sext6/Statement.lean` | the reference to private logs replaced by "per-prime search outputs (not shipped)" |
| `Sext6/T2Height.lean` | working label removed; the docstring of `TheoremA16_LRC5` said that `LRC 5` is a theorem of the literature for `n <= 13` and that `ResidueDataSub P16` is "computed, uncertified"; now: `LRC 5` is proved in this development (`Sext6.LRC5`) and `ResidueDataSub P16` is discharged in `K313.Discharge16` |
| `Sext6/K313/Final.lean` | the docstring said that the 16 primes give the box `41,912,890` and that `TheoremA16_LRC5` assembles them; the assembly uses the box `21^5 = 4,084,101` (`TheoremBox_P16_T2`); corrected, the other boxes mentioned as not used |
| `Sext6/Gen/{TwoDir,Height,Weight1Stmt,Weight1}.lean` | the header line `[STATUS: UNBUILT, written ..., drafting seat]` removed (the saved build outputs `gen_*` show that the modules build); in `Weight1` a reference to a private review note removed |

The generated modules (`FinBlk*`, `RobustKBlk*`, `OEFin*`, `OEPrimeBlocks`, `RobustCorB2/B3`) already carried a banner without private paths in the development tree.

## Not checked

That the shipped tree builds from a clean checkout; that the Lean statements say what the papers say (beyond the reviews described in the README); anything about the 17,597 archive modules (see the archive's README).
