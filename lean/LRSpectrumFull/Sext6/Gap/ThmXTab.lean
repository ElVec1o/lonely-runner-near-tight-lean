import LRSpectrumFull.Sext6.Gap.ThmXRun

/-!
# Theorem X, part 2: the table of last exceptional `N`  [2026-11-25]

Source: the accompanying notes on Theorem X, Section 5 (the ten values of `r` with `N_last = 3r + ell*(r)`).

For `r = 2, 4, 6, 10, 12, 18, 24, 30, 42, 60` the last `N` with `XHolds r N` (the criterion
`D0 > 2N - 2r`) is `7, 13, 20, 33, 38, 56, 74, 93, 131, 183` respectively; `LastExc r L` says
`XHolds r L` and `¬ XHolds r N` for every `N > L` (finite check on `(L, 4 r]` by `decide +kernel`, then
`not_xholds_of_ge`).  `nonInterval_42` records that the exceptional set is not an interval.
No `sorry`, no `axiom`.

Convention: as in `ThmXRun`.
Hypotheses: none (closed numerical statements).
Axiom audit: covered by `Axioms24`.
-/

namespace LRSpectrumFull
namespace Sext6
namespace Gap

theorem lastExc_r2 : LastExc 2 7 :=
  lastExc_of_finite (by norm_num) (by decide +kernel) (by decide +kernel)
theorem lastExc_r4 : LastExc 4 13 :=
  lastExc_of_finite (by norm_num) (by decide +kernel) (by decide +kernel)
theorem lastExc_r6 : LastExc 6 20 :=
  lastExc_of_finite (by norm_num) (by decide +kernel) (by decide +kernel)
theorem lastExc_r10 : LastExc 10 33 :=
  lastExc_of_finite (by norm_num) (by decide +kernel) (by decide +kernel)
theorem lastExc_r12 : LastExc 12 38 :=
  lastExc_of_finite (by norm_num) (by decide +kernel) (by decide +kernel)
theorem lastExc_r18 : LastExc 18 56 :=
  lastExc_of_finite (by norm_num) (by decide +kernel) (by decide +kernel)
theorem lastExc_r24 : LastExc 24 74 :=
  lastExc_of_finite (by norm_num) (by decide +kernel) (by decide +kernel)
theorem lastExc_r30 : LastExc 30 93 :=
  lastExc_of_finite (by norm_num) (by decide +kernel) (by decide +kernel)
theorem lastExc_r42 : LastExc 42 131 :=
  lastExc_of_finite (by norm_num) (by decide +kernel) (by decide +kernel)
theorem lastExc_r60 : LastExc 60 183 :=
  lastExc_of_finite (by norm_num) (by decide +kernel) (by decide +kernel)

/-- The exceptional set is not an interval: for `r = 42`, `N = 128` and `131` satisfy the criterion,
`N = 129, 130` do not. -/
theorem nonInterval_42 :
    XHolds 42 128 ∧ ¬ XHolds 42 129 ∧ ¬ XHolds 42 130 ∧ XHolds 42 131 := by
  decide +kernel

end Gap
end Sext6
end LRSpectrumFull
