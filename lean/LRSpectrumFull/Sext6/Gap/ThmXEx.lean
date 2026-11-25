import LRSpectrumFull.Sext6.Gap.ThmXMain

/-!
# Theorem X: non-vacuity check  [2026-11-25]

`N = 4`, `r = 2`: `B = {1,3,4}`, `W = {7}`, `D0 = 7 > 2N - 2r = 4`.  The vector `![1,3,4,7]` satisfies
`IsV 4 2` and Theorem X gives `ML < 1/4` (the ledger value is `1/5`).
No `sorry`, no `axiom`.

Convention: as in `ThmXMain`.  Hypotheses: none.  Axiom audit: covered by `Axioms24`.
-/

namespace LRSpectrumFull
namespace Sext6
namespace Gap

theorem isV_example : IsV 4 2 (![1, 3, 4, 7] : Fin 4 → ℤ) := by
  constructor
  · intro i
    fin_cases i
    · left; simp
    · left; simp
    · left; simp
    · right; exact ⟨7, by simp, by norm_num, by norm_num, by decide⟩
  · intro x hx
    rcases hx with ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩
    · interval_cases x
      · exact ⟨0, by simp⟩
      · exact absurd rfl h3
      · exact ⟨1, by simp⟩
      · exact ⟨2, by simp⟩
    · interval_cases x
      · exact ⟨3, by simp⟩
      · exact absurd h3 (by decide)

theorem dspec_example : DSpec 4 2 7 :=
  ⟨by norm_num, by norm_num, by norm_num, by norm_num, by decide, fun b hb _ => hb⟩

theorem example_lt : ML (![1, 3, 4, 7] : Fin 4 → ℤ) < 1 / ((4 : ℕ) : ℝ) :=
  (thmX_iff dspec_example (by norm_num) _ isV_example).mpr (by norm_num)

end Gap
end Sext6
end LRSpectrumFull
