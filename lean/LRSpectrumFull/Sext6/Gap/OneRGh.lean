import LRSpectrumFull.Sext6.Gap.OneRG

/-!
# One-entry deletion `B = [N] \ {r}`, part 7: Proposition G in the form `L w h / (w h + 2)`  [2026-11-25]

Source: the accompanying notes on the one-entry deletion (Plan 3), Proposition G.

With `L = 2/D`, `X0 = D - 2r`, `h = 1/(2r) + 1/X0`:
`L w h / (w h + 2) = 2 w / (D w + 4 r X0)` (`G_form_eq`), so `prop_G` reads
`L w h / (w h + 2) ≤ ML ([N]_{r → w}) ≤ L` for every integer `w ≥ 4 N` (`prop_G_h`).
No `sorry`, no `axiom`.

Convention: `N` is the size of the ambient interval `[N]` (`DSpec N r D`, `IsB N r v`); `wFam (k+1) r w` has `k + 2 = N` entries. Speeds are the moving runners; the runner at rest is not counted, so a vector of `N` speeds means `N + 1` runners and the Lonely Runner value is `1/(N+1)`.
Hypotheses: those of the individual statements. The unproved predicates `DusartPi`, `LRCHyp`, `CopWinHyp` are not hypotheses of any statement in this module.
Axiom audit: covered by `Axioms21`.
-/

namespace LRSpectrumFull
namespace Sext6
namespace Gap

theorem G_form_eq {D r : ℕ} {w : ℝ} (hw : 0 < w) (hD : (0 : ℝ) < D) (hr : (0 : ℝ) < r)
    (hX : (0 : ℝ) < (D : ℝ) - 2 * r) :
    2 / (D : ℝ) * w * (1 / (2 * (r : ℝ)) + 1 / ((D : ℝ) - 2 * r)) /
        (w * (1 / (2 * (r : ℝ)) + 1 / ((D : ℝ) - 2 * r)) + 2) =
      2 * w / ((D : ℝ) * w + 4 * r * ((D : ℝ) - 2 * r)) := by
  have hh : 0 < 1 / (2 * (r : ℝ)) + 1 / ((D : ℝ) - 2 * r) :=
    add_pos (one_div_pos.mpr (by linarith)) (one_div_pos.mpr hX)
  have hn1 : w * (1 / (2 * (r : ℝ)) + 1 / ((D : ℝ) - 2 * r)) + 2 ≠ 0 :=
    (add_pos (mul_pos hw hh) (by norm_num)).ne'
  have hn2 : (D : ℝ) * w + 4 * r * ((D : ℝ) - 2 * r) ≠ 0 :=
    (add_pos (mul_pos hD hw) (mul_pos (by linarith : (0 : ℝ) < 4 * (r : ℝ)) hX)).ne'
  rw [div_eq_div_iff hn1 hn2]
  have hDne := hD.ne'
  have hrne := hr.ne'
  have hXne := hX.ne'
  first
    | (field_simp; ring)
    | field_simp

/-- **Proposition G**, in the form of the notes: for every integer `w ≥ 4 N`,
`L w h / (w h + 2) ≤ ML ([N]_{r → w}) ≤ L`, `L = 2/D`, `h = 1/(2r) + 1/(D - 2r)`. -/
theorem prop_G_h {k N r D w : ℕ} (hk : k + 2 = N) (hS : DSpec N r D) (hw : 4 * N ≤ w) :
    2 / (D : ℝ) * (w : ℝ) * (1 / (2 * (r : ℝ)) + 1 / ((D : ℝ) - 2 * r)) /
        ((w : ℝ) * (1 / (2 * (r : ℝ)) + 1 / ((D : ℝ) - 2 * r)) + 2) ≤ ML (wFam (k + 1) r w) ∧
      ML (wFam (k + 1) r w) ≤ 2 / (D : ℝ) := by
  have hr := hS.hr
  have hN2 := hS.hN
  have hN3 := hS.hN3
  have hD1 := hS.hD1
  obtain ⟨h1, h2⟩ := prop_G hk hS hw
  refine ⟨?_, h2⟩
  have hw0 : (0 : ℝ) < (w : ℝ) := by exact_mod_cast (by omega : 0 < w)
  have hD : (0 : ℝ) < D := by exact_mod_cast (by omega : 0 < D)
  have hr0 : (0 : ℝ) < r := by exact_mod_cast (by omega : 0 < r)
  have hX : (0 : ℝ) < (D : ℝ) - 2 * r := by
    have h3 : 2 * r < D := by omega
    have h' : ((2 * r : ℕ) : ℝ) < D := by exact_mod_cast h3
    push_cast at h'
    linarith
  rw [G_form_eq hw0 hD hr0 hX]
  exact h1

end Gap
end Sext6
end LRSpectrumFull
