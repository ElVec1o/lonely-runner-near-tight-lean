import LRSpectrumFull.Sext6.Gap.OEFinA
import LRSpectrumFull.Sext6.Gap.OEFinB
import LRSpectrumFull.Sext6.Gap.OEFinC
import LRSpectrumFull.Sext6.Gap.OEFinExc

/-!
# Theorem OE-low, finite range `14 ≤ N ≤ 78`: assembly  [2026-11-24]
`fin_tab` : the three kernel-checked table modules give `tabOK N tab` for every `14 ≤ N ≤ 78`;
`OE_low_fin` : `1/N ≤ ML` for `14 ≤ N ≤ 78`, `1 ≤ r`, `2r ≤ N`, `w > N` (unconditional).
No `sorry`, no `axiom`.

Convention: `N = k + 1` is the number of entries (speeds) of the one-entry vector `wFam k r w = ([1,N] \ {r}) ∪ {w}`. Speeds are the moving runners; the runner at rest is not counted, so a vector of `N` speeds means `N + 1` runners and the Lonely Runner value is `1/(N+1)`.
Hypotheses: those of the individual statements (numerical bounds, structural conditions and, where named in the list above, window predicates such as `PrimeWin`, `CopWin`, `PrimeWindow7`, which later modules discharge for explicit ranges). The unproved predicates `DusartPi`, `LRCHyp`, `CopWinHyp` are not hypotheses of any statement in this module.
Axiom audit: covered by `Axioms6` (first); every later audit module imports this module (`#print axioms`; declarations not printed there are bricks of printed ones, so their axioms are bounded by the printed lines).
-/

namespace LRSpectrumFull
namespace Sext6
namespace Gap

theorem fin_tab : ∀ N, 14 ≤ N → N ≤ 78 → ∃ tab, tabOK N tab = true := by
  intro N h1 h2
  interval_cases N
  · exact ⟨_, chunk14⟩
  · exact ⟨_, chunk15⟩
  · exact ⟨_, chunk16⟩
  · exact ⟨_, chunk17⟩
  · exact ⟨_, chunk18⟩
  · exact ⟨_, chunk19⟩
  · exact ⟨_, chunk20⟩
  · exact ⟨_, chunk21⟩
  · exact ⟨_, chunk22⟩
  · exact ⟨_, chunk23⟩
  · exact ⟨_, chunk24⟩
  · exact ⟨_, chunk25⟩
  · exact ⟨_, chunk26⟩
  · exact ⟨_, chunk27⟩
  · exact ⟨_, chunk28⟩
  · exact ⟨_, chunk29⟩
  · exact ⟨_, chunk30⟩
  · exact ⟨_, chunk31⟩
  · exact ⟨_, chunk32⟩
  · exact ⟨_, chunk33⟩
  · exact ⟨_, chunk34⟩
  · exact ⟨_, chunk35⟩
  · exact ⟨_, chunk36⟩
  · exact ⟨_, chunk37⟩
  · exact ⟨_, chunk38⟩
  · exact ⟨_, chunk39⟩
  · exact ⟨_, chunk40⟩
  · exact ⟨_, chunk41⟩
  · exact ⟨_, chunk42⟩
  · exact ⟨_, chunk43⟩
  · exact ⟨_, chunk44⟩
  · exact ⟨_, chunk45⟩
  · exact ⟨_, chunk46⟩
  · exact ⟨_, chunk47⟩
  · exact ⟨_, chunk48⟩
  · exact ⟨_, chunk49⟩
  · exact ⟨_, chunk50⟩
  · exact ⟨_, chunk51⟩
  · exact ⟨_, chunk52⟩
  · exact ⟨_, chunk53⟩
  · exact ⟨_, chunk54⟩
  · exact ⟨_, chunk55⟩
  · exact ⟨_, chunk56⟩
  · exact ⟨_, chunk57⟩
  · exact ⟨_, chunk58⟩
  · exact ⟨_, chunk59⟩
  · exact ⟨_, chunk60⟩
  · exact ⟨_, chunk61⟩
  · exact ⟨_, chunk62⟩
  · exact ⟨_, chunk63⟩
  · exact ⟨_, chunk64⟩
  · exact ⟨_, chunk65⟩
  · exact ⟨_, chunk66⟩
  · exact ⟨_, chunk67⟩
  · exact ⟨_, chunk68⟩
  · exact ⟨_, chunk69⟩
  · exact ⟨_, chunk70⟩
  · exact ⟨_, chunk71⟩
  · exact ⟨_, chunk72⟩
  · exact ⟨_, chunk73⟩
  · exact ⟨_, chunk74⟩
  · exact ⟨_, chunk75⟩
  · exact ⟨_, chunk76⟩
  · exact ⟨_, chunk77⟩
  · exact ⟨_, chunk78⟩

theorem OE_low_fin {k N r w : ℕ} (hk : k + 1 = N) (hN : 14 ≤ N) (hN' : N ≤ 78) (hr1 : 1 ≤ r)
    (hr : 2 * r ≤ N) (hw : N < w) : 1 / (N : ℝ) ≤ ML (wFam k r w) := by
  obtain ⟨tab, ht⟩ := fin_tab N hN hN'
  rcases tabOK_sound (by omega) ht r hr1 hr w hw with hc | ⟨h14, h6, hw'⟩
  · exact ML_ge_inv_of_cover hk (by omega) hr1 (by omega) hc
  · subst h14
    subst h6
    have hk13 : k = 13 := by omega
    subst hk13
    exact ML_ge_inv_exc14 hw'

end Gap
end Sext6
end LRSpectrumFull
