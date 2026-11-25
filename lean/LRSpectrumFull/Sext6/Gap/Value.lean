import LRSpectrumFull.Sext6.Gap.UpperTrap

/-!
# Theorem V (assembly)  [2026-11-24]

For `N ≥ 2`, `N/2 < r ≤ N`, `m ≥ 2`, `s = N + 1 - r`, `β = least integer ≥ s coprime to r`
and `V = ([1,N] \ {r}) ∪ {m r}` (`N = k + 1` speeds, `vFam k r m`):

  `ML V = max (1/(N+1)) (m/(m r + β)) = m / (m r + min β (m s))`,

and `ML V = 1/(N+1)` iff `m s ≤ β`.   (the accompanying notes section 1, Lemma 0, section 3.)

Convention: `N = k + 1` is the number of speeds of the vector `v : Fin (k+1) → ℤ`. Speeds are the moving runners; the runner at rest is not counted, so a vector of `N` speeds means `N + 1` runners and the Lonely Runner value is `1/(N+1)`.
Hypotheses: those of the individual statements (numerical bounds, structural conditions and, where named in the list above, window predicates such as `PrimeWin`, `CopWin`, `PrimeWindow7`, which later modules discharge for explicit ranges). The unproved predicates `DusartPi`, `LRCHyp`, `CopWinHyp` are not hypotheses of any statement in this module.
Axiom audit: covered by `Axioms` (first); every later audit module imports this module (`#print axioms`; declarations not printed there are bricks of printed ones, so their axioms are bounded by the printed lines).
-/

namespace LRSpectrumFull
namespace Sext6
namespace Gap

/-- Theorem V, for any `β` satisfying the specification `Spec`. -/
theorem value_formula_spec {k N r m β : ℕ} (hk : k + 1 = N) (hS : Spec N r m β) :
    ML (vFam k r m) = max (1 / ((N : ℝ) + 1)) ((m : ℝ) / ((m * r + β : ℕ) : ℝ)) := by
  have hbpos := hS.beta_pos
  have hrr := hS.two_le_r
  have hNR : (0 : ℝ) < (N : ℝ) + 1 := by positivity
  have hDR : (0 : ℝ) < ((m * r + β : ℕ) : ℝ) := by
    have : 0 < m * r + β := by omega
    exact_mod_cast this
  apply le_antisymm
  · exact ML_le_tau hk hS _ (le_max_left _ _) (le_max_right _ _)
  · apply max_le
    · by_cases hlt : m * (N + 1) < m * r + β
      · exact ML_ge_B hk hS hlt
      · have h1 : m * r + β ≤ m * (N + 1) := by omega
        have h2 : (((m * r + β : ℕ)) : ℝ) ≤ (m : ℝ) * ((N : ℝ) + 1) := by exact_mod_cast h1
        have h3 : 1 / ((N : ℝ) + 1) ≤ (m : ℝ) / ((m * r + β : ℕ) : ℝ) := by
          rw [div_le_div_iff₀ hNR hDR]
          linarith
        exact h3.trans (ML_ge_A hk hS)
    · exact ML_ge_A hk hS

theorem max_eq_alt {N r m β s : ℕ} (hs : s + r = N + 1) (hm : 0 < m) (hb : 0 < β) :
    max (1 / ((N : ℝ) + 1)) ((m : ℝ) / ((m * r + β : ℕ) : ℝ)) =
      (m : ℝ) / ((m * r + min β (m * s) : ℕ) : ℝ) := by
  have hNR : (0 : ℝ) < (N : ℝ) + 1 := by positivity
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hDR : (0 : ℝ) < ((m * r + β : ℕ) : ℝ) := by
    have : 0 < m * r + β := by positivity
    exact_mod_cast this
  have hmul : m * (N + 1) = m * s + m * r := by rw [← hs]; ring
  rcases le_total β (m * s) with h | h
  · rw [min_eq_left h]
    apply max_eq_right
    rw [div_le_div_iff₀ hNR hDR]
    have h1 : m * r + β ≤ m * (N + 1) := by linarith
    have h2 : (((m * r + β : ℕ)) : ℝ) ≤ (m : ℝ) * ((N : ℝ) + 1) := by exact_mod_cast h1
    linarith
  · rw [min_eq_right h]
    have h1 : m * (N + 1) ≤ m * r + β := by linarith
    have h2 : (m : ℝ) * ((N : ℝ) + 1) ≤ (((m * r + β : ℕ)) : ℝ) := by exact_mod_cast h1
    have h3 : (m : ℝ) / ((m * r + β : ℕ) : ℝ) ≤ 1 / ((N : ℝ) + 1) := by
      rw [div_le_div_iff₀ hDR hNR]
      linarith
    rw [max_eq_left h3]
    have h4 : m * r + m * s = m * (N + 1) := by linarith
    rw [h4]
    push_cast
    field_simp

theorem tight_iff_spec {k N r m β : ℕ} (hk : k + 1 = N) (hS : Spec N r m β) :
    ML (vFam k r m) = 1 / ((N : ℝ) + 1) ↔ m * (N + 1 - r) ≤ β := by
  have hbpos := hS.beta_pos
  have hrr := hS.two_le_r
  have hr2 := hS.hr2
  have hNR : (0 : ℝ) < (N : ℝ) + 1 := by positivity
  have hDR : (0 : ℝ) < ((m * r + β : ℕ) : ℝ) := by
    have : 0 < m * r + β := by omega
    exact_mod_cast this
  rw [value_formula_spec hk hS, max_eq_left_iff, div_le_div_iff₀ hDR hNR]
  have hmul : m * (N + 1) = m * (N + 1 - r) + m * r := by
    have : N + 1 - r + r = N + 1 := by omega
    calc m * (N + 1) = m * (N + 1 - r + r) := by rw [this]
      _ = _ := by ring
  constructor
  · intro h
    have h' : m * (N + 1) ≤ m * r + β := by exact_mod_cast (by linarith : (m : ℝ) * ((N : ℝ) + 1) ≤ ((m * r + β : ℕ) : ℝ))
    linarith
  · intro h
    have h' : m * (N + 1) ≤ m * r + β := by linarith
    have h2 : (m : ℝ) * ((N : ℝ) + 1) ≤ (((m * r + β : ℕ)) : ℝ) := by exact_mod_cast h'
    linarith

/-- **Theorem V** (the accompanying notes section 1), with `β = betaFam N r` the least integer `≥ s` coprime to `r`.
`N = k + 1` is the number of speeds. -/
theorem theoremV {k N r m : ℕ} (hk : k + 1 = N) (hN : 2 ≤ N) (hr1 : N < 2 * r) (hr2 : r ≤ N)
    (hm : 2 ≤ m) :
    ML (vFam k r m) = max (1 / ((N : ℝ) + 1)) ((m : ℝ) / ((m * r + betaFam N r : ℕ) : ℝ)) :=
  value_formula_spec hk (spec_betaFam hN hr1 hr2 hm)

/-- Theorem V, second form: `ML = m / (m r + min (β, m s))`. -/
theorem theoremV_alt {k N r m : ℕ} (hk : k + 1 = N) (hN : 2 ≤ N) (hr1 : N < 2 * r)
    (hr2 : r ≤ N) (hm : 2 ≤ m) :
    ML (vFam k r m) =
      (m : ℝ) / ((m * r + min (betaFam N r) (m * sFam N r) : ℕ) : ℝ) := by
  have hS := spec_betaFam (m := m) hN hr1 hr2 hm
  rw [value_formula_spec hk hS]
  exact max_eq_alt (sFam_add hr2) (by omega) hS.beta_pos

/-- Tightness criterion (Goddyn-Wong): `ML V = 1/(N+1)` iff `m s ≤ β`. -/
theorem theoremV_tight_iff {k N r m : ℕ} (hk : k + 1 = N) (hN : 2 ≤ N) (hr1 : N < 2 * r)
    (hr2 : r ≤ N) (hm : 2 ≤ m) :
    ML (vFam k r m) = 1 / ((N : ℝ) + 1) ↔ m * sFam N r ≤ betaFam N r :=
  tight_iff_spec hk (spec_betaFam hN hr1 hr2 hm)

end Gap
end Sext6
end LRSpectrumFull
