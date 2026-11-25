import LRSpectrumFull.Sext6.Gap.Value

/-!
# Q8.1, Lemma Z  [2026-11-25]

Source: the accompanying notes on Zhang's Question 8.1 section 5.1.

For `N/2 < r1 < r2 ≤ N` and `γ = r2 / gcd(r1, r2)`:  `β(N, r1) < γ · s1`  (`s1 = N + 1 - r1`).
Hence the criterion (9) `m s ≤ β` fails for the smaller removed speed `r1` with every multiplier `m ≥ γ`; in
particular a single entry `r1 -> m r1` with `m ≥ r2/gcd(r1,r2)` is never tight (`lemmaZ_not_tight`).
Proof: `(γ - 1) s1 > r1`, so the window `[s1, s1 + r1]` (which contains an integer `≡ 1 (mod r1)`)
lies below `γ s1`.
No `sorry`, no `axiom`.

Convention: `N = k + 1` is the number of speeds of the vector `v : Fin (k+1) → ℤ`. Speeds are the moving runners; the runner at rest is not counted, so a vector of `N` speeds means `N + 1` runners and the Lonely Runner value is `1/(N+1)`.
Hypotheses: those of the individual statements (numerical bounds, structural conditions and, where named in the list above, window predicates such as `PrimeWin`, `CopWin`, `PrimeWindow7`, which later modules discharge for explicit ranges). The unproved predicates `DusartPi`, `LRCHyp`, `CopWinHyp` are not hypotheses of any statement in this module.
Axiom audit: covered by `Axioms8` (`#print axioms`; declarations not printed there are bricks of printed ones, so their axioms are bounded by the printed lines).
-/

namespace LRSpectrumFull
namespace Sext6
namespace Gap

/-- Any `r + 1` consecutive integers `s, ..., s + r` contain a unit modulo `r` (one `≡ 1`). -/
theorem exists_unit_window (r s : ℕ) (hr : 2 ≤ r) :
    ∃ b : ℕ, s ≤ b ∧ b ≤ s + r ∧ Nat.Coprime b r := by
  have hr0 : 0 < r := by omega
  have hdm := Nat.div_add_mod s r
  have hlt : s % r < r := Nat.mod_lt s hr0
  have hcop : ∀ t : ℕ, Nat.Coprime (1 + r * t) r := by
    intro t
    have h1 : (1 + r * t) % r = 1 := by
      rw [Nat.add_mul_mod_self_left]
      exact Nat.mod_eq_of_lt (by omega)
    have h2 : Nat.gcd r (1 + r * t) = 1 := by
      rw [Nat.gcd_rec, h1]
      exact Nat.gcd_one_left r
    show Nat.gcd (1 + r * t) r = 1
    rw [Nat.gcd_comm]
    exact h2
  by_cases hρ : s % r ≤ 1
  · refine ⟨1 + r * (s / r), ?_, ?_, hcop _⟩
    · omega
    · omega
  · refine ⟨1 + r * (s / r + 1), ?_, ?_, hcop _⟩
    · have : r * (s / r + 1) = r * (s / r) + r := by ring
      omega
    · have : r * (s / r + 1) = r * (s / r) + r := by ring
      omega

/-- **Lemma Z.** `r1 < r2 ≤ N < 2 r1`, `γ = r2 / gcd(r1, r2)`: `β(N, r1) < γ · s(N, r1)`. -/
theorem lemmaZ {N r1 r2 : ℕ} (hN : 2 ≤ N) (h1 : N < 2 * r1) (h12 : r1 < r2) (h2 : r2 ≤ N) :
    betaFam N r1 < (r2 / Nat.gcd r1 r2) * sFam N r1 := by
  have hr1N : r1 ≤ N := by omega
  have hr12 : 2 ≤ r1 := by omega
  have hgpos : 0 < Nat.gcd r1 r2 := Nat.gcd_pos_of_pos_left _ (by omega)
  obtain ⟨α, hα⟩ := Nat.gcd_dvd_left r1 r2
  obtain ⟨γ, hγ⟩ := Nat.gcd_dvd_right r1 r2
  generalize Nat.gcd r1 r2 = g at hgpos hα hγ ⊢
  have hdiv : r2 / g = γ := by
    rw [hγ]
    exact Nat.mul_div_cancel_left γ hgpos
  rw [hdiv]
  -- s = N + 1 - r1 and the window
  have hs : sFam N r1 = N + 1 - r1 := rfl
  have hαγ : α + 1 ≤ γ := by
    by_contra hcon
    have : γ ≤ α := by omega
    have : g * γ ≤ g * α := Nat.mul_le_mul_left g this
    omega
  have hα1 : 1 ≤ α := by
    rcases Nat.eq_zero_or_pos α with h | h
    · rw [h] at hα
      simp at hα
      omega
    · exact h
  have hsg : g + 1 ≤ sFam N r1 := by
    have hlt : g * α + g ≤ g * γ := by nlinarith [Nat.mul_le_mul_left g hαγ]
    rw [hs]
    omega
  have hkey : sFam N r1 + r1 + 1 ≤ γ * sFam N r1 := by
    have e1 : (α + 1) * sFam N r1 ≤ γ * sFam N r1 := Nat.mul_le_mul_right _ hαγ
    have e2 : α * (g + 1) ≤ α * sFam N r1 := Nat.mul_le_mul_left α hsg
    nlinarith
  obtain ⟨b, hb1, hb2, hb3⟩ := exists_unit_window r1 (sFam N r1) hr12
  have hS := spec_betaFam (m := 2) hN h1 hr1N le_rfl
  have hbeta : betaFam N r1 ≤ b := hS.hb3 b (by rw [hs] at hb1; omega) hb3
  omega

/-- Consequence: a single entry `r1 -> m r1` with `m ≥ r2 / gcd(r1, r2)` (and `m ≥ 2`) is never tight. -/
theorem lemmaZ_not_tight {k N r1 r2 m : ℕ} (hk : k + 1 = N) (hN : 2 ≤ N) (h1 : N < 2 * r1)
    (h12 : r1 < r2) (h2 : r2 ≤ N) (hm : 2 ≤ m) (hmγ : r2 / Nat.gcd r1 r2 ≤ m) :
    ML (vFam k r1 m) ≠ 1 / ((N : ℝ) + 1) := by
  intro hML
  have hr1N : r1 ≤ N := by omega
  have hT := (theoremV_tight_iff hk hN h1 hr1N hm).mp hML
  have hZ := lemmaZ hN h1 h12 h2
  have : (r2 / Nat.gcd r1 r2) * sFam N r1 ≤ m * sFam N r1 := Nat.mul_le_mul_right _ hmγ
  omega

end Gap
end Sext6
end LRSpectrumFull
