import LRSpectrumFull.MaxLoneliness
import Mathlib.Data.Nat.Lattice
import Mathlib.Data.Nat.GCD.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.IntervalCases

/-!
# Theorem V (value of ML for [N]_{r -> m r}): definitions and arithmetic of beta  [2026-11-24]

Source: the accompanying notes on Theorem V (Theorem V, Lemma 1).
Reuses the project definition `LRSpectrumFull.ML` (`MaxLoneliness.lean`) for `v : Fin (k+1) → ℤ`.
Here `N = k + 1` is the number of speeds.
No `sorry`, no `axiom`.

Convention: `N = k + 1` is the number of speeds of the vector `v : Fin (k+1) → ℤ`. Speeds are the moving runners; the runner at rest is not counted, so a vector of `N` speeds means `N + 1` runners and the Lonely Runner value is `1/(N+1)`.
Hypotheses: those of the individual statements (numerical bounds, structural conditions and, where named in the list above, window predicates such as `PrimeWin`, `CopWin`, `PrimeWindow7`, which later modules discharge for explicit ranges). The unproved predicates `DusartPi`, `LRCHyp`, `CopWinHyp` are not hypotheses of any statement in this module.
Axiom audit: covered by `Axioms` (first); every later audit module imports this module (`#print axioms`; declarations not printed there are bricks of printed ones, so their axioms are bounded by the printed lines).
-/

namespace LRSpectrumFull
namespace Sext6
namespace Gap

/-- The speed vector `([1,N] \ {r}) ∪ {m r}` on `N = k + 1` speeds: index `i` carries `i + 1`,
except index `r - 1` which carries `m * r`. -/
def vFam (k r m : ℕ) : Fin (k + 1) → ℤ :=
  fun i => if (i : ℕ) + 1 = r then ((m * r : ℕ) : ℤ) else (((i : ℕ) + 1 : ℕ) : ℤ)

/-- `s = N + 1 - r`. -/
def sFam (N r : ℕ) : ℕ := N + 1 - r

/-- `β(N,r)`: the least `b ≥ s = N + 1 - r` (written `N + 1 ≤ r + b`) coprime to `r`. -/
noncomputable def betaFam (N r : ℕ) : ℕ := sInf {b : ℕ | N + 1 ≤ r + b ∧ Nat.Coprime b r}

/-- Hypothesis (H) of the accompanying notes section 1, with `β` given by its defining properties
(`hb1`: `β ≥ s`; `hb2`: `gcd(β,r)=1`; `hb3`: minimality). -/
structure Spec (N r m β : ℕ) : Prop where
  hN : 2 ≤ N
  hr1 : N < 2 * r
  hr2 : r ≤ N
  hm : 2 ≤ m
  hb1 : N + 1 ≤ r + β
  hb2 : Nat.Coprime β r
  hb3 : ∀ b : ℕ, N + 1 ≤ r + b → Nat.Coprime b r → β ≤ b

theorem Spec.two_le_r {N r m β : ℕ} (h : Spec N r m β) : 2 ≤ r := by
  have := h.hN; have := h.hr1; omega

/-- Lemma 1(b): `β ≤ r + 1`. -/
theorem Spec.beta_le_succ {N r m β : ℕ} (h : Spec N r m β) : β ≤ r + 1 := by
  have h1 := h.hr1
  exact h.hb3 (r + 1) (by omega) (Nat.coprime_self_add_left.mpr (Nat.coprime_one_left r))

/-- Lemma 1(c): `β ≤ N`. -/
theorem Spec.beta_le_N {N r m β : ℕ} (h : Spec N r m β) : β ≤ N := by
  have hN := h.hN
  have h2 := h.hr2
  by_cases hrN : r = N
  · have := h.hb3 1 (by omega) (Nat.coprime_one_left r)
    omega
  · have := h.beta_le_succ
    omega

theorem Spec.beta_pos {N r m β : ℕ} (h : Spec N r m β) : 0 < β := by
  by_contra h0
  have h0' : β = 0 := by omega
  have hb := h.hb2
  rw [h0', Nat.coprime_zero_left] at hb
  have := h.two_le_r
  omega

/-- `betaFam N r` satisfies the specification, under (H). -/
theorem spec_betaFam {N r m : ℕ} (hN : 2 ≤ N) (hr1 : N < 2 * r) (hr2 : r ≤ N) (hm : 2 ≤ m) :
    Spec N r m (betaFam N r) := by
  have hne : ({b : ℕ | N + 1 ≤ r + b ∧ Nat.Coprime b r}).Nonempty :=
    ⟨r + 1, by omega, Nat.coprime_self_add_left.mpr (Nat.coprime_one_left r)⟩
  have hmem := Nat.sInf_mem hne
  exact ⟨hN, hr1, hr2, hm, hmem.1, hmem.2, fun b hb1 hb2 => Nat.sInf_le ⟨hb1, hb2⟩⟩

theorem sFam_add {N r : ℕ} (h : r ≤ N) : sFam N r + r = N + 1 := by
  unfold sFam; omega

end Gap
end Sext6
end LRSpectrumFull
