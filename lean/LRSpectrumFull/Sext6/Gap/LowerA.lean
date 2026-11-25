import LRSpectrumFull.Sext6.Gap.Bridge
import Mathlib.RingTheory.Coprime.Lemmas

/-!
# Theorem V, Lemma 2 (lower bound at the time a/D, D = m r + β)  [2026-11-24]

the accompanying notes section 3, Lemma 2: with `a r ≡ -1 (mod D)`, at `t = a/D` every speed of
`([1,N] \ {r}) ∪ {m r}` has `‖t v‖ ≥ m/D`.  Hence `ML ≥ m/(m r + β)`.

Convention: `N = k + 1` is the number of speeds of the vector `v : Fin (k+1) → ℤ`. Speeds are the moving runners; the runner at rest is not counted, so a vector of `N` speeds means `N + 1` runners and the Lonely Runner value is `1/(N+1)`.
Hypotheses: those of the individual statements (numerical bounds, structural conditions and, where named in the list above, window predicates such as `PrimeWin`, `CopWin`, `PrimeWindow7`, which later modules discharge for explicit ranges). The unproved predicates `DusartPi`, `LRCHyp`, `CopWinHyp` are not hypotheses of any statement in this module.
Axiom audit: covered by `Axioms` (first); every later audit module imports this module (`#print axioms`; declarations not printed there are bricks of printed ones, so their axioms are bounded by the printed lines).
-/

namespace LRSpectrumFull
namespace Sext6
namespace Gap

/-- (B) bridge: an integer `z` with `|z - n D| ≥ m` for all integers `n` is at distance `≥ m/D`
from a multiple of `D`; so `‖z/D‖ ≥ m/D`. -/
theorem nid_div_ge {D : ℕ} (hD : 0 < D) (z : ℤ) (m : ℕ)
    (h : ∀ n : ℤ, (m : ℤ) ≤ |z - n * D|) : (m : ℝ) / D ≤ nearestIntDist ((z : ℝ) / D) := by
  apply nid_ge_of_int
  intro n
  have hDR : (0 : ℝ) < D := by exact_mod_cast hD
  have hDne : (D : ℝ) ≠ 0 := hDR.ne'
  have h1 : (((m : ℤ)) : ℝ) ≤ ((|z - n * D| : ℤ) : ℝ) := Int.cast_le.mpr (h n)
  rw [Int.cast_abs] at h1
  have h2 : (m : ℝ) ≤ |((z - n * D : ℤ) : ℝ)| := by simpa using h1
  have e : (z : ℝ) / D - n = ((z - n * D : ℤ) : ℝ) / D := by
    push_cast; field_simp
  rw [e, abs_div, abs_of_pos hDR]
  gcongr

theorem abs_far_mr (D m K : ℤ) (hm : 0 ≤ m) (hD : 2 * m ≤ D) : m ≤ |D * K - m| := by
  have hD0 : 0 ≤ D := by linarith
  rcases lt_trichotomy K 0 with hK | hK | hK
  · have h1 : 0 ≤ D * (-K - 1) := mul_nonneg hD0 (by omega)
    rw [abs_of_nonpos (by nlinarith)]
    nlinarith
  · subst hK
    simp [abs_of_nonneg hm]
  · have h1 : 0 ≤ D * (K - 1) := mul_nonneg hD0 (by omega)
    rw [abs_of_nonneg (by nlinarith)]
    nlinarith

/-- The `x ∈ [1,N] \ {r}` part of Lemma 2, in integers. -/
theorem lowerA_int {N r m β : ℕ} (hS : Spec N r m β) (a c : ℤ)
    (hD : a * r + 1 = c * ((m * r + β : ℕ) : ℤ)) (x : ℕ) (hx1 : 1 ≤ x) (hxN : x ≤ N)
    (hxr : x ≠ r) (n : ℤ) : (m : ℤ) ≤ |a * x - n * ((m * r + β : ℕ) : ℤ)| := by
  by_contra hcon
  push Not at hcon
  have hN2 := hS.hN
  have hr1 := hS.hr1
  have hr2 := hS.hr2
  have hb1 := hS.hb1
  have hbpos := hS.beta_pos
  have hrr := hS.two_le_r
  have hm2 := hS.hm
  obtain ⟨hlo, hhi⟩ := abs_lt.mp hcon
  obtain ⟨y, hy⟩ : ∃ y : ℤ, y = a * x - n * ((m * r + β : ℕ) : ℤ) := ⟨_, rfl⟩
  rw [← hy] at hlo hhi
  push_cast at hD hy
  have hK : y * (r : ℤ) + (x : ℤ) = ((m : ℤ) * r + β) * (c * x - n * r) := by
    rw [hy]; linear_combination (x : ℤ) * hD
  have hD0 : (0 : ℤ) ≤ (m : ℤ) * r + β := by positivity
  have hxN' : (x : ℤ) ≤ N := by exact_mod_cast hxN
  have hx1' : (1 : ℤ) ≤ x := by exact_mod_cast hx1
  have hr1' : (N : ℤ) < 2 * r := by exact_mod_cast hr1
  have hb1' : (N : ℤ) + 1 ≤ r + β := by exact_mod_cast hb1
  have hr0 : (0 : ℤ) ≤ r := by positivity
  generalize hKdef : (c * (x : ℤ) - n * r) = K at hK
  rcases lt_trichotomy K 0 with hKl | hKz | hKg
  · have h1 : 0 ≤ ((m : ℤ) * r + β) * (-K - 1) := mul_nonneg hD0 (by omega)
    have h2 : (-(m : ℤ) + 1) * r ≤ y * r := mul_le_mul_of_nonneg_right (by omega) hr0
    nlinarith
  · subst hKz
    rcases (show 0 ≤ y ∨ y = -1 ∨ y ≤ -2 by omega) with hy0 | hy1 | hy2
    · have : 0 ≤ y * r := mul_nonneg hy0 hr0
      nlinarith
    · subst hy1
      apply hxr
      have : (x : ℤ) = r := by linarith
      exact_mod_cast this
    · have : y * r ≤ (-2) * r := mul_le_mul_of_nonneg_right hy2 hr0
      nlinarith
  · have h1 : 0 ≤ ((m : ℤ) * r + β) * (K - 1) := mul_nonneg hD0 (by omega)
    have h2 : y * r ≤ ((m : ℤ) - 1) * r := mul_le_mul_of_nonneg_right (by omega) hr0
    nlinarith

/-- The new speed `m r` part of Lemma 2, in integers. -/
theorem lowerA_speed {N r m β : ℕ} (hS : Spec N r m β) (a c : ℤ)
    (hD : a * r + 1 = c * ((m * r + β : ℕ) : ℤ)) (n : ℤ) :
    (m : ℤ) ≤ |a * ((m * r : ℕ) : ℤ) - n * ((m * r + β : ℕ) : ℤ)| := by
  have hbpos := hS.beta_pos
  have hrr := hS.two_le_r
  push_cast at hD ⊢
  have hm0 : (0 : ℤ) ≤ m := by positivity
  have h2 : 2 * (m : ℤ) ≤ (m : ℤ) * r + β := by
    have : (2 : ℤ) ≤ r := by exact_mod_cast hrr
    have : (1 : ℤ) ≤ β := by exact_mod_cast hbpos
    nlinarith
  have e : a * ((m : ℤ) * r) - n * ((m : ℤ) * r + β) =
      ((m : ℤ) * r + β) * ((m : ℤ) * c - n) - m := by
    linear_combination (m : ℤ) * hD
  rw [e]
  exact abs_far_mr _ _ _ hm0 h2

theorem coprime_D {N r m β : ℕ} (hS : Spec N r m β) : Nat.Coprime r (m * r + β) := by
  have h := (Nat.coprime_mul_left_add_left β r m).mpr hS.hb2
  rw [mul_comm r m] at h
  exact h.symm

/-- Lemma 2: `ML ≥ m / (m r + β)`. -/
theorem ML_ge_A {k N r m β : ℕ} (hk : k + 1 = N) (hS : Spec N r m β) :
    (m : ℝ) / ((m * r + β : ℕ) : ℝ) ≤ ML (vFam k r m) := by
  have hbpos := hS.beta_pos
  have hrr := hS.two_le_r
  have hDpos : 0 < m * r + β := by omega
  obtain ⟨u, v, huv⟩ : IsCoprime (r : ℤ) ((m * r + β : ℕ) : ℤ) :=
    Nat.isCoprime_iff_coprime.mpr (coprime_D hS)
  have hD : (-u) * r + 1 = v * ((m * r + β : ℕ) : ℤ) := by
    linear_combination (-1 : ℤ) * huv
  have hDR : (0 : ℝ) < ((m * r + β : ℕ) : ℝ) := by exact_mod_cast hDpos
  apply ML_ge_fam hk (by omega) hS.hr2 _ (((-u : ℤ) : ℝ) / ((m * r + β : ℕ) : ℝ))
  · intro x hx1 hxN hxr
    have e : (x : ℝ) * (((-u : ℤ) : ℝ) / ((m * r + β : ℕ) : ℝ)) =
        (((-u) * (x : ℤ) : ℤ) : ℝ) / ((m * r + β : ℕ) : ℝ) := by
      push_cast; ring
    rw [e]
    exact nid_div_ge hDpos _ m (fun n => lowerA_int hS (-u) v hD x hx1 hxN hxr n)
  · have e : ((m : ℝ) * r) * (((-u : ℤ) : ℝ) / ((m * r + β : ℕ) : ℝ)) =
        (((-u) * ((m * r : ℕ) : ℤ) : ℤ) : ℝ) / ((m * r + β : ℕ) : ℝ) := by
      push_cast; ring
    rw [e]
    exact nid_div_ge hDpos _ m (fun n => lowerA_speed hS (-u) v hD n)

end Gap
end Sext6
end LRSpectrumFull
