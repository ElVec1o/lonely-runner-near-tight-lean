import LRSpectrumFull.Sext6.Gap.LowerA

/-!
# Theorem V, Lemma 3 (lower bound at the time 1/(N+1))  [2026-11-24]

the accompanying notes section 3, Lemma 3: if `m s < β` (written `m (N+1) < m r + β`) then `ML ≥ 1/(N+1)`.

Convention: `N = k + 1` is the number of speeds of the vector `v : Fin (k+1) → ℤ`. Speeds are the moving runners; the runner at rest is not counted, so a vector of `N` speeds means `N + 1` runners and the Lonely Runner value is `1/(N+1)`.
Hypotheses: those of the individual statements (numerical bounds, structural conditions and, where named in the list above, window predicates such as `PrimeWin`, `CopWin`, `PrimeWindow7`, which later modules discharge for explicit ranges). The unproved predicates `DusartPi`, `LRCHyp`, `CopWinHyp` are not hypotheses of any statement in this module.
Axiom audit: covered by `Axioms` (first); every later audit module imports this module (`#print axioms`; declarations not printed there are bricks of printed ones, so their axioms are bounded by the printed lines).
-/

namespace LRSpectrumFull
namespace Sext6
namespace Gap

theorem far_of_not_dvd (D : ℕ) (z : ℤ) (h : ¬ (D : ℤ) ∣ z) :
    ∀ n : ℤ, (((1 : ℕ)) : ℤ) ≤ |z - n * D| := by
  intro n
  by_contra hc
  have hc' : |z - n * D| < 1 := by
    have := not_le.mp hc
    exact_mod_cast this
  obtain ⟨h1, h2⟩ := abs_lt.mp hc'
  apply h
  exact ⟨n, by linarith⟩

/-- Lemma 3. -/
theorem ML_ge_B {k N r m β : ℕ} (hk : k + 1 = N) (hS : Spec N r m β)
    (hlt : m * (N + 1) < m * r + β) : 1 / ((N : ℝ) + 1) ≤ ML (vFam k r m) := by
  have hbN := hS.beta_le_N
  have hr2 := hS.hr2
  have hm2 := hS.hm
  have hrr := hS.two_le_r
  have hpos : 0 < N + 1 := by omega
  have hc : 1 / ((N : ℝ) + 1) = ((1 : ℕ) : ℝ) / ((N + 1 : ℕ) : ℝ) := by push_cast; ring
  rw [hc]
  apply ML_ge_fam hk (by omega) hr2 _ (((1 : ℤ) : ℝ) / ((N + 1 : ℕ) : ℝ))
  · intro x hx1 hxN hxr
    have e : (x : ℝ) * (((1 : ℤ) : ℝ) / ((N + 1 : ℕ) : ℝ)) =
        ((((x : ℤ)) : ℤ) : ℝ) / ((N + 1 : ℕ) : ℝ) := by
      push_cast; ring
    rw [e]
    apply nid_div_ge hpos
    apply far_of_not_dvd
    intro hd
    have := Int.le_of_dvd (by exact_mod_cast hx1) hd
    have h3 : (x : ℤ) ≤ N := by exact_mod_cast hxN
    push_cast at this
    omega
  · have e : ((m : ℝ) * r) * (((1 : ℤ) : ℝ) / ((N + 1 : ℕ) : ℝ)) =
        ((((m * r : ℕ) : ℤ)) : ℝ) / ((N + 1 : ℕ) : ℝ) := by
      push_cast; ring
    rw [e]
    apply nid_div_ge hpos
    apply far_of_not_dvd
    intro hd
    have hd2 : ((N + 1 : ℕ) : ℤ) ∣ (m : ℤ) * ((N + 1 : ℕ) : ℤ) := ⟨m, by ring⟩
    have hd3 := dvd_sub hd2 hd
    have hw0 : (0 : ℤ) < (m : ℤ) * ((N + 1 : ℕ) : ℤ) - ((m * r : ℕ) : ℤ) := by
      push_cast
      have : (r : ℤ) < N + 1 := by exact_mod_cast (by omega : r < N + 1)
      have : (2 : ℤ) ≤ m := by exact_mod_cast hm2
      nlinarith
    have hw1 : (m : ℤ) * ((N + 1 : ℕ) : ℤ) - ((m * r : ℕ) : ℤ) < ((N + 1 : ℕ) : ℤ) := by
      have h1 : (m : ℤ) * ((N : ℤ) + 1) < (m : ℤ) * r + β := by exact_mod_cast hlt
      have h2 : (β : ℤ) ≤ N := by exact_mod_cast hbN
      push_cast
      linarith
    have := Int.le_of_dvd hw0 hd3
    omega

end Gap
end Sext6
end LRSpectrumFull
