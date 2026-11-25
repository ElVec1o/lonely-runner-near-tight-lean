import LRSpectrumFull.Sext6.Gap.Q81T3

/-!
# Q8.1, Theorem T (necessity of the rescue windows) for the two-entry family  [2026-11-25]

Source: the accompanying notes on Zhang's Question 8.1 section 4.
`V = v2Fam k r1 r2 m1 m2 = ([1,N] \ {r1, r2}) ∪ {m1 r1, m2 r2}`, `N = k + 1`, `4 ≤ N`, `N < 2 r1`, `r1 < r2 ≤ N`,
tight meaning `ML V ≤ 1/(N+1)`.  For a modulus `r_i` with own multiplier `m_i` (`m_i + 1 ≤ N`) and every failing unit `b`
(`gcd(b, r_i) = 1`, `N + 1 - r_i ≤ b ≤ N`, `b < m_i (N + 1 - r_i)`), the other inserted speed `p = w_j` rescues `b`:
`z b ≡ p (mod r_i)`, `m_i (z A - r_i) ≤ p`, `(A - r_i) p ≤ b (z A + r_i)`, `A = N + 1`, `z ≥ 0`.
* `rescue_necessary_1`, `rescue_necessary_2`, `theoremT_only_if`.
Not formalised: the converse direction (every failing unit rescued => tight), which needs the Dirichlet reduction and the
class structure at the level `1/(N+1)` (the notes, Steps 1-4 of Theorem T).  `gcd(r1, r2) > 1` is not needed here.
No `sorry`, no `axiom`.

Convention: `N = k + 1` is the number of speeds of the vector `v : Fin (k+1) → ℤ`. Speeds are the moving runners; the runner at rest is not counted, so a vector of `N` speeds means `N + 1` runners and the Lonely Runner value is `1/(N+1)`.
Hypotheses: those of the individual statements (numerical bounds, structural conditions and, where named in the list above, window predicates such as `PrimeWin`, `CopWin`, `PrimeWindow7`, which later modules discharge for explicit ranges). The unproved predicates `DusartPi`, `LRCHyp`, `CopWinHyp` are not hypotheses of any statement in this module.
Axiom audit: covered by `Axioms22` (`#print axioms`; declarations not printed there are bricks of printed ones, so their axioms are bounded by the printed lines).
-/

namespace LRSpectrumFull
namespace Sext6
namespace Gap

theorem bezout_class {M b : ℕ} (hb : Nat.Coprime b M) :
    ∃ c k' : ℤ, (b : ℤ) * c + 1 = (M : ℤ) * k' ∧ IsCoprime (M : ℤ) c := by
  obtain ⟨u, v, huv⟩ : IsCoprime (b : ℤ) (M : ℤ) := Nat.isCoprime_iff_coprime.mpr hb
  exact ⟨-u, v, by linear_combination (-1 : ℤ) * huv, ⟨v, -(b : ℤ), by linear_combination huv⟩⟩

theorem rescue_necessary_1 {k N r1 r2 m1 m2 : ℕ} (hk : k + 1 = N) (hN4 : 4 ≤ N)
    (hr1 : N < 2 * r1) (h12 : r1 < r2) (h2N : r2 ≤ N) (hm1 : 2 ≤ m1) (hm2 : 2 ≤ m2)
    (hm1N : m1 + 1 ≤ N) (hcov : ML (v2Fam k r1 r2 m1 m2) ≤ 1 / ((N : ℝ) + 1))
    (b : ℕ) (hb : Nat.Coprime b r1) (hb1 : N + 1 ≤ b + r1) (hbN : b ≤ N)
    (hbm : b < m1 * (N + 1 - r1)) :
    ∃ z : ℕ, z * b ≡ m2 * r2 [MOD r1] ∧ m1 * (z * (N + 1)) ≤ m2 * r2 + m1 * r1 ∧
      (N + 1 - r1) * (m2 * r2) ≤ b * (z * (N + 1) + r1) := by
  obtain ⟨c, k', hbc, hcop⟩ := bezout_class hb
  refine rescue_core (N := N) (M := r1) (m := m1) (p := m2 * r2) (b := b) c k' (by omega) hr1
    (by omega) hm1 hm1N (Nat.mul_pos (by omega) (by omega)) hN4 hcop hbc hb1 hbN hbm ?_
  intro η _ _
  obtain ⟨i, hi⟩ := exists_close_of_ML_le (v2Fam k r1 r2 m1 m2) (1 / ((N : ℝ) + 1)) hcov
    (((c : ℝ) + η) / r1)
  by_cases hi1 : (i : ℕ) + 1 = r1
  · rw [v2Fam_at1 i hi1] at hi
    right; left
    simpa using hi
  · by_cases hi2 : (i : ℕ) + 1 = r2
    · rw [v2Fam_at2 i hi1 hi2] at hi
      right; right
      simpa using hi
    · rw [v2Fam_at0 i hi1 hi2] at hi
      left
      have hiN : (i : ℕ) < k + 1 := i.isLt
      exact ⟨(i : ℕ) + 1, by omega, by omega, hi1, by simpa using hi⟩

theorem rescue_necessary_2 {k N r1 r2 m1 m2 : ℕ} (hk : k + 1 = N) (hN4 : 4 ≤ N)
    (hr1 : N < 2 * r1) (h12 : r1 < r2) (h2N : r2 ≤ N) (hm1 : 2 ≤ m1) (hm2 : 2 ≤ m2)
    (hm2N : m2 + 1 ≤ N) (hcov : ML (v2Fam k r1 r2 m1 m2) ≤ 1 / ((N : ℝ) + 1))
    (b : ℕ) (hb : Nat.Coprime b r2) (hb1 : N + 1 ≤ b + r2) (hbN : b ≤ N)
    (hbm : b < m2 * (N + 1 - r2)) :
    ∃ z : ℕ, z * b ≡ m1 * r1 [MOD r2] ∧ m2 * (z * (N + 1)) ≤ m1 * r1 + m2 * r2 ∧
      (N + 1 - r2) * (m1 * r1) ≤ b * (z * (N + 1) + r2) := by
  obtain ⟨c, k', hbc, hcop⟩ := bezout_class hb
  refine rescue_core (N := N) (M := r2) (m := m2) (p := m1 * r1) (b := b) c k' h2N (by omega)
    (by omega) hm2 hm2N (Nat.mul_pos (by omega) (by omega)) hN4 hcop hbc hb1 hbN hbm ?_
  intro η _ _
  obtain ⟨i, hi⟩ := exists_close_of_ML_le (v2Fam k r1 r2 m1 m2) (1 / ((N : ℝ) + 1)) hcov
    (((c : ℝ) + η) / r2)
  by_cases hi1 : (i : ℕ) + 1 = r1
  · rw [v2Fam_at1 i hi1] at hi
    right; right
    simpa using hi
  · by_cases hi2 : (i : ℕ) + 1 = r2
    · rw [v2Fam_at2 i hi1 hi2] at hi
      right; left
      simpa using hi
    · rw [v2Fam_at0 i hi1 hi2] at hi
      left
      have hiN : (i : ℕ) < k + 1 := i.isLt
      exact ⟨(i : ℕ) + 1, by omega, by omega, hi2, by simpa using hi⟩

/-- **Theorem T, "only if"**: if `V` is tight, every failing unit of either entry is rescued by the other inserted speed. -/
theorem theoremT_only_if {k N r1 r2 m1 m2 : ℕ} (hk : k + 1 = N) (hN4 : 4 ≤ N)
    (hr1 : N < 2 * r1) (h12 : r1 < r2) (h2N : r2 ≤ N) (hm1 : 2 ≤ m1) (hm2 : 2 ≤ m2)
    (hm1N : m1 + 1 ≤ N) (hm2N : m2 + 1 ≤ N) (hcov : ML (v2Fam k r1 r2 m1 m2) ≤ 1 / ((N : ℝ) + 1)) :
    (∀ b : ℕ, Nat.Coprime b r1 → N + 1 ≤ b + r1 → b ≤ N → b < m1 * (N + 1 - r1) →
      ∃ z : ℕ, z * b ≡ m2 * r2 [MOD r1] ∧ m1 * (z * (N + 1)) ≤ m2 * r2 + m1 * r1 ∧
        (N + 1 - r1) * (m2 * r2) ≤ b * (z * (N + 1) + r1)) ∧
    (∀ b : ℕ, Nat.Coprime b r2 → N + 1 ≤ b + r2 → b ≤ N → b < m2 * (N + 1 - r2) →
      ∃ z : ℕ, z * b ≡ m1 * r1 [MOD r2] ∧ m2 * (z * (N + 1)) ≤ m1 * r1 + m2 * r2 ∧
        (N + 1 - r2) * (m1 * r1) ≤ b * (z * (N + 1) + r2)) :=
  ⟨fun b hb hb1 hbN hbm => rescue_necessary_1 hk hN4 hr1 h12 h2N hm1 hm2 hm1N hcov b hb hb1 hbN hbm,
   fun b hb hb1 hbN hbm => rescue_necessary_2 hk hN4 hr1 h12 h2N hm1 hm2 hm2N hcov b hb hb1 hbN hbm⟩

end Gap
end Sext6
end LRSpectrumFull
