import LRSpectrumFull.Sext6.Gap.MultiLower

/-!
# Multi-entry value theorem, tight regime without the extra divisibility hypothesis  [2026-11-24]

If every entry satisfies `m r / (m r * r + β r) ≤ 1/(N+1)` (equivalently `m s ≤ β`, the Goddyn-Wong condition (9)),
then `(N+1) ∤ m r * r` holds automatically: `m s ≤ β ≤ N` and `m r * r = m (N+1) - m s`.
So `ML v = 1/(N+1)` follows from the pairwise non-coprimality alone.
No `sorry`, no `axiom`.

Convention: `N` is the size of the ambient interval `[1,N]`; the speed vector `v : Fin (k+1) → ℤ` is a finite family (repetitions allowed) and `k`, `N` are independent parameters of the generic statements. Speeds are the moving runners; the runner at rest is not counted, so a vector of `N` speeds means `N + 1` runners and the Lonely Runner value is `1/(N+1)`.
Hypotheses: those of the individual statements (numerical bounds, structural conditions and, where named in the list above, window predicates such as `PrimeWin`, `CopWin`, `PrimeWindow7`, which later modules discharge for explicit ranges). The unproved predicates `DusartPi`, `LRCHyp`, `CopWinHyp` are not hypotheses of any statement in this module.
Axiom audit: covered by `MultiAxioms` (`#print axioms`; declarations not printed there are bricks of printed ones, so their axioms are bounded by the printed lines).
-/

namespace LRSpectrumFull
namespace Sext6
namespace Gap

theorem not_dvd_of_tight {N r m β : ℕ} (hS : Spec N r m β)
    (ht : (m : ℝ) / ((m * r + β : ℕ) : ℝ) ≤ 1 / ((N : ℝ) + 1)) :
    ¬ (((N + 1 : ℕ) : ℤ) ∣ ((m * r : ℕ) : ℤ)) := by
  have hbpos := hS.beta_pos
  have hrr := hS.two_le_r
  have hbN := hS.beta_le_N
  have hr2 := hS.hr2
  have hm2 := hS.hm
  have hNR : (0 : ℝ) < (N : ℝ) + 1 := by positivity
  have hDR : (0 : ℝ) < ((m * r + β : ℕ) : ℝ) := by
    have : 0 < m * r + β := by omega
    exact_mod_cast this
  rw [div_le_div_iff₀ hDR hNR] at ht
  have h1 : m * (N + 1) ≤ m * r + β := by
    have : (m : ℝ) * ((N : ℝ) + 1) ≤ ((m * r + β : ℕ) : ℝ) := by linarith
    exact_mod_cast this
  intro hd
  obtain ⟨q, hq⟩ := hd
  have hmul : (m : ℤ) * ((N : ℤ) + 1) = ((m * r : ℕ) : ℤ) + (m : ℤ) * ((N : ℤ) + 1 - r) := by
    push_cast; ring
  have hsr : (1 : ℤ) ≤ (N : ℤ) + 1 - r := by omega
  have hms : (1 : ℤ) ≤ (m : ℤ) * ((N : ℤ) + 1 - r) := by
    have : (1 : ℤ) ≤ m := by exact_mod_cast (by omega : 1 ≤ m)
    nlinarith
  have hmsb : (m : ℤ) * ((N : ℤ) + 1 - r) ≤ β := by
    have h1' : (m : ℤ) * ((N : ℤ) + 1) ≤ (m : ℤ) * r + β := by exact_mod_cast h1
    nlinarith
  have hbN' : (β : ℤ) ≤ N := by exact_mod_cast hbN
  have hK : (m : ℤ) * ((N : ℤ) + 1 - r) = ((N : ℤ) + 1) * ((m : ℤ) - q) := by
    push_cast at hq ⊢
    linear_combination (-1 : ℤ) * hq
  rcases le_or_gt ((m : ℤ) - q) 0 with h | h
  · nlinarith
  · nlinarith

/-- Tight regime: pairwise non-coprime entries with `m r / (m r * r + β r) ≤ 1/(N+1)` give `ML v = 1/(N+1)`. -/
theorem multi_value_tight_auto {k N : ℕ} (hN : 2 ≤ N) (R : Finset ℕ) (m β : ℕ → ℕ)
    (hS : ∀ r ∈ R, Spec N r (m r) (β r))
    (hG : ∀ r ∈ R, ∀ r' ∈ R, r' ≠ r → ¬ Nat.Coprime r' r)
    (v : Fin (k + 1) → ℤ)
    (hret : ∀ x : ℕ, 1 ≤ x → x ≤ N → x ∉ R → ∃ i, v i = (x : ℤ))
    (hnew : ∀ r ∈ R, ∃ i, v i = ((m r * r : ℕ) : ℤ))
    (hwith : WithinMulti N R m v)
    (htight : ∀ r ∈ R, (m r : ℝ) / ((m r * r + β r : ℕ) : ℝ) ≤ 1 / ((N : ℝ) + 1)) :
    ML v = 1 / ((N : ℝ) + 1) :=
  multi_value_tight hN R m β hS hG v hret hnew hwith htight
    (fun r' hr' => not_dvd_of_tight (hS r' hr') (htight r' hr'))

end Gap
end Sext6
end LRSpectrumFull
