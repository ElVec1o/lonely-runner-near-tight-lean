import LRSpectrumFull.Sext6.Gap.Q81T1

/-!
# Q8.1, Theorem C for every `N ≥ 4`  [2026-11-25]

Assembly of `theoremC` (`Q81Core`: `m1 < r2`, `m2 < r1` or `N ≥ 10`), `theoremC_five_nine` (`Q81S3`) and `theoremC_four` (`Q81T1`).
Setting: `N = k + 1`, `N < 2 r1`, `r1 < r2 ≤ N`, `gcd(r1, r2) = 1`, `m1, m2 ≥ 2`, `V = v2Fam k r1 r2 m1 m2`.
No hypothesis on the size of `m1, m2` relative to `r2, r1`, and no restriction on `N`.
* `theoremC_ge5`  : `5 ≤ N` gives `1/N ≤ ML V`.
* `theoremC_unif` : `4 ≤ N` gives `2/(2N+1) ≤ ML V`.
* `theoremC_unif_cor` : `1/(N+1) < Gfam N ≤ 2/(2N+1) ≤ ML V`, so `V` is not tight and `ML V ≥ G(N)`.
No `sorry`, no `axiom`.

Convention: `N = k + 1` is the number of speeds of the vector `v : Fin (k+1) → ℤ`. Speeds are the moving runners; the runner at rest is not counted, so a vector of `N` speeds means `N + 1` runners and the Lonely Runner value is `1/(N+1)`.
Hypotheses: those of the individual statements (numerical bounds, structural conditions and, where named in the list above, window predicates such as `PrimeWin`, `CopWin`, `PrimeWindow7`, which later modules discharge for explicit ranges). The unproved predicates `DusartPi`, `LRCHyp`, `CopWinHyp` are not hypotheses of any statement in this module.
Axiom audit: covered by `Axioms22` (`#print axioms`; declarations not printed there are bricks of printed ones, so their axioms are bounded by the printed lines).
-/

namespace LRSpectrumFull
namespace Sext6
namespace Gap

/-- **Theorem C, all multipliers, `N ≥ 5`**: `1/N ≤ ML V`. -/
theorem theoremC_ge5 {k N r1 r2 m1 m2 : ℕ} (hk : k + 1 = N) (hN5 : 5 ≤ N) (hr1 : N < 2 * r1)
    (h12 : r1 < r2) (h2N : r2 ≤ N) (hcop : Nat.Coprime r1 r2) (hm1 : 2 ≤ m1) (hm2 : 2 ≤ m2) :
    1 / (N : ℝ) ≤ ML (v2Fam k r1 r2 m1 m2) := by
  by_cases hc : m1 + 1 ≤ r2 ∨ m2 + 1 ≤ r1 ∨ 10 ≤ N
  · exact theoremC hk hr1 h12 h2N hcop hm1 hm2 hc
  · push Not at hc
    exact theoremC_five_nine hk hN5 (by omega) hr1 h12 h2N hcop (by omega) (by omega)

/-- **Theorem C, uniform**: `2/(2N+1) ≤ ML V` for `N ≥ 4`. -/
theorem theoremC_unif {k N r1 r2 m1 m2 : ℕ} (hk : k + 1 = N) (hN4 : 4 ≤ N) (hr1 : N < 2 * r1)
    (h12 : r1 < r2) (h2N : r2 ≤ N) (hcop : Nat.Coprime r1 r2) (hm1 : 2 ≤ m1) (hm2 : 2 ≤ m2) :
    2 / (2 * (N : ℝ) + 1) ≤ ML (v2Fam k r1 r2 m1 m2) := by
  by_cases h5 : 5 ≤ N
  · have h := theoremC_ge5 hk h5 hr1 h12 h2N hcop hm1 hm2
    have hNpos : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
    have : 2 / (2 * (N : ℝ) + 1) ≤ 1 / (N : ℝ) := by
      rw [div_le_div_iff₀ (by positivity) hNpos]
      linarith
    exact this.trans h
  · have hN : N = 4 := by omega
    subst hN
    have hr13 : r1 = 3 := by omega
    have hr24 : r2 = 4 := by omega
    subst hr13
    subst hr24
    have hk3 : k = 3 := by omega
    subst hk3
    have h := theoremC_four hm1 hm2
    norm_num
    exact h

theorem theoremC_unif_cor {k N r1 r2 m1 m2 : ℕ} (hk : k + 1 = N) (hN4 : 4 ≤ N) (hr1 : N < 2 * r1)
    (h12 : r1 < r2) (h2N : r2 ≤ N) (hcop : Nat.Coprime r1 r2) (hm1 : 2 ≤ m1) (hm2 : 2 ≤ m2) :
    1 / ((N : ℝ) + 1) < Gfam N ∧ Gfam N ≤ 2 / (2 * (N : ℝ) + 1) ∧
      2 / (2 * (N : ℝ) + 1) ≤ ML (v2Fam k r1 r2 m1 m2) ∧
      1 / ((N : ℝ) + 1) < ML (v2Fam k r1 r2 m1 m2) := by
  have hN2 : 2 ≤ N := by omega
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hu := theoremC_unif hk hN4 hr1 h12 h2N hcop hm1 hm2
  have h1 := Gfam_gt hN2
  have h2 := Gfam_le_two hN2
  refine ⟨h1, h2, hu, ?_⟩
  have : 1 / ((N : ℝ) + 1) < 2 / (2 * (N : ℝ) + 1) := by
    rw [div_lt_div_iff₀ (by positivity) (by positivity)]
    linarith
  exact this.trans_le hu

end Gap
end Sext6
end LRSpectrumFull
