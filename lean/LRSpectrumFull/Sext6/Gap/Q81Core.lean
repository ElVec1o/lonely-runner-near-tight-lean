import LRSpectrumFull.Sext6.Gap.Q81Aux
import LRSpectrumFull.Sext6.Gap.Q81Time
import LRSpectrumFull.Sext6.Gap.GAsym

/-!
# Q8.1, Theorem C (coprime two-entry modification, both removed speeds `> N/2`)  [2026-11-25]

Source: the accompanying notes on Zhang's Question 8.1 section 3 (Lemmas 3, 4) and the notes (part 2) section 3.

Setting: `N = k + 1`, `N < 2 r1`, `r1 < r2 ≤ N`, `gcd(r1, r2) = 1`, `m1, m2 ≥ 2`,
`V = v2Fam k r1 r2 m1 m2 = ([1,N] \ {r1, r2}) ∪ {m1 r1, m2 r2}`.

* `caseII_ML`  : `m1 ≥ r2`, `m2 ≥ r1`, `N ≥ 10` gives `1/N ≤ ML V` (counting lemma `good_eta_exists` + inequality (*)).
* `theoremC`   : `1/N ≤ ML V` whenever `m1 < r2` or `m2 < r1` or `N ≥ 10`.
* `theoremC_cor` : `1/(N+1) < G(N) ≤ 2/(2N+1) < 1/N ≤ ML V` (so V is not tight and ML exceeds G(N)).
NOT formalised here: `N = 5..9` with `m1 ≥ r2` and `m2 ≥ r1` (the notes: finite certificate, computed only).
No `sorry`, no `axiom`.

Convention: `N = k + 1` is the number of speeds of the vector `v : Fin (k+1) → ℤ`. Speeds are the moving runners; the runner at rest is not counted, so a vector of `N` speeds means `N + 1` runners and the Lonely Runner value is `1/(N+1)`.
Hypotheses: those of the individual statements (numerical bounds, structural conditions and, where named in the list above, window predicates such as `PrimeWin`, `CopWin`, `PrimeWindow7`, which later modules discharge for explicit ranges). The unproved predicates `DusartPi`, `LRCHyp`, `CopWinHyp` are not hypotheses of any statement in this module.
Axiom audit: covered by `Axioms8` (`#print axioms`; declarations not printed there are bricks of printed ones, so their axioms are bounded by the printed lines).
-/

namespace LRSpectrumFull
namespace Sext6
namespace Gap

/-- The two bad-set bounds are at most `4 τ E + 3 τ (1 + 2 τ)/ρ` once `a, α ≥ ρ`. -/
theorem hfin_aux {τ E ρ a α : ℝ} (hρ : 0 < ρ) (ha : ρ ≤ a) (hα : ρ ≤ α) (hτ : 0 < τ) :
    τ / a + (a * E + τ) * (2 * τ / a) + (α * E + 2 * τ + 1) * (2 * τ / α) ≤
      4 * τ * E + 3 * (τ * (1 + 2 * τ) * (1 / ρ)) := by
  have ha0 : 0 < a := lt_of_lt_of_le hρ ha
  have hα0 : 0 < α := lt_of_lt_of_le hρ hα
  have ha0' : a ≠ 0 := ha0.ne'
  have hα0' : α ≠ 0 := hα0.ne'
  have key : τ / a + (a * E + τ) * (2 * τ / a) + (α * E + 2 * τ + 1) * (2 * τ / α) =
      4 * τ * E + τ * (1 + 2 * τ) * (1 / a) + 2 * τ * (1 + 2 * τ) * (1 / α) := by
    field_simp
    try ring
  rw [key]
  have h1 : 1 / a ≤ 1 / ρ := one_div_le_one_div_of_le hρ ha
  have h2 : 1 / α ≤ 1 / ρ := one_div_le_one_div_of_le hρ hα
  have hc1 : 0 ≤ τ * (1 + 2 * τ) := by positivity
  have hc2 : 0 ≤ 2 * τ * (1 + 2 * τ) := by positivity
  have h3 := mul_le_mul_of_nonneg_left h1 hc1
  have h4 := mul_le_mul_of_nonneg_left h2 hc2
  have e3 : 3 * (τ * (1 + 2 * τ) * (1 / ρ)) =
      τ * (1 + 2 * τ) * (1 / ρ) + 2 * τ * (1 + 2 * τ) * (1 / ρ) := by ring
  rw [e3]
  linarith

/-- The inequality `(*)` of the accompanying notes Lemma 4 at `N = 10` (finite check over the coprime pairs). -/
theorem star10 (r1 r2 : ℕ) (h1 : 6 ≤ r1) (h12 : r1 < r2) (h2 : r2 ≤ 10) (hc : Nat.Coprime r1 r2) :
    (3 * 10 * (10 + 2) : ℝ) < (2 * 10 - (r2 : ℝ)) * (10 - 4) * (r1 : ℝ) := by
  have hr1 : r1 ≤ 9 := by omega
  interval_cases r1 <;> interval_cases r2 <;>
    first | exact absurd hc (by decide) | norm_num

/-- The inequality `(*)`: `3 N (N + 2) < (2 N - r2)(N - 4) r1` for `N ≥ 10`. -/
theorem star_ineq {N r1 r2 : ℕ} (hN : 10 ≤ N) (hr1 : N < 2 * r1) (h12 : r1 < r2) (h2N : r2 ≤ N)
    (hcop : Nat.Coprime r1 r2) :
    3 * (N : ℝ) * (N + 2) < (2 * N - (r2 : ℝ)) * (N - 4) * (r1 : ℝ) := by
  by_cases h10 : N = 10
  · subst h10
    have := star10 r1 r2 (by omega) h12 h2N hcop
    push_cast
    linarith
  · have hN11 : 11 ≤ N := by omega
    have hNR : (11 : ℝ) ≤ N := by exact_mod_cast hN11
    have hNpos : (0 : ℝ) < N := by linarith
    have hr2R : (r2 : ℝ) ≤ N := by exact_mod_cast h2N
    have hr1R : (N : ℝ) + 1 ≤ 2 * r1 := by exact_mod_cast hr1
    have hX : (N : ℝ) ≤ 2 * N - r2 := by linarith
    have hY0 : (0 : ℝ) ≤ (N : ℝ) - 4 := by linarith
    have hZ0 : (0 : ℝ) ≤ (r1 : ℝ) := Nat.cast_nonneg _
    have s1 : (N : ℝ) * (N - 4) * r1 ≤ (2 * N - r2) * (N - 4) * r1 :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hX hY0) hZ0
    have hNY : (0 : ℝ) ≤ (N : ℝ) * (N - 4) := mul_nonneg hNpos.le hY0
    have s2 : (N : ℝ) * (N - 4) * (((N : ℝ) + 1) / 2) ≤ (N : ℝ) * (N - 4) * r1 :=
      mul_le_mul_of_nonneg_left (by linarith) hNY
    have hq : (0 : ℝ) < (N : ℝ) ^ 2 - 9 * N - 16 := by nlinarith [sq_nonneg ((N : ℝ) - 11)]
    have s3 : 3 * (N : ℝ) * (N + 2) < (N : ℝ) * (N - 4) * (((N : ℝ) + 1) / 2) := by
      nlinarith [mul_pos hNpos hq]
    linarith

/-- **Case II** (`m1 ≥ r2`, `m2 ≥ r1`, `N ≥ 10`): `1/N ≤ ML`, by the counting lemma. -/
theorem caseII_ML {k N r1 r2 m1 m2 : ℕ} (hk : k + 1 = N) (hr1 : N < 2 * r1) (h12 : r1 < r2)
    (h2N : r2 ≤ N) (hcop : Nat.Coprime r1 r2) (hm1 : r2 ≤ m1) (hm2 : r1 ≤ m2) (hN10 : 10 ≤ N) :
    1 / (N : ℝ) ≤ ML (v2Fam k r1 r2 m1 m2) := by
  have hN2 : 2 ≤ N := by omega
  obtain ⟨u, w, huw⟩ : IsCoprime (r1 : ℤ) (r2 : ℤ) := Nat.isCoprime_iff_coprime.mpr hcop
  have hc : (r1 : ℤ) * (-u) + 1 = (r2 : ℤ) * w := by linear_combination (-1 : ℤ) * huw
  have hcopc : IsCoprime (r2 : ℤ) (-u) := ⟨w, -(r1 : ℤ), by linear_combination huw⟩
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hr1pos : (0 : ℝ) < r1 := by exact_mod_cast (by omega : 0 < r1)
  have hr2pos : (0 : ℝ) < r2 := by exact_mod_cast (by omega : 0 < r2)
  have hN0 : (N : ℝ) ≠ 0 := hNpos.ne'
  have hr10 : (r1 : ℝ) ≠ 0 := hr1pos.ne'
  have hr20 : (r2 : ℝ) ≠ 0 := hr2pos.ne'
  have hm1R : (r2 : ℝ) ≤ m1 := by exact_mod_cast hm1
  have hm2R : (r1 : ℝ) ≤ m2 := by exact_mod_cast hm2
  have hm1pos : (0 : ℝ) < m1 := lt_of_lt_of_le hr2pos hm1R
  have hm2pos : (0 : ℝ) < m2 := lt_of_lt_of_le hr1pos hm2R
  -- parameters of the counting lemma
  obtain ⟨E, hE⟩ : ∃ E : ℝ, E = (2 * (N : ℝ) - r2) / (N : ℝ) ^ 2 := ⟨_, rfl⟩
  have hr2N : (r2 : ℝ) ≤ N := by exact_mod_cast h2N
  have hEpos : 0 < E := by
    rw [hE]
    exact div_pos (by linarith) (pow_pos hNpos 2)
  have hNE : (N : ℝ) * E = 2 - (r2 : ℝ) / N := by
    rw [hE]
    field_simp
    try ring
  have hαρ : (r1 : ℝ) ≤ (m1 : ℝ) * r1 / r2 := by
    rw [le_div_iff₀ hr2pos]
    nlinarith [mul_le_mul_of_nonneg_left hm1R hr1pos.le]
  have hαpos : 0 < (m1 : ℝ) * r1 / r2 := lt_of_lt_of_le hr1pos hαρ
  have hτ0 : (0 : ℝ) < 1 / (N : ℝ) := one_div_pos.mpr hNpos
  have hN10R : (10 : ℝ) ≤ N := by exact_mod_cast hN10
  have hN1 : (1 : ℝ) ≤ N := by linarith
  have hτ1 : 1 / (N : ℝ) ≤ 1 := by
    rw [div_le_iff₀ hNpos]
    linarith
  have hstar := star_ineq hN10 hr1 h12 h2N hcop
  have hfin' := hfin_aux (τ := 1 / (N : ℝ)) (E := E) (ρ := (r1 : ℝ)) (a := (m2 : ℝ))
    (α := (m1 : ℝ) * r1 / r2) hr1pos hm2R hαρ hτ0
  have hgap : 4 * (1 / (N : ℝ)) * E + 3 * ((1 / (N : ℝ)) * (1 + 2 * (1 / (N : ℝ))) * (1 / (r1 : ℝ)))
      < E := by
    have hdiff : E - (4 * (1 / (N : ℝ)) * E +
        3 * ((1 / (N : ℝ)) * (1 + 2 * (1 / (N : ℝ))) * (1 / (r1 : ℝ)))) =
        ((2 * N - (r2 : ℝ)) * (N - 4) * r1 - 3 * N * (N + 2)) / ((N : ℝ) ^ 3 * r1) := by
      rw [hE]
      field_simp
      ring
    have : 0 < E - (4 * (1 / (N : ℝ)) * E +
        3 * ((1 / (N : ℝ)) * (1 + 2 * (1 / (N : ℝ))) * (1 / (r1 : ℝ)))) := by
      rw [hdiff]
      exact div_pos (by linarith) (mul_pos (pow_pos hNpos 3) hr1pos)
    linarith
  have hfin := lt_of_le_of_lt hfin' hgap
  obtain ⟨η, hη0, hηE, hA, hB⟩ := good_eta_exists (τ := 1 / (N : ℝ)) (E := E) (a := (m2 : ℝ))
    (α := (m1 : ℝ) * r1 / r2) (x0 := (m1 : ℝ) / r2) hτ0 hτ1 hEpos hm2pos hαpos hfin
  have hηN : (N : ℝ) * η ≤ 2 - (r2 : ℝ) / N := by
    rw [← hNE]
    exact mul_le_mul_of_nonneg_left hηE hNpos.le
  refine ML_v2Fam_ge hk (1 / (N : ℝ)) ((((-u : ℤ) : ℝ) + η) / (r2 : ℝ)) ?_ ?_ ?_
  · intro x hx1 hxN hxr1 hxr2
    exact retained_big hr1 h12 h2N (-u) w hc hcopc η hη0.le hηN x hx1 hxN hxr1 hxr2
  · rw [nid_mul_blocker m1 r1 r2 (-u) w η (by omega) hc]
    exact hB
  · rw [nid_mul_mod m2 r2 (-u) η (by omega)]
    exact hA

/-- **Theorem C** (coprime two-entry modification with both removed speeds `> N/2`):
`1/N ≤ ML V` whenever `m1 < r2`, or `m2 < r1`, or `N ≥ 10`. -/
theorem theoremC {k N r1 r2 m1 m2 : ℕ} (hk : k + 1 = N) (hr1 : N < 2 * r1) (h12 : r1 < r2)
    (h2N : r2 ≤ N) (hcop : Nat.Coprime r1 r2) (hm1 : 2 ≤ m1) (hm2 : 2 ≤ m2)
    (hcase : m1 + 1 ≤ r2 ∨ m2 + 1 ≤ r1 ∨ 10 ≤ N) :
    1 / (N : ℝ) ≤ ML (v2Fam k r1 r2 m1 m2) := by
  by_cases h1 : m1 + 1 ≤ r2
  · exact caseI_ML hk hr1 h12 h2N hcop hm1 hm2 h1
  · by_cases h2 : m2 + 1 ≤ r1
    · exact caseI'_ML hk hr1 h12 h2N hcop hm1 hm2 h2
    · have hN10 : 10 ≤ N := by
        rcases hcase with h | h | h
        · exact absurd h h1
        · exact absurd h h2
        · exact h
      exact caseII_ML hk hr1 h12 h2N hcop (by omega) (by omega) hN10

/-- **Corollary.**  Under the hypotheses of `theoremC`:
`1/(N+1) < G(N) ≤ 2/(2N+1) < 1/N ≤ ML V`.  In particular `V` is not tight and `ML V > G(N)`. -/
theorem theoremC_cor {k N r1 r2 m1 m2 : ℕ} (hk : k + 1 = N) (hr1 : N < 2 * r1) (h12 : r1 < r2)
    (h2N : r2 ≤ N) (hcop : Nat.Coprime r1 r2) (hm1 : 2 ≤ m1) (hm2 : 2 ≤ m2)
    (hcase : m1 + 1 ≤ r2 ∨ m2 + 1 ≤ r1 ∨ 10 ≤ N) :
    1 / ((N : ℝ) + 1) < Gfam N ∧ Gfam N ≤ 2 / (2 * (N : ℝ) + 1) ∧
      2 / (2 * (N : ℝ) + 1) < 1 / (N : ℝ) ∧ 1 / (N : ℝ) ≤ ML (v2Fam k r1 r2 m1 m2) := by
  have hN2 : 2 ≤ N := by omega
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  refine ⟨Gfam_gt hN2, Gfam_le_two hN2, ?_, theoremC hk hr1 h12 h2N hcop hm1 hm2 hcase⟩
  rw [div_lt_div_iff₀ (by positivity) hNpos]
  linarith

end Gap
end Sext6
end LRSpectrumFull
