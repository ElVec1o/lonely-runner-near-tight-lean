import LRSpectrumFull.Sext6.Gap.MultiNecCore
import LRSpectrumFull.Delta2Boundary

/-!
# Multi-entry value theorem: necessity half of M3(b)  [2026-11-25]

Setting of `multi_ML_le`: `R` a finite set of entries, each `N/2 < r ≤ N`, pairwise non-coprime (`hG`),
`m r ≥ 2`, `β r` the least integer `≥ N+1-r` coprime to `r` (through `Spec`), `v` a speed vector containing
`[1,N] \ R` and every `m r * r`.

* `mnec_at`          : sign-normalised form (the offset `η ∈ [0,1/(N+1)]` at the entry `r`).
* `multi_ML_nec`     : if `τ > 1/(N+1)`, every `m r / (m r * r + β r) ≤ τ`, and `ML v = τ`, then some `r0 ∈ R`
                       has `τ = m r0 / (m r0 * r0 + β r0)` and, with `a r0 + 1 = c (m r0 * r0 + β r0)`,
                       every other new speed `m r' * r'` is at distance `≥ m r0 / D` from `a/D` modulo integers
                       (the residue hypothesis `hW` of `multi_ML_ge_B`).
* `multi_ML_eq_iff`  : with `WithinMulti`, `ML v = τ` iff such an `r0` exists (necessity above, sufficiency
                       `multi_value_wit`).
No `sorry`, no `axiom`.  Attainment of `ML` is `le_ML_iff_exists_far` (`Delta2Boundary`).

Convention: `N` is the size of the ambient interval `[1,N]`; the speed vector `v : Fin (k+1) → ℤ` is a finite family (repetitions allowed) and `k`, `N` are independent parameters of the generic statements. Speeds are the moving runners; the runner at rest is not counted, so a vector of `N` speeds means `N + 1` runners and the Lonely Runner value is `1/(N+1)`.
Axiom audit: covered by `Axioms23`.
-/

namespace LRSpectrumFull
namespace Sext6
namespace Gap

theorem mnec_at {N r : ℕ} (R : Finset ℕ) (m β : ℕ → ℕ) (hR : r ∈ R)
    (hRlt : ∀ r' ∈ R, N < 2 * r') (hG : ∀ r' ∈ R, r' ≠ r → ¬ Nat.Coprime r' r)
    (hS : Spec N r (m r) (β r)) (τ : ℝ)
    (hτ1 : 1 / ((N : ℝ) + 1) < τ) (hτ2 : (m r : ℝ) / ((m r * r + β r : ℕ) : ℝ) ≤ τ)
    (t : ℝ) (c : ℤ) (η : ℝ) (hrt : (r : ℝ) * t = c + η) (hη0 : 0 ≤ η)
    (hη1 : η ≤ 1 / ((N : ℝ) + 1))
    (hx : ∀ x : ℕ, 1 ≤ x → x ≤ N → x ∉ R → τ ≤ nearestIntDist ((x : ℝ) * t))
    (hnw : ∀ r' ∈ R, τ ≤ nearestIntDist ((((m r' * r' : ℕ) : ℤ) : ℝ) * t)) :
    τ = (m r : ℝ) / ((m r * r + β r : ℕ) : ℝ) ∧
      ∃ a c' : ℤ, a * r + 1 = c' * ((m r * r + β r : ℕ) : ℤ) ∧
        ∀ r' ∈ R, r' ≠ r → ∀ n : ℤ,
          (m r : ℤ) ≤ |a * ((m r' * r' : ℕ) : ℤ) - n * ((m r * r + β r : ℕ) : ℤ)| := by
  have hm' := hnw r hR
  push_cast at hm'
  obtain ⟨hτeq, hηeq, k, hk⟩ := mnec_core R hRlt hG hS τ hτ1 hτ2 t c η hrt hη0 hη1 hx hm'
  refine ⟨hτeq, -(c * (m r : ℤ) + k), -c, ?_, ?_⟩
  · push_cast
    linear_combination hk
  · intro r' hr' hne n
    have hrr := hS.two_le_r
    have hbpos := hS.beta_pos
    have hmpos := hS.hm
    have hrpos : (0 : ℝ) < r := by exact_mod_cast (by omega : 0 < r)
    have hDnat : 0 < m r * r + β r := by omega
    have hDpos : (0 : ℝ) < ((m r * r + β r : ℕ) : ℝ) := by exact_mod_cast hDnat
    have hkR : (c : ℝ) * (β r) + 1 = r * k := by exact_mod_cast hk
    have hDeq : ((m r * r + β r : ℕ) : ℝ) = (m r : ℝ) * r + β r := by push_cast; ring
    have hdη : ((m r * r + β r : ℕ) : ℝ) * η = 1 := by
      rw [hηeq]
      exact mul_one_div_cancel hDpos.ne'
    have hDt : ((m r * r + β r : ℕ) : ℝ) * t = c * (m r : ℝ) + k := by
      have h0 : (r : ℝ) * (((m r * r + β r : ℕ) : ℝ) * t - (c * (m r : ℝ) + k)) = 0 := by
        linear_combination ((m r * r + β r : ℕ) : ℝ) * hrt + hdη + hkR + (c : ℝ) * hDeq
      rcases mul_eq_zero.mp h0 with h | h
      · exact absurd h hrpos.ne'
      · linarith
    have hw' := hnw r' hr'
    have e : (((m r' * r' : ℕ) : ℤ) : ℝ) * t =
        ((((c * (m r : ℤ) + k) * ((m r' * r' : ℕ) : ℤ) : ℤ)) : ℝ) / ((m r * r + β r : ℕ) : ℝ) := by
      rw [eq_div_iff hDpos.ne']
      have hz : ((((c * (m r : ℤ) + k) * ((m r' * r' : ℕ) : ℤ) : ℤ)) : ℝ) =
          (c * (m r : ℝ) + k) * ((((m r' * r' : ℕ) : ℤ) : ℝ)) := by
        push_cast; ring
      rw [hz]
      linear_combination ((((m r' * r' : ℕ) : ℤ) : ℝ)) * hDt
    have hfar : (m r : ℝ) / ((m r * r + β r : ℕ) : ℝ) ≤
        nearestIntDist ((((c * (m r : ℤ) + k) * ((m r' * r' : ℕ) : ℤ) : ℤ) : ℝ) /
          ((m r * r + β r : ℕ) : ℝ)) := by
      rw [← e, ← hτeq]
      exact hw'
    have h9 := int_far_of_nid hDnat _ (m r) hfar (-n)
    have e2 : -(c * (m r : ℤ) + k) * ((m r' * r' : ℕ) : ℤ) - n * ((m r * r + β r : ℕ) : ℤ) =
        -((c * (m r : ℤ) + k) * ((m r' * r' : ℕ) : ℤ) - (-n) * ((m r * r + β r : ℕ) : ℤ)) := by
      ring
    rw [e2, abs_neg]
    exact h9

theorem multi_ML_nec {k N : ℕ} (hN : 2 ≤ N) (R : Finset ℕ) (m β : ℕ → ℕ)
    (hS : ∀ r ∈ R, Spec N r (m r) (β r))
    (hG : ∀ r ∈ R, ∀ r' ∈ R, r' ≠ r → ¬ Nat.Coprime r' r)
    (v : Fin (k + 1) → ℤ)
    (hret : ∀ x : ℕ, 1 ≤ x → x ≤ N → x ∉ R → ∃ i, v i = (x : ℤ))
    (hnew : ∀ r ∈ R, ∃ i, v i = ((m r * r : ℕ) : ℤ))
    (τ : ℝ) (h1 : 1 / ((N : ℝ) + 1) < τ)
    (h2 : ∀ r ∈ R, (m r : ℝ) / ((m r * r + β r : ℕ) : ℝ) ≤ τ)
    (hML : ML v = τ) :
    ∃ r0 ∈ R, τ = (m r0 : ℝ) / ((m r0 * r0 + β r0 : ℕ) : ℝ) ∧
      ∃ a c : ℤ, a * r0 + 1 = c * ((m r0 * r0 + β r0 : ℕ) : ℤ) ∧
        ∀ r' ∈ R, r' ≠ r0 → ∀ n : ℤ,
          (m r0 : ℤ) ≤ |a * ((m r' * r' : ℕ) : ℤ) - n * ((m r0 * r0 + β r0 : ℕ) : ℤ)| := by
  have hRlt : ∀ r' ∈ R, N < 2 * r' := fun r' h => (hS r' h).hr1
  obtain ⟨t, ht⟩ := (le_ML_iff_exists_far v τ).mp hML.ge
  have hx : ∀ x : ℕ, 1 ≤ x → x ≤ N → x ∉ R → τ ≤ nearestIntDist ((x : ℝ) * t) := by
    intro x hx1 hxN hxR
    obtain ⟨i, hi⟩ := hret x hx1 hxN hxR
    have := ht i
    have e : ((v i : ℤ) : ℝ) = (x : ℝ) := by rw [hi]; norm_cast
    rwa [e] at this
  have hnw : ∀ r' ∈ R, τ ≤ nearestIntDist ((((m r' * r' : ℕ) : ℤ) : ℝ) * t) := by
    intro r' hr'
    obtain ⟨i, hi⟩ := hnew r' hr'
    have := ht i
    rwa [hi] at this
  obtain ⟨j, q, hq0, hqN, hqd⟩ := Real.exists_int_int_abs_mul_sub_le t (n := N) (by omega)
  obtain ⟨qn, hqn⟩ : ∃ qn : ℕ, (qn : ℤ) = q := ⟨q.toNat, Int.toNat_of_nonneg (by omega)⟩
  have hqnR : (qn : ℝ) = (q : ℝ) := by exact_mod_cast hqn
  have hqnN : qn ≤ N := by
    have : (qn : ℤ) ≤ N := by rw [hqn]; exact_mod_cast hqN
    exact_mod_cast this
  have hqR : qn ∈ R := by
    by_contra hne
    have h3 := hx qn (by omega) hqnN hne
    rw [hqnR] at h3
    have h4 := nearestIntDist_le_dist ((q : ℝ) * t) j
    linarith
  have hSq := hS qn hqR
  have hGq := hG qn hqR
  have hq' : (q : ℝ) = qn := hqnR.symm
  rw [hq'] at hqd
  obtain ⟨hl, hu⟩ := abs_le.mp hqd
  rcases le_or_gt 0 ((qn : ℝ) * t - j) with hη | hη
  · exact ⟨qn, hqR, mnec_at R m β hqR hRlt hGq hSq τ h1 (h2 qn hqR) t j ((qn : ℝ) * t - j)
      (by ring) hη hu hx hnw⟩
  · refine ⟨qn, hqR, mnec_at R m β hqR hRlt hGq hSq τ h1 (h2 qn hqR) (-t) (-j)
      (-((qn : ℝ) * t - j)) (by push_cast; ring) (by linarith) (by linarith) ?_ ?_⟩
    · intro x hx1 hxN hxR
      have := hx x hx1 hxN hxR
      rwa [show (x : ℝ) * (-t) = -((x : ℝ) * t) by ring, nearestIntDist_neg]
    · intro r' hr'
      have := hnw r' hr'
      rwa [show (((m r' * r' : ℕ) : ℤ) : ℝ) * (-t) = -((((m r' * r' : ℕ) : ℤ) : ℝ) * t) by ring,
        nearestIntDist_neg]

/-- With `WithinMulti`: `ML v = τ` (for `τ > 1/(N+1)` bounding every `m r / D r`) iff some `r0` realises it
with the residue test.  `⟸` is `multi_value_wit`, `⟹` is `multi_ML_nec`. -/
theorem multi_ML_eq_iff {k N : ℕ} (hN : 2 ≤ N) (R : Finset ℕ) (m β : ℕ → ℕ)
    (hS : ∀ r ∈ R, Spec N r (m r) (β r))
    (hG : ∀ r ∈ R, ∀ r' ∈ R, r' ≠ r → ¬ Nat.Coprime r' r)
    (v : Fin (k + 1) → ℤ)
    (hret : ∀ x : ℕ, 1 ≤ x → x ≤ N → x ∉ R → ∃ i, v i = (x : ℤ))
    (hnew : ∀ r ∈ R, ∃ i, v i = ((m r * r : ℕ) : ℤ))
    (hwith : WithinMulti N R m v)
    (τ : ℝ) (h1 : 1 / ((N : ℝ) + 1) < τ)
    (h2 : ∀ r ∈ R, (m r : ℝ) / ((m r * r + β r : ℕ) : ℝ) ≤ τ) :
    ML v = τ ↔
      ∃ r0 ∈ R, τ = (m r0 : ℝ) / ((m r0 * r0 + β r0 : ℕ) : ℝ) ∧
        ∃ a c : ℤ, a * r0 + 1 = c * ((m r0 * r0 + β r0 : ℕ) : ℤ) ∧
          ∀ r' ∈ R, r' ≠ r0 → ∀ n : ℤ,
            (m r0 : ℤ) ≤ |a * ((m r' * r' : ℕ) : ℤ) - n * ((m r0 * r0 + β r0 : ℕ) : ℤ)| := by
  constructor
  · intro hML
    exact multi_ML_nec hN R m β hS hG v hret hnew τ h1 h2 hML
  · rintro ⟨r0, hr0, hτ, a, c, hD, hW⟩
    rw [hτ]
    rw [hτ] at h1 h2
    exact multi_value_wit hN R m β hS hG v hret hnew hwith r0 hr0 h1.le h2 a c hD hW

end Gap
end Sext6
end LRSpectrumFull
