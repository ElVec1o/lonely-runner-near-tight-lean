import LRSpectrumFull.Sext6.Gap.Value
import Mathlib.Data.Nat.Prime.Basic

/-!
# Theorem V: consequences (the accompanying notes section 8 (i), (iii))  [2026-11-24]

* `gNT k` : the non-tight infimum `g(N)`, `N = k + 1` speeds:
  `g(N) = inf { ML V : V an N-element set of positive integers, ML V > 1/(N+1) }`.
* Corollary A(b): `g(N) ≤ 2/(2N+1)` for all `N ≥ 2`.
* Corollary A(c): `N = r + 1`, `6 ∣ r`, `5 ∤ r` gives `g(N) ≤ 3/(3N+2) < 2/(2N+1)`.
* Instances: `N = 13` (`r = 12`, `m = 3`, value `3/41`), `N = 31` (`r = 30`, `m = 4`, value `4/127`),
  and the tight neighbours `(13,12,2)`, `(31,30,2)`, `(31,30,3)`.

Not formalised here: Theorem C (primorial liminf) and the closed form of `G(N)` as a minimum over `r`
(the accompanying notes section 8 (ii), (a)); `g(N) = G(N)` is a CONJECTURE in the accompanying notes and is not claimed.

Convention: `N = k + 1` is the number of speeds of the vector `v : Fin (k+1) → ℤ`. Speeds are the moving runners; the runner at rest is not counted, so a vector of `N` speeds means `N + 1` runners and the Lonely Runner value is `1/(N+1)`.
Hypotheses: those of the individual statements (numerical bounds, structural conditions and, where named in the list above, window predicates such as `PrimeWin`, `CopWin`, `PrimeWindow7`, which later modules discharge for explicit ranges). The unproved predicates `DusartPi`, `LRCHyp`, `CopWinHyp` are not hypotheses of any statement in this module.
Axiom audit: covered by `Axioms` (also reached through the imports of `Axioms2`, `Axioms3`, `Axioms8`) (`#print axioms`; declarations not printed there are bricks of printed ones, so their axioms are bounded by the printed lines).
-/

namespace LRSpectrumFull
namespace Sext6
namespace Gap

/-- Values of `ML` over `N = k+1`-element sets of distinct positive integers that are not tight. -/
def NonTightSet (k : ℕ) : Set ℝ :=
  {x | ∃ v : Fin (k + 1) → ℤ, Function.Injective v ∧ (∀ i, 0 < v i) ∧ ML v = x ∧
    1 / (((k + 1 : ℕ) : ℝ) + 1) < x}

/-- `g(N)` of the accompanying notes section 8, with `N = k + 1`. -/
noncomputable def gNT (k : ℕ) : ℝ := sInf (NonTightSet k)

theorem vFam_injective {k N r m : ℕ} (hk : k + 1 = N) (hr1 : N < 2 * r) (hr2 : r ≤ N)
    (hm : 2 ≤ m) : Function.Injective (vFam k r m) := by
  intro i j hij
  have hi := i.isLt
  have hj := j.isLt
  have hmr : 2 * r ≤ m * r := Nat.mul_le_mul_right r hm
  apply Fin.ext
  by_cases h1 : (i : ℕ) + 1 = r <;> by_cases h2 : (j : ℕ) + 1 = r
  · omega
  · simp only [vFam, if_pos h1, if_neg h2] at hij
    have : m * r = (j : ℕ) + 1 := by exact_mod_cast hij
    omega
  · simp only [vFam, if_neg h1, if_pos h2] at hij
    have : (i : ℕ) + 1 = m * r := by exact_mod_cast hij
    omega
  · simp only [vFam, if_neg h1, if_neg h2] at hij
    have : (i : ℕ) + 1 = (j : ℕ) + 1 := by exact_mod_cast hij
    omega

theorem vFam_pos {k r m : ℕ} (hr : 1 ≤ r) (hm : 1 ≤ m) (i : Fin (k + 1)) : 0 < vFam k r m i := by
  unfold vFam
  split_ifs
  · exact_mod_cast Nat.mul_pos (by omega) (by omega)
  · exact_mod_cast Nat.succ_pos _

/-- Any non-tight family member bounds `g(N)` from above. -/
theorem gNT_le {k N r m β : ℕ} (hk : k + 1 = N) (hS : Spec N r m β)
    (hlt : 1 / ((N : ℝ) + 1) < ML (vFam k r m)) : gNT k ≤ ML (vFam k r m) := by
  have hrr := hS.two_le_r
  apply csInf_le
  · exact ⟨0, by rintro x ⟨v, _, _, rfl, _⟩; exact ML_nonneg v⟩
  · refine ⟨vFam k r m, vFam_injective hk hS.hr1 hS.hr2 hS.hm, vFam_pos (by omega) (by have := hS.hm; omega),
      rfl, ?_⟩
    subst hk
    exact hlt

/-- Corollary A(b): the family `r = N`, `m = 2` has `ML = 2/(2N+1) > 1/(N+1)`; hence `g(N) ≤ 2/(2N+1)`. -/
theorem corA_b {k N : ℕ} (hk : k + 1 = N) (hN : 2 ≤ N) :
    ML (vFam k N 2) = 2 / (2 * (N : ℝ) + 1) ∧ 1 / ((N : ℝ) + 1) < 2 / (2 * (N : ℝ) + 1) ∧
      gNT k ≤ 2 / (2 * (N : ℝ) + 1) := by
  have hS : Spec N N 2 1 :=
    ⟨hN, by omega, le_refl _, le_refl _, by omega, Nat.coprime_one_left _, fun b hb _ => by omega⟩
  have hNR : (0 : ℝ) < (N : ℝ) := by exact_mod_cast (by omega : 0 < N)
  have hlt : 1 / ((N : ℝ) + 1) < 2 / (2 * (N : ℝ) + 1) := by
    rw [div_lt_div_iff₀ (by positivity) (by positivity)]
    linarith
  have hv : ML (vFam k N 2) = 2 / (2 * (N : ℝ) + 1) := by
    rw [value_formula_spec hk hS]
    push_cast
    exact max_eq_right hlt.le
  refine ⟨hv, hlt, ?_⟩
  rw [← hv]
  exact gNT_le hk hS (by rw [hv]; exact hlt)

/-- Corollary A(c): `N = r + 1`, `6 ∣ r`, `5 ∤ r`, `r > 0`: `β = 5`, `m = 3`, `ML = 3/(3N+2)`. -/
theorem spec_c {r : ℕ} (hr : 0 < r) (h6 : 6 ∣ r) (h5 : ¬ 5 ∣ r) : Spec (r + 1) r 3 5 := by
  have hr6 : 6 ≤ r := Nat.le_of_dvd hr h6
  have h2 : 2 ∣ r := dvd_trans (by norm_num) h6
  have h3 : 3 ∣ r := dvd_trans (by norm_num) h6
  refine ⟨by omega, by omega, by omega, by norm_num, by omega,
    (Nat.Prime.coprime_iff_not_dvd Nat.prime_five).mpr h5, ?_⟩
  intro b hb hcop
  by_contra hlt
  have hb2 : 2 ≤ b := by omega
  have hb5 : b < 5 := by omega
  interval_cases b
  · exact absurd (Nat.Coprime.eq_one_of_dvd hcop h2) (by norm_num)
  · exact absurd (Nat.Coprime.eq_one_of_dvd hcop h3) (by norm_num)
  · exact absurd (Nat.Coprime.eq_one_of_dvd (Nat.Coprime.coprime_dvd_left (by norm_num : 2 ∣ 4) hcop) h2)
      (by norm_num)

theorem corA_c {k N r : ℕ} (hk : k + 1 = N) (hNr : N = r + 1) (hr : 0 < r) (h6 : 6 ∣ r)
    (h5 : ¬ 5 ∣ r) :
    ML (vFam k r 3) = 3 / (3 * (N : ℝ) + 2) ∧ 1 / ((N : ℝ) + 1) < 3 / (3 * (N : ℝ) + 2) ∧
      3 / (3 * (N : ℝ) + 2) < 2 / (2 * (N : ℝ) + 1) ∧ gNT k ≤ 3 / (3 * (N : ℝ) + 2) := by
  have hS : Spec N r 3 5 := by rw [hNr]; exact spec_c hr h6 h5
  have hN' : (N : ℝ) = r + 1 := by exact_mod_cast hNr
  have hr6 : 6 ≤ r := Nat.le_of_dvd hr h6
  have hrR : (6 : ℝ) ≤ r := by exact_mod_cast hr6
  have hNpos : (0 : ℝ) < N := by rw [hN']; linarith
  have hlt : 1 / ((N : ℝ) + 1) < 3 / (3 * (N : ℝ) + 2) := by
    rw [div_lt_div_iff₀ (by positivity) (by positivity)]
    linarith
  have hlt2 : 3 / (3 * (N : ℝ) + 2) < 2 / (2 * (N : ℝ) + 1) := by
    rw [div_lt_div_iff₀ (by positivity) (by positivity)]
    linarith
  have e : 3 * (N : ℝ) + 2 = 3 * r + 5 := by rw [hN']; ring
  have hv : ML (vFam k r 3) = 3 / (3 * (N : ℝ) + 2) := by
    rw [value_formula_spec hk hS]
    push_cast
    rw [e]
    exact max_eq_right (by rw [← e]; exact hlt.le)
  refine ⟨hv, hlt, hlt2, ?_⟩
  rw [← hv]
  exact gNT_le hk hS (by rw [hv]; exact hlt)

/-! ### Instances -/

theorem spec_13 {m : ℕ} (hm : 2 ≤ m) : Spec 13 12 m 5 := by
  refine ⟨by norm_num, by norm_num, by norm_num, hm, by norm_num, by decide, ?_⟩
  intro b hb hcop
  by_contra hlt
  have hb2 : 2 ≤ b := by omega
  have hb5 : b < 5 := by omega
  interval_cases b <;> exact absurd hcop (by decide)

theorem spec_31 {m : ℕ} (hm : 2 ≤ m) : Spec 31 30 m 7 := by
  refine ⟨by norm_num, by norm_num, by norm_num, hm, by norm_num, by decide, ?_⟩
  intro b hb hcop
  by_contra hlt
  have hb2 : 2 ≤ b := by omega
  have hb7 : b < 7 := by omega
  interval_cases b <;> exact absurd hcop (by decide)

/-- `N = 13`, `r = 12`, `m = 3`: `ML = 3/41`, so `g(13) ≤ 3/41`. -/
theorem inst_13_12_3 : ML (vFam 12 12 3) = 3 / 41 ∧ gNT 12 ≤ 3 / 41 := by
  have hS := spec_13 (m := 3) (by norm_num)
  have hv : ML (vFam 12 12 3) = 3 / 41 := by
    rw [value_formula_spec (N := 13) rfl hS]
    norm_num [max_def]
  refine ⟨hv, ?_⟩
  rw [← hv]
  exact gNT_le (N := 13) rfl hS (by rw [hv]; norm_num)

/-- `N = 31`, `r = 30`, `m = 4`: `ML = 4/127`, so `g(31) ≤ 4/127`. -/
theorem inst_31_30_4 : ML (vFam 30 30 4) = 4 / 127 ∧ gNT 30 ≤ 4 / 127 := by
  have hS := spec_31 (m := 4) (by norm_num)
  have hv : ML (vFam 30 30 4) = 4 / 127 := by
    rw [value_formula_spec (N := 31) rfl hS]
    norm_num [max_def]
  refine ⟨hv, ?_⟩
  rw [← hv]
  exact gNT_le (N := 31) rfl hS (by rw [hv]; norm_num)

/-- Tight neighbours: `ML = 1/(N+1)`. -/
theorem inst_13_12_2 : ML (vFam 12 12 2) = 1 / 14 := by
  rw [value_formula_spec (N := 13) rfl (spec_13 (m := 2) (by norm_num))]
  norm_num [max_def]

theorem inst_31_30_2 : ML (vFam 30 30 2) = 1 / 32 := by
  rw [value_formula_spec (N := 31) rfl (spec_31 (m := 2) (by norm_num))]
  norm_num [max_def]

theorem inst_31_30_3 : ML (vFam 30 30 3) = 1 / 32 := by
  rw [value_formula_spec (N := 31) rfl (spec_31 (m := 3) (by norm_num))]
  norm_num [max_def]

end Gap
end Sext6
end LRSpectrumFull
