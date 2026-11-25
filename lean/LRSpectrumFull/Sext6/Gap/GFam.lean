import LRSpectrumFull.Sext6.Gap.Cor
import Mathlib.Order.ConditionallyCompleteLattice.Finset

/-!
# The family value `G(N)` and `g(N) ≤ G(N)`  [2026-11-24]

Source: the accompanying notes on Theorem V section 8 (i).

`N = k + 1` speeds.  For `N/2 < r ≤ N` let `s = N + 1 - r`, `β = betaFam N r`,
`PhiFam N r m = m / (m r + β)` (the Theorem V value in the non-tight case `β < m s`), and
`m_r = β / s + 1` the least `m` with `β < m s`.

* `Gfam N = min_{r ∈ rFam N} PhiFam N r (mFam N r)`  (defined as `sInf` of a finite nonempty set of reals).
* `mFam N r ∈ [2, N+1]`, and `β < m_r s`; every `m` with `β < m s` has `m ≥ m_r`.
* `PhiFam N r m` is monotone in `m`, so `Gfam N ≤ PhiFam N r m` for EVERY `r` in range and EVERY `m`
  with `β < m s` (the minimum over all `m` is attained at `m_r ≤ N + 1`).
* `gNT_le_Gfam`: `g(N) ≤ G(N)` for all `N ≥ 2`.
* `Gfam_attained`: `G(N) = PhiFam N r (mFam N r)` for some `r` in range.

`g(N) = G(N)` is an open CONJECTURE and is NOT claimed.   No `sorry`, no `axiom`.

Convention: `N = k + 1` is the number of speeds of the vector `v : Fin (k+1) → ℤ`. Speeds are the moving runners; the runner at rest is not counted, so a vector of `N` speeds means `N + 1` runners and the Lonely Runner value is `1/(N+1)`.
Hypotheses: those of the individual statements (numerical bounds, structural conditions and, where named in the list above, window predicates such as `PrimeWin`, `CopWin`, `PrimeWindow7`, which later modules discharge for explicit ranges). The unproved predicates `DusartPi`, `LRCHyp`, `CopWinHyp` are not hypotheses of any statement in this module.
Axiom audit: covered by `Axioms2` (also reached through the imports of `Axioms3`, `Axioms8`) (`#print axioms`; declarations not printed there are bricks of printed ones, so their axioms are bounded by the printed lines).
-/

namespace LRSpectrumFull
namespace Sext6
namespace Gap

/-- The range of `r`: `N/2 < r ≤ N`. -/
def rFam (N : ℕ) : Finset ℕ := (Finset.Icc 1 N).filter (fun r => N < 2 * r)

theorem mem_rFam {N r : ℕ} : r ∈ rFam N ↔ 1 ≤ r ∧ r ≤ N ∧ N < 2 * r := by
  simp only [rFam, Finset.mem_filter, Finset.mem_Icc, and_assoc]

/-- The least `m` with `β < m s`. -/
noncomputable def mFam (N r : ℕ) : ℕ := betaFam N r / sFam N r + 1

/-- The Theorem V value `m / (m r + β)` of the family member `(N, r, m)`. -/
noncomputable def PhiFam (N r m : ℕ) : ℝ := (m : ℝ) / ((m * r + betaFam N r : ℕ) : ℝ)

/-- `G(N)`: the minimum over `N/2 < r ≤ N` of the smallest non-tight family value in the column `r`. -/
noncomputable def Gfam (N : ℕ) : ℝ :=
  sInf ((fun r => PhiFam N r (mFam N r)) '' ((rFam N : Finset ℕ) : Set ℕ))

theorem PhiFam_nonneg (N r m : ℕ) : 0 ≤ PhiFam N r m := by
  unfold PhiFam; positivity

section fam

variable {N r : ℕ}

theorem rFam_spec (hN : 2 ≤ N) (hr : r ∈ rFam N) : Spec N r 2 (betaFam N r) := by
  obtain ⟨h1, h2, h3⟩ := mem_rFam.1 hr
  exact spec_betaFam hN h3 h2 le_rfl

theorem sFam_pos (hr : r ∈ rFam N) : 0 < sFam N r := by
  obtain ⟨h1, h2, h3⟩ := mem_rFam.1 hr
  unfold sFam; omega

theorem sFam_le_beta (hN : 2 ≤ N) (hr : r ∈ rFam N) : sFam N r ≤ betaFam N r := by
  have hS := rFam_spec hN hr
  have := hS.hb1
  unfold sFam; omega

theorem mFam_ge_two (hN : 2 ≤ N) (hr : r ∈ rFam N) : 2 ≤ mFam N r := by
  have h := Nat.div_pos (sFam_le_beta hN hr) (sFam_pos hr)
  unfold mFam; omega

theorem mFam_nonTight (hr : r ∈ rFam N) : betaFam N r < mFam N r * sFam N r := by
  have h := Nat.lt_mul_div_succ (betaFam N r) (sFam_pos hr)
  unfold mFam
  rw [mul_comm]
  exact h

theorem mFam_le (hN : 2 ≤ N) (hr : r ∈ rFam N) : mFam N r ≤ N + 1 := by
  have hS := rFam_spec hN hr
  have h1 := hS.beta_le_N
  have h2 : betaFam N r / sFam N r ≤ betaFam N r := Nat.div_le_self _ _
  unfold mFam; omega

theorem mFam_min (hr : r ∈ rFam N) {m : ℕ} (hnt : betaFam N r < m * sFam N r) : mFam N r ≤ m := by
  have h : betaFam N r < sFam N r * m := by rw [mul_comm]; exact hnt
  have := Nat.div_lt_of_lt_mul h
  unfold mFam; omega

theorem PhiFam_mono (hN : 2 ≤ N) (hr : r ∈ rFam N) {m m' : ℕ} (hm : 2 ≤ m) (hmm : m ≤ m') :
    PhiFam N r m ≤ PhiFam N r m' := by
  have hS := rFam_spec hN hr
  have hb := hS.beta_pos
  have hD : (0 : ℝ) < ((m * r + betaFam N r : ℕ) : ℝ) := by
    have : 0 < m * r + betaFam N r := by omega
    exact_mod_cast this
  have hD' : (0 : ℝ) < ((m' * r + betaFam N r : ℕ) : ℝ) := by
    have : 0 < m' * r + betaFam N r := by omega
    exact_mod_cast this
  unfold PhiFam
  rw [div_le_div_iff₀ hD hD']
  have hmm' : (m : ℝ) ≤ m' := by exact_mod_cast hmm
  have hb' : (0 : ℝ) ≤ betaFam N r := Nat.cast_nonneg _
  push_cast
  nlinarith [mul_nonneg (sub_nonneg.2 hmm') hb']

/-- Theorem V in the non-tight case: `ML = m / (m r + β) > 1/(N+1)` when `β < m s`. -/
theorem ML_nontight {k m β : ℕ} (hk : k + 1 = N) (hS : Spec N r m β) (hnt : β < m * (N + 1 - r)) :
    ML (vFam k r m) = (m : ℝ) / ((m * r + β : ℕ) : ℝ) ∧ 1 / ((N : ℝ) + 1) < ML (vFam k r m) := by
  have hbpos := hS.beta_pos
  have hrr := hS.two_le_r
  have hr2 := hS.hr2
  have hNR : (0 : ℝ) < (N : ℝ) + 1 := by positivity
  have hDR : (0 : ℝ) < ((m * r + β : ℕ) : ℝ) := by
    have : 0 < m * r + β := by omega
    exact_mod_cast this
  have hmul : m * (N + 1) = m * (N + 1 - r) + m * r := by
    have : N + 1 - r + r = N + 1 := by omega
    calc m * (N + 1) = m * (N + 1 - r + r) := by rw [this]
      _ = _ := by ring
  have hnat : m * r + β < m * (N + 1) := by omega
  have hreal : (((m * r + β : ℕ)) : ℝ) < (m : ℝ) * ((N : ℝ) + 1) := by exact_mod_cast hnat
  have hlt : 1 / ((N : ℝ) + 1) < (m : ℝ) / ((m * r + β : ℕ) : ℝ) := by
    rw [div_lt_div_iff₀ hNR hDR]
    linarith
  have hv : ML (vFam k r m) = (m : ℝ) / ((m * r + β : ℕ) : ℝ) := by
    rw [value_formula_spec hk hS]
    exact max_eq_right hlt.le
  exact ⟨hv, by rw [hv]; exact hlt⟩

/-- Every non-tight family member bounds `g(N)`: `g(N) ≤ m / (m r + β)` whenever `β < m s`. -/
theorem gNT_le_Phi {k : ℕ} (hk : k + 1 = N) (hN : 2 ≤ N) (hr : r ∈ rFam N) {m : ℕ}
    (hnt : betaFam N r < m * sFam N r) : gNT k ≤ PhiFam N r m := by
  obtain ⟨h1, h2, h3⟩ := mem_rFam.1 hr
  have hsβ := sFam_le_beta hN hr
  have hspos := sFam_pos hr
  have hm : 2 ≤ m := by
    by_contra hlt
    have : m = 0 ∨ m = 1 := by omega
    rcases this with rfl | rfl <;> simp at hnt <;> omega
  have hS := spec_betaFam hN h3 h2 hm
  obtain ⟨hv, hlt⟩ := ML_nontight hk hS hnt
  have := gNT_le hk hS hlt
  rw [hv] at this
  exact this

end fam

theorem rFam_nonempty {N : ℕ} (hN : 1 ≤ N) : N ∈ rFam N := mem_rFam.2 ⟨hN, le_rfl, by omega⟩

theorem Gfam_bddBelow (N : ℕ) :
    BddBelow ((fun r => PhiFam N r (mFam N r)) '' ((rFam N : Finset ℕ) : Set ℕ)) :=
  ⟨0, by rintro _ ⟨r', _, rfl⟩; exact PhiFam_nonneg _ _ _⟩

/-- `g(N) ≤ G(N)` for all `N = k + 1 ≥ 2`. -/
theorem gNT_le_Gfam {k N : ℕ} (hk : k + 1 = N) (hN : 2 ≤ N) : gNT k ≤ Gfam N := by
  unfold Gfam
  apply le_csInf
  · exact ⟨_, N, Finset.mem_coe.2 (rFam_nonempty (by omega)), rfl⟩
  · rintro _ ⟨r, hr, rfl⟩
    have hr' := Finset.mem_coe.1 hr
    exact gNT_le_Phi hk hN hr' (mFam_nonTight hr')

/-- The minimum over ALL `m` is attained at `m_r`: `G(N) ≤ PhiFam N r m` for every `r` in range and
every non-tight `m` (`β < m s`). -/
theorem Gfam_le_Phi {N r m : ℕ} (hN : 2 ≤ N) (hr : r ∈ rFam N)
    (hnt : betaFam N r < m * sFam N r) : Gfam N ≤ PhiFam N r m := by
  calc Gfam N ≤ PhiFam N r (mFam N r) :=
        csInf_le (Gfam_bddBelow N) ⟨r, Finset.mem_coe.2 hr, rfl⟩
    _ ≤ PhiFam N r m := PhiFam_mono hN hr (mFam_ge_two hN hr) (mFam_min hr hnt)

/-- `G(N)` is attained: `G(N) = PhiFam N r (mFam N r)` for some `r` with `N/2 < r ≤ N`, and
`2 ≤ mFam N r ≤ N + 1`. -/
theorem Gfam_attained {N : ℕ} (hN : 2 ≤ N) :
    ∃ r ∈ rFam N, Gfam N = PhiFam N r (mFam N r) ∧ 2 ≤ mFam N r ∧ mFam N r ≤ N + 1 := by
  have hne : ((fun r => PhiFam N r (mFam N r)) '' ((rFam N : Finset ℕ) : Set ℕ)).Nonempty :=
    ⟨_, N, Finset.mem_coe.2 (rFam_nonempty (by omega)), rfl⟩
  have hfin : ((fun r => PhiFam N r (mFam N r)) '' ((rFam N : Finset ℕ) : Set ℕ)).Finite :=
    (Finset.finite_toSet _).image _
  obtain ⟨r, hr, hEq⟩ := hne.csInf_mem hfin
  have hr' := Finset.mem_coe.1 hr
  exact ⟨r, hr', hEq.symm, mFam_ge_two hN hr', mFam_le hN hr'⟩

end Gap
end Sext6
end LRSpectrumFull
