import LRSpectrumFull.Sext6.Gap.GFam
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Data.Nat.Prime.Infinite
import Mathlib.Algebra.Order.Floor.Semiring

/-!
# The family value `G(N)`: exact reformulation and the elementary asymptotics  [2026-11-24]

Source: the accompanying notes on the asymptotics of `G(N)` (Prop 1, Prop 2, Thm A).

With `A = N + 1`, `s = sFam N r`, `β = betaFam N r`, `m = mFam N r = β / s + 1`, `e = m s - β`:

* `1 ≤ e ≤ s`, and `m r + β + e = m A` (`eFam_sum`);
* `PhiFam N r m = m / (m A - e) = 1 / (A - e / m)` (`Phi_eq`);
* `Gfam N = 1 / (A - μ)` with `μ = min_r e_r / m_r` (`Gfam_eq_mu`), `0 < μ ≤ 1/2`,
  `Gfam N ≤ 2/(2N+1)`, `1/(N+1) < Gfam N`;
* `N² (Gfam N - 1/(N+1)) < 1/2` for all `N ≥ 2` (the draft statement is TRUE as written,
  no `(1 + O(1/N))` factor is needed: `N²/((N+1)(2N+1)) < 1/2`);
* if `N + 1` is prime then `Gfam N = 2/(2N+1)`, hence the scaled gap is `≥ 1/2 - ε` infinitely often;
* `Gfam N < 2/(2N+1) ↔ ∃ r, 2 e < m`, and then the forcing at `s ≥ 2`: every `b ∈ [s, 2s-1]` shares
  a factor with `r = N + 1 - s` (so every prime in `[s, 2s-1]` divides `r`).

`g(N) = G(N)` is NOT claimed.  No `sorry`, no `axiom`.

Convention: `N = k + 1` is the number of speeds of the vector `v : Fin (k+1) → ℤ`. Speeds are the moving runners; the runner at rest is not counted, so a vector of `N` speeds means `N + 1` runners and the Lonely Runner value is `1/(N+1)`.
Hypotheses: those of the individual statements (numerical bounds, structural conditions and, where named in the list above, window predicates such as `PrimeWin`, `CopWin`, `PrimeWindow7`, which later modules discharge for explicit ranges). The unproved predicates `DusartPi`, `LRCHyp`, `CopWinHyp` are not hypotheses of any statement in this module.
Axiom audit: covered by `Axioms3` (also reached through the imports of `Axioms8`) (`#print axioms`; declarations not printed there are bricks of printed ones, so their axioms are bounded by the printed lines).
-/

namespace LRSpectrumFull
namespace Sext6
namespace Gap

/-- `e = m s - β`. -/
noncomputable def eFam (N r : ℕ) : ℕ := mFam N r * sFam N r - betaFam N r

section e

variable {N r : ℕ}

theorem eFam_add (hr : r ∈ rFam N) : eFam N r + betaFam N r = mFam N r * sFam N r := by
  have := mFam_nonTight hr
  unfold eFam; omega

theorem eFam_pos (hr : r ∈ rFam N) : 1 ≤ eFam N r := by
  have := mFam_nonTight hr
  unfold eFam; omega

theorem eFam_le (hr : r ∈ rFam N) : eFam N r ≤ sFam N r := by
  have h1 := Nat.div_mul_le_self (betaFam N r) (sFam N r)
  have h2 : mFam N r * sFam N r = betaFam N r / sFam N r * sFam N r + sFam N r := by
    unfold mFam; ring
  have := mFam_nonTight hr
  unfold eFam; omega

/-- `m r + β + e = m (N + 1)`. -/
theorem eFam_sum (hr : r ∈ rFam N) :
    mFam N r * r + betaFam N r + eFam N r = mFam N r * (N + 1) := by
  obtain ⟨h1, h2, h3⟩ := mem_rFam.1 hr
  have h := eFam_add hr
  have hs := sFam_add h2
  have h3' : mFam N r * (sFam N r + r) = mFam N r * (N + 1) := by rw [hs]
  have h4 : mFam N r * (sFam N r + r) = mFam N r * sFam N r + mFam N r * r := by ring
  omega

theorem denom_real (hr : r ∈ rFam N) :
    (((mFam N r * r + betaFam N r : ℕ)) : ℝ) = (mFam N r : ℝ) * ((N : ℝ) + 1) - (eFam N r : ℝ) := by
  have h := eFam_sum hr
  have h' : ((mFam N r * r + betaFam N r + eFam N r : ℕ) : ℝ) = ((mFam N r * (N + 1) : ℕ) : ℝ) := by
    rw [h]
  push_cast at h' ⊢
  linarith

theorem mFam_pos_real (hN : 2 ≤ N) (hr : r ∈ rFam N) : (0 : ℝ) < (mFam N r : ℝ) := by
  have := mFam_ge_two hN hr
  exact_mod_cast (by omega : 0 < mFam N r)

theorem denom_pos (hN : 2 ≤ N) (hr : r ∈ rFam N) : (0 : ℝ) < (((mFam N r * r + betaFam N r : ℕ)) : ℝ) := by
  have hS := rFam_spec hN hr
  have hb := hS.beta_pos
  have : 0 < mFam N r * r + betaFam N r := by omega
  exact_mod_cast this

theorem A_sub_eq (hN : 2 ≤ N) (hr : r ∈ rFam N) :
    (N : ℝ) + 1 - (eFam N r : ℝ) / (mFam N r : ℝ) = (((mFam N r * r + betaFam N r : ℕ)) : ℝ) / (mFam N r : ℝ) := by
  have hm := mFam_pos_real hN hr
  have hm' : (mFam N r : ℝ) ≠ 0 := hm.ne'
  rw [denom_real hr]
  first | (field_simp; ring) | field_simp

theorem A_sub_pos (hN : 2 ≤ N) (hr : r ∈ rFam N) : (0 : ℝ) < (N : ℝ) + 1 - (eFam N r : ℝ) / (mFam N r : ℝ) := by
  rw [A_sub_eq hN hr]
  exact div_pos (denom_pos hN hr) (mFam_pos_real hN hr)

/-- Prop 1(b): `PhiFam N r m_r = 1 / (A - e / m)`. -/
theorem Phi_eq (hN : 2 ≤ N) (hr : r ∈ rFam N) :
    PhiFam N r (mFam N r) = 1 / ((N : ℝ) + 1 - (eFam N r : ℝ) / (mFam N r : ℝ)) := by
  rw [A_sub_eq hN hr, one_div_div]
  rfl

/-- Prop 1(b), other form: `PhiFam N r m_r = m / (m A - e)`. -/
theorem Phi_eq' (hr : r ∈ rFam N) :
    PhiFam N r (mFam N r) = (mFam N r : ℝ) / ((mFam N r : ℝ) * ((N : ℝ) + 1) - (eFam N r : ℝ)) := by
  unfold PhiFam
  rw [denom_real hr]

end e

/-- `μ(N) = min_r e_r / m_r`. -/
noncomputable def muFam (N : ℕ) : ℝ :=
  sInf ((fun r => (eFam N r : ℝ) / (mFam N r : ℝ)) '' ((rFam N : Finset ℕ) : Set ℕ))

section mu

variable {N : ℕ}

theorem mu_bdd (N : ℕ) :
    BddBelow ((fun r => (eFam N r : ℝ) / (mFam N r : ℝ)) '' ((rFam N : Finset ℕ) : Set ℕ)) :=
  ⟨0, by rintro _ ⟨r', _, rfl⟩; positivity⟩

theorem mu_le_div {r : ℕ} (hr : r ∈ rFam N) : muFam N ≤ (eFam N r : ℝ) / (mFam N r : ℝ) :=
  csInf_le (mu_bdd N) ⟨r, Finset.mem_coe.2 hr, rfl⟩

theorem mu_attained (hN : 2 ≤ N) :
    ∃ r ∈ rFam N, muFam N = (eFam N r : ℝ) / (mFam N r : ℝ) := by
  have hne : ((fun r => (eFam N r : ℝ) / (mFam N r : ℝ)) '' ((rFam N : Finset ℕ) : Set ℕ)).Nonempty :=
    ⟨_, N, Finset.mem_coe.2 (rFam_nonempty (by omega)), rfl⟩
  have hfin : ((fun r => (eFam N r : ℝ) / (mFam N r : ℝ)) '' ((rFam N : Finset ℕ) : Set ℕ)).Finite :=
    (Finset.finite_toSet _).image _
  obtain ⟨r, hr, hEq⟩ := hne.csInf_mem hfin
  exact ⟨r, Finset.mem_coe.1 hr, hEq.symm⟩

theorem mu_pos (hN : 2 ≤ N) : 0 < muFam N := by
  obtain ⟨r, hr, h⟩ := mu_attained hN
  rw [h]
  have he := eFam_pos hr
  have he' : (0 : ℝ) < (eFam N r : ℝ) := by exact_mod_cast (by omega : 0 < eFam N r)
  exact div_pos he' (mFam_pos_real hN hr)

/-- Prop 1(c): `μ ≤ 1/2`  (the column `r = N` has `s = 1`, `e ≤ 1`, `m ≥ 2`). -/
theorem mu_le_half (hN : 2 ≤ N) : muFam N ≤ 1 / 2 := by
  have hr : N ∈ rFam N := rFam_nonempty (by omega)
  have h1 := mu_le_div hr
  have hs : sFam N N = 1 := by unfold sFam; omega
  have he : (eFam N N : ℝ) ≤ 1 := by
    have := eFam_le hr
    rw [hs] at this
    exact_mod_cast this
  have hm : (2 : ℝ) ≤ (mFam N N : ℝ) := by exact_mod_cast mFam_ge_two hN hr
  have hmpos := mFam_pos_real hN hr
  have : (eFam N N : ℝ) / (mFam N N : ℝ) ≤ 1 / 2 := by
    rw [div_le_iff₀ hmpos]
    linarith
  linarith

/-- Prop 1(c): `G(N) = 1 / (A - μ)`. -/
theorem Gfam_eq_mu (hN : 2 ≤ N) : Gfam N = 1 / ((N : ℝ) + 1 - muFam N) := by
  obtain ⟨r1, hr1, hmu1⟩ := mu_attained hN
  obtain ⟨r0, hr0, hG0, -, -⟩ := Gfam_attained hN
  apply le_antisymm
  · calc Gfam N ≤ PhiFam N r1 (mFam N r1) :=
          csInf_le (Gfam_bddBelow N) ⟨r1, Finset.mem_coe.2 hr1, rfl⟩
      _ = 1 / ((N : ℝ) + 1 - (eFam N r1 : ℝ) / (mFam N r1 : ℝ)) := Phi_eq hN hr1
      _ = 1 / ((N : ℝ) + 1 - muFam N) := by rw [hmu1]
  · rw [hG0, Phi_eq hN hr0]
    apply one_div_le_one_div_of_le (A_sub_pos hN hr0)
    have := mu_le_div hr0
    linarith

/-- Prop 2(a): `G(N) ≤ 2/(2N+1)`. -/
theorem Gfam_le_two (hN : 2 ≤ N) : Gfam N ≤ 2 / (2 * (N : ℝ) + 1) := by
  rw [Gfam_eq_mu hN]
  have hmu := mu_le_half hN
  have hN0 : (0 : ℝ) ≤ N := Nat.cast_nonneg _
  have hA : (0 : ℝ) < (N : ℝ) + 1 - 1 / 2 := by linarith
  calc 1 / ((N : ℝ) + 1 - muFam N) ≤ 1 / ((N : ℝ) + 1 - 1 / 2) :=
        one_div_le_one_div_of_le hA (by linarith)
    _ = 2 / (2 * (N : ℝ) + 1) := by
        rw [show (N : ℝ) + 1 - 1 / 2 = (2 * (N : ℝ) + 1) / 2 by ring, one_div_div]

/-- `1/(N+1) < G(N)`. -/
theorem Gfam_gt (hN : 2 ≤ N) : 1 / ((N : ℝ) + 1) < Gfam N := by
  rw [Gfam_eq_mu hN]
  have hmu := mu_le_half hN
  have hmu0 := mu_pos hN
  have hN0 : (0 : ℝ) ≤ N := Nat.cast_nonneg _
  exact one_div_lt_one_div_of_lt (by linarith) (by linarith)

/-- Prop 1(d): `G - 1/A = μ / (A (A - μ))`. -/
theorem Gfam_sub_inv (hN : 2 ≤ N) :
    Gfam N - 1 / ((N : ℝ) + 1) = muFam N / (((N : ℝ) + 1) * ((N : ℝ) + 1 - muFam N)) := by
  have hmu := mu_le_half hN
  have hN0 : (0 : ℝ) ≤ N := Nat.cast_nonneg _
  have h1 : (N : ℝ) + 1 - muFam N ≠ 0 := by intro h; linarith
  have h2 : (N : ℝ) + 1 ≠ 0 := by intro h; linarith
  rw [Gfam_eq_mu hN]
  first | (field_simp; ring) | field_simp

end mu

/-- The scaled gap `N² (G(N) - 1/(N+1))`. -/
noncomputable def gapA (N : ℕ) : ℝ := (N : ℝ) ^ 2 * (Gfam N - 1 / ((N : ℝ) + 1))

theorem two_sub_eq (N : ℕ) :
    2 / (2 * (N : ℝ) + 1) - 1 / ((N : ℝ) + 1) = 1 / ((2 * (N : ℝ) + 1) * ((N : ℝ) + 1)) := by
  have hN0 : (0 : ℝ) ≤ N := Nat.cast_nonneg _
  have h1 : (2 * (N : ℝ) + 1) ≠ 0 := by intro h; linarith
  have h2 : (N : ℝ) + 1 ≠ 0 := by intro h; linarith
  first | (field_simp; ring) | field_simp

theorem gapA_pos {N : ℕ} (hN : 2 ≤ N) : 0 < gapA N := by
  unfold gapA
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have := Gfam_gt hN
  have h : 0 < Gfam N - 1 / ((N : ℝ) + 1) := by linarith
  positivity

/-- (2) The strict inequality `N² (G(N) - 1/(N+1)) < 1/2` holds EXACTLY as stated, for every `N ≥ 2`. -/
theorem gapA_lt_half {N : ℕ} (hN : 2 ≤ N) : gapA N < 1 / 2 := by
  have hG := Gfam_le_two hN
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have key := two_sub_eq N
  have h2 : (N : ℝ) ^ 2 * (1 / ((2 * (N : ℝ) + 1) * ((N : ℝ) + 1))) < 1 / 2 := by
    rw [mul_one_div, div_lt_div_iff₀ (by positivity) (by norm_num)]
    nlinarith
  unfold gapA
  calc (N : ℝ) ^ 2 * (Gfam N - 1 / ((N : ℝ) + 1))
      ≤ (N : ℝ) ^ 2 * (1 / ((2 * (N : ℝ) + 1) * ((N : ℝ) + 1))) :=
        mul_le_mul_of_nonneg_left (by linarith) (by positivity)
    _ < 1 / 2 := h2

/-! ### (3) the limsup -/

theorem betaFam_prime {N r : ℕ} (hN : 2 ≤ N) (hA : (N + 1).Prime) (hr : r ∈ rFam N) :
    betaFam N r = sFam N r := by
  obtain ⟨h1, h2, h3⟩ := mem_rFam.1 hr
  have hS := rFam_spec hN hr
  have hs := sFam_add h2
  have hspos := sFam_pos hr
  have hcop : Nat.Coprime (sFam N r) r := by
    have h1' : Nat.Coprime (N + 1) (sFam N r) :=
      (Nat.Prime.coprime_iff_not_dvd hA).2 (fun hd => by
        have := Nat.le_of_dvd hspos hd
        omega)
    have h2' : Nat.Coprime (sFam N r) (N + 1) := h1'.symm
    rw [← hs] at h2'
    exact Nat.coprime_self_add_right.1 h2'
  apply le_antisymm
  · exact hS.hb3 (sFam N r) (by omega) hcop
  · have := hS.hb1
    omega

theorem mFam_prime {N r : ℕ} (hN : 2 ≤ N) (hA : (N + 1).Prime) (hr : r ∈ rFam N) :
    mFam N r = 2 := by
  have hb := betaFam_prime hN hA hr
  have hspos := sFam_pos hr
  unfold mFam
  rw [hb, Nat.div_self hspos]

/-- If `N + 1` is prime then `G(N) = 2/(2N+1)` (`μ = 1/2`). -/
theorem Gfam_prime {N : ℕ} (hN : 2 ≤ N) (hA : (N + 1).Prime) : Gfam N = 2 / (2 * (N : ℝ) + 1) := by
  apply le_antisymm (Gfam_le_two hN)
  unfold Gfam
  apply le_csInf
  · exact ⟨_, N, Finset.mem_coe.2 (rFam_nonempty (by omega)), rfl⟩
  · rintro _ ⟨r, hr, rfl⟩
    have hr' := Finset.mem_coe.1 hr
    obtain ⟨h1, h2, h3⟩ := mem_rFam.1 hr'
    have hb := betaFam_prime hN hA hr'
    have hm := mFam_prime hN hA hr'
    have hs := sFam_add h2
    have hD : (0 : ℝ) < ((2 * r + sFam N r : ℕ) : ℝ) := by
      have : 0 < 2 * r + sFam N r := by omega
      exact_mod_cast this
    have hsR : (sFam N r : ℝ) + r = (N : ℝ) + 1 := by exact_mod_cast hs
    have hrR : (r : ℝ) ≤ N := by exact_mod_cast h2
    show 2 / (2 * (N : ℝ) + 1) ≤ PhiFam N r (mFam N r)
    unfold PhiFam
    rw [hm, hb]
    have hN0 : (0 : ℝ) ≤ N := Nat.cast_nonneg _
    rw [div_le_div_iff₀ (by positivity) hD]
    push_cast
    nlinarith

/-- The lower side of the limsup: for every `ε > 0`, `N² (G(N) - 1/(N+1)) ≥ 1/2 - ε` for infinitely
many `N` (all `N` with `N + 1` prime and `ε N ≥ 1`). -/
theorem gapA_frequently (ε : ℝ) (hε : 0 < ε) :
    ∃ᶠ N in Filter.atTop, 1 / 2 - ε ≤ gapA N := by
  rw [Filter.frequently_atTop]
  intro a
  obtain ⟨p, hp, hpp⟩ := Nat.exists_infinite_primes (a + 3 + ⌈1 / ε⌉₊)
  obtain ⟨N, rfl⟩ : ∃ N, p = N + 1 := ⟨p - 1, by omega⟩
  refine ⟨N, by omega, ?_⟩
  have hN2 : 2 ≤ N := by omega
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hceil : 1 / ε ≤ (N : ℝ) := by
    have h1 := Nat.le_ceil (1 / ε)
    have h2 : ((⌈1 / ε⌉₊ : ℕ) : ℝ) ≤ N := by exact_mod_cast (by omega : ⌈1 / ε⌉₊ ≤ N)
    linarith
  have hεN : 1 ≤ ε * N := by
    have := (div_le_iff₀ hε).1 hceil
    linarith
  unfold gapA
  rw [Gfam_prime hN2 hpp, two_sub_eq, mul_one_div,
    le_div_iff₀ (by positivity)]
  nlinarith [mul_nonneg hN0.le (sub_nonneg.2 hεN), hε]

/-- (3) Summary: `limsup N² (G(N) - 1/(N+1)) = 1/2` in the `ε`-form: bounded by `1/2` strictly for all
`N ≥ 2`, and within `ε` of `1/2` infinitely often. -/
theorem limsup_gapA :
    (∀ N : ℕ, 2 ≤ N → gapA N < 1 / 2) ∧ ∀ ε : ℝ, 0 < ε → ∃ᶠ N in Filter.atTop, 1 / 2 - ε ≤ gapA N :=
  ⟨fun _ hN => gapA_lt_half hN, gapA_frequently⟩

/-! ### (4) forcing -/

section force

variable {N : ℕ}

theorem Phi_lt_iff (hN : 2 ≤ N) {r : ℕ} (hr : r ∈ rFam N) :
    PhiFam N r (mFam N r) < 2 / (2 * (N : ℝ) + 1) ↔ 2 * eFam N r < mFam N r := by
  have hD := denom_pos hN hr
  have hN0 : (0 : ℝ) ≤ N := Nat.cast_nonneg _
  unfold PhiFam
  rw [div_lt_div_iff₀ hD (by positivity), denom_real hr]
  constructor
  · intro h
    have : (2 * (eFam N r : ℝ)) < (mFam N r : ℝ) := by nlinarith
    exact_mod_cast this
  · intro h
    have h' : ((2 * eFam N r : ℕ) : ℝ) < (mFam N r : ℝ) := by exact_mod_cast h
    push_cast at h'
    nlinarith

/-- Prop 2(c): `G(N) < 2/(2N+1)` iff some column has `2 e < m`. -/
theorem Gfam_lt_iff (hN : 2 ≤ N) :
    Gfam N < 2 / (2 * (N : ℝ) + 1) ↔ ∃ r ∈ rFam N, 2 * eFam N r < mFam N r := by
  constructor
  · intro h
    obtain ⟨r0, hr0, hG0, -, -⟩ := Gfam_attained hN
    rw [hG0] at h
    exact ⟨r0, hr0, (Phi_lt_iff hN hr0).1 h⟩
  · rintro ⟨r, hr, h⟩
    exact lt_of_le_of_lt
      (show Gfam N ≤ PhiFam N r (mFam N r) from
        csInf_le (Gfam_bddBelow N) ⟨r, Finset.mem_coe.2 hr, rfl⟩)
      ((Phi_lt_iff hN hr).2 h)

/-- Prop 2(b),(d), forcing necessity: if `G(N) < 2/(2N+1)` then there is a column `r` with
`s = N + 1 - r ≥ 2`, `β ≥ 2 s`, every `b ∈ [s, 2s-1]` not coprime to `r`, hence every prime in
`[s, 2s-1]` divides `r`. -/
theorem Gfam_lt_forcing (hN : 2 ≤ N) (h : Gfam N < 2 / (2 * (N : ℝ) + 1)) :
    ∃ r ∈ rFam N, 2 ≤ sFam N r ∧ 2 * sFam N r ≤ betaFam N r ∧
      (∀ b : ℕ, sFam N r ≤ b → b < 2 * sFam N r → ¬ Nat.Coprime b r) ∧
      (∀ p : ℕ, p.Prime → sFam N r ≤ p → p < 2 * sFam N r → p ∣ r) := by
  obtain ⟨r, hr, hlt⟩ := (Gfam_lt_iff hN).1 h
  have he := eFam_pos hr
  have hspos := sFam_pos hr
  have hm3 : 3 ≤ mFam N r := by omega
  have hdiv : 2 ≤ betaFam N r / sFam N r := by
    have : 3 ≤ betaFam N r / sFam N r + 1 := hm3
    omega
  have hb2 : 2 * sFam N r ≤ betaFam N r := (Nat.le_div_iff_mul_le hspos).1 hdiv
  obtain ⟨h1, h2, h3⟩ := mem_rFam.1 hr
  have hS := rFam_spec hN hr
  have hs := sFam_add h2
  have hforce : ∀ b : ℕ, sFam N r ≤ b → b < 2 * sFam N r → ¬ Nat.Coprime b r := by
    intro b hb1 hb2' hc
    have := hS.hb3 b (by omega) hc
    omega
  refine ⟨r, hr, ?_, hb2, hforce, ?_⟩
  · by_contra hlt2
    have h1' : sFam N r = 1 := by omega
    exact hforce 1 (by omega) (by omega) (Nat.coprime_one_left r)
  · intro p hp hp1 hp2
    by_contra hnd
    exact hforce p hp1 hp2 ((Nat.Prime.coprime_iff_not_dvd hp).2 hnd)

end force

end Gap
end Sext6
end LRSpectrumFull
