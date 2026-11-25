import LRSpectrumFull.Sext6.Gap.ThmXLast
import Mathlib.NumberTheory.SumPrimeReciprocals
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Order.Filter.AtTopBot.Basic

/-!
# Theorem X, part 6: the exceptional family and the growth law (finiteness-free form)  [2026-11-25]

Source: the accompanying notes on Theorem X, Sections 0 (vi) and 4 (vi).

Semantics.  `ExcAt k N r` : `2 ≤ r`, `2 r ≤ N`, and some speed vector `v` contains every `x ∈ [1,N] \ {r}`, no entry equals `r`,
all entries are `≥ 1`, at most `k` distinct entries exceed `N`, and `ML v < 1/N`.
`N0Ge k M` ("`N0(k) ≥ M`") : some `N` with `M ≤ N + 1` and some `r` satisfy `ExcAt k N r`.
This is the statement `N0(k) = 1 + max{N : ...} ≥ M` without asserting that the maximum exists (finiteness of `N0(k)`
is NOT formalised here and is not needed for any statement below).

* `excAt_of_xholds`, `excAt_lastN`, `exception_family` : for `r ≥ 2` and `N = 3r + ell*(r)` there is a vector
  `V = ([N] \ {r}) ∪ W` with `|V \ [N]| = φ(r)`, `r ∉ V`, `ML V < 1/N`, and `N` is the last exceptional `N`.
* `n0ge_phi`, `n0ge_phi_three` : `N0(φ(r)) ≥ 3r + ell*(r) + 1 ≥ 3r + 1`.
* `exists_ratio_gt`, `exists_ratio_gt_big` : `r/φ(r)` is unbounded (from the divergence of `Σ 1/p`,
  `Nat.Primes.not_summable_one_div`), also with `φ(r) ≥ K0` arbitrary.
* `growth_unbounded`, `growth_frequently`, `n0_growth` : for every `C` there are arbitrarily large `k` with `N0(k) > C k`.
NOT formalised: the rate `(3 e^γ - o(1)) k log log k` (needs Mertens' third theorem, not in Mathlib: grep found nothing)
and the upper bounds on `N0(k)`.
No `sorry`, no `axiom`.

Convention: `N` is the size of the ambient interval `[N]`; `k` is a bound on the number of added speeds.
Hypotheses: those of the individual statements.
Axiom audit: covered by `Axioms25`.
-/

namespace LRSpectrumFull
namespace Sext6
namespace Gap

/-- `ExcAt k N r`: the unit-window-type exception at `N` with at most `k` added speeds. -/
def ExcAt (k N r : ℕ) : Prop :=
  2 ≤ r ∧ 2 * r ≤ N ∧
  ∃ (m : ℕ) (v : Fin (m + 1) → ℤ),
    (∀ x : ℕ, 1 ≤ x → x ≤ N → x ≠ r → ∃ i, v i = (x : ℤ)) ∧
    (∀ i, 1 ≤ v i ∧ v i ≠ (r : ℤ)) ∧
    (outEntries N v).card ≤ k ∧
    ML v < 1 / (N : ℝ)

theorem ExcAt.mono {k k' N r : ℕ} (h : ExcAt k N r) (hk : k ≤ k') : ExcAt k' N r := by
  obtain ⟨a, b, m, v, c, d, e, f⟩ := h
  exact ⟨a, b, m, v, c, d, e.trans hk, f⟩

/-- `N0(k) ≥ M`: an exceptional `N ≥ M - 1` exists with at most `k` added speeds. -/
def N0Ge (k M : ℕ) : Prop := ∃ N r : ℕ, M ≤ N + 1 ∧ ExcAt k N r

theorem N0Ge.mono_k {k k' M : ℕ} (h : N0Ge k M) (hk : k ≤ k') : N0Ge k' M := by
  obtain ⟨N, r, hM, hE⟩ := h
  exact ⟨N, r, hM, hE.mono hk⟩

theorem N0Ge.mono_M {k M M' : ℕ} (h : N0Ge k M) (hM : M' ≤ M) : N0Ge k M' := by
  obtain ⟨N, r, hMN, hE⟩ := h
  exact ⟨N, r, hM.trans hMN, hE⟩

/-- The criterion `XHolds r N` gives an exception with exactly the window `W`, `|W| = φ(r)`. -/
theorem excAt_of_xholds {N r : ℕ} (hr2 : 2 ≤ r) (hN : 2 * r ≤ N) (hX : XHolds r N) :
    ExcAt (Nat.totient r) N r := by
  obtain ⟨m, v, hV⟩ := exists_isV hr2 hN
  refine ⟨hr2, hN, m, v, ?_, ?_, ?_, ?_⟩
  · intro x h1 h2 h3
    exact hV.cov x (Or.inl ⟨h1, h2, h3⟩)
  · intro i
    exact ⟨(hV.sub i).pos_le.1, isV_ne_r v hV i⟩
  · exact (isV_out_card v hV).le
  · exact (thmX_xholds hr2 hN v hV).mpr hX

/-- At the last exceptional `N = 3r + ell*(r)` there is an exception with `φ(r)` added speeds. -/
theorem excAt_lastN {r : ℕ} (hr2 : 2 ≤ r) : ExcAt (Nat.totient r) (3 * r + lstar r) r := by
  have h := lastN_eq r
  rw [← h]
  exact excAt_of_xholds hr2 (by have := three_le_lastN r; omega) (xholds_lastN r)

/-- The exceptional family at `N = 3r + ell*(r)`: the vector, its value, `|V \ [N]| = φ(r)`, `r ∉ V`, and that
`N` is the last exceptional `N`. -/
theorem exception_family {r : ℕ} (hr2 : 2 ≤ r) :
    ∃ (m : ℕ) (v : Fin (m + 1) → ℤ), IsV (3 * r + lstar r) r v ∧
      ML v < 1 / ((3 * r + lstar r : ℕ) : ℝ) ∧
      (outEntries (3 * r + lstar r) v).card = Nat.totient r ∧
      (∀ i, v i ≠ (r : ℤ)) ∧
      LastExc r (3 * r + lstar r) := by
  have h := lastN_eq r
  have hLE : LastExc r (3 * r + lstar r) := by rw [← h]; exact lastExc_lastN (by omega)
  have hN : 2 * r ≤ 3 * r + lstar r := by omega
  obtain ⟨m, v, hV⟩ := exists_isV hr2 hN
  refine ⟨m, v, hV, ?_, isV_out_card v hV, isV_ne_r v hV, hLE⟩
  exact (thmX_xholds hr2 hN v hV).mpr hLE.1

/-- Sharpness: beyond the last exceptional `N` every vector of the family has `1/N ≤ ML`. -/
theorem exception_last_sharp {r : ℕ} (hr2 : 2 ≤ r) :
    ∀ N : ℕ, 3 * r + lstar r < N → ∀ (k : ℕ) (v : Fin (k + 1) → ℤ), IsV N r v → 1 / (N : ℝ) ≤ ML v := by
  have h := lastN_eq r
  have hLE : LastExc r (3 * r + lstar r) := by rw [← h]; exact lastExc_lastN (by omega)
  exact (thmX_last hr2 (by omega) hLE).2

/-- `N0(φ(r)) ≥ 3r + ell*(r) + 1`. -/
theorem n0ge_phi {r : ℕ} (hr2 : 2 ≤ r) : N0Ge (Nat.totient r) (3 * r + lstar r + 1) :=
  ⟨3 * r + lstar r, r, le_rfl, excAt_lastN hr2⟩

/-- `N0(φ(r)) ≥ 3r + 1`. -/
theorem n0ge_phi_three {r : ℕ} (hr2 : 2 ≤ r) : N0Ge (Nat.totient r) (3 * r + 1) :=
  (n0ge_phi hr2).mono_M (by omega)

/-! ### `r / φ(r)` is unbounded -/

/-- The product of a finite set of primes. -/
def pprod (u : Finset Nat.Primes) : ℕ := ∏ p ∈ u, (p : ℕ)

theorem pprod_pos (u : Finset Nat.Primes) : 0 < pprod u :=
  Finset.prod_pos (fun p _ => p.prop.pos)

theorem pprod_insert {p : Nat.Primes} {u : Finset Nat.Primes} (hp : p ∉ u) :
    pprod (insert p u) = (p : ℕ) * pprod u := by
  unfold pprod
  rw [Finset.prod_insert hp]

theorem coprime_pprod {p : Nat.Primes} {u : Finset Nat.Primes} (hp : p ∉ u) :
    Nat.Coprime (p : ℕ) (pprod u) := by
  rw [Nat.Prime.coprime_iff_not_dvd p.prop]
  intro hd
  unfold pprod at hd
  obtain ⟨q, hq, hpq⟩ := (Prime.dvd_finsetProd_iff p.prop.prime _).mp hd
  have h1 : (p : ℕ) = (q : ℕ) := (Nat.prime_dvd_prime_iff_eq p.prop q.prop).mp hpq
  have h2 : p = q := (Nat.Primes.coe_nat_inj p q).mp h1
  exact hp (by rw [h2]; exact hq)

theorem ratio_aux (x S F R : ℝ) (hx : 2 ≤ x) (hS : 0 ≤ S) (hF : 0 ≤ F) (ih : (1 + S) * F ≤ R) :
    (1 + (1 / x + S)) * ((x - 1) * F) ≤ x * R := by
  have hx0 : 0 < x := by linarith
  have e : 1 / x * x = 1 := by field_simp
  have h1x : 0 ≤ 1 / x := by positivity
  have key : (1 + (1 / x + S)) * (x - 1) ≤ (1 + S) * x := by nlinarith [e, h1x, hS]
  calc (1 + (1 / x + S)) * ((x - 1) * F) = ((1 + (1 / x + S)) * (x - 1)) * F := by ring
    _ ≤ ((1 + S) * x) * F := mul_le_mul_of_nonneg_right key hF
    _ = x * ((1 + S) * F) := by ring
    _ ≤ x * R := mul_le_mul_of_nonneg_left ih hx0.le

/-- `(1 + Σ_{p ∈ u} 1/p) φ(P) ≤ P` for `P` the product of the primes in `u` (i.e. `P/φ(P) ≥ 1 + Σ 1/p`). -/
theorem ratio_ge (u : Finset Nat.Primes) :
    (1 + ∑ p ∈ u, 1 / ((p : ℕ) : ℝ)) * (Nat.totient (pprod u) : ℝ) ≤ (pprod u : ℝ) := by
  refine Finset.induction_on u ?_ ?_
  · simp [pprod]
  · intro p u hp ih
    have hp2 : (2 : ℝ) ≤ ((p : ℕ) : ℝ) := by exact_mod_cast p.prop.two_le
    have hS : 0 ≤ ∑ q ∈ u, 1 / ((q : ℕ) : ℝ) := Finset.sum_nonneg (fun q _ => by positivity)
    have hF : 0 ≤ (Nat.totient (pprod u) : ℝ) := Nat.cast_nonneg _
    have hcast : (((p : ℕ) - 1 : ℕ) : ℝ) = ((p : ℕ) : ℝ) - 1 := by
      rw [Nat.cast_sub p.prop.one_le, Nat.cast_one]
    rw [Finset.sum_insert hp, pprod_insert hp, Nat.totient_mul (coprime_pprod hp),
      Nat.totient_prime p.prop, Nat.cast_mul, Nat.cast_mul, hcast]
    exact ratio_aux _ _ _ _ hp2 hS hF ih

/-- `r / φ(r)` is unbounded (divergence of `Σ 1/p`). -/
theorem exists_ratio_gt (C : ℝ) : ∃ r : ℕ, 2 ≤ r ∧ C * (Nat.totient r : ℝ) < r := by
  have hc1 : (1 : ℝ) ≤ max C 1 := le_max_right _ _
  have hCc : C ≤ max C 1 := le_max_left _ _
  obtain ⟨u, hu⟩ : ∃ u : Finset Nat.Primes, max C 1 < ∑ p ∈ u, 1 / ((p : ℕ) : ℝ) := by
    by_contra hcon
    push_neg at hcon
    exact Nat.Primes.not_summable_one_div
      (summable_of_sum_le (c := max C 1)
        (fun p => by show (0 : ℝ) ≤ 1 / ((p : ℕ) : ℝ); positivity) hcon)
  have hR := ratio_ge u
  have hpos : 0 < pprod u := pprod_pos u
  have hFpos : (0 : ℝ) < (Nat.totient (pprod u) : ℝ) := by
    exact_mod_cast Nat.totient_pos.mpr hpos
  refine ⟨pprod u, ?_, ?_⟩
  · by_contra hlt
    have h1 : pprod u = 1 := by omega
    rw [h1] at hR
    simp only [Nat.totient_one, Nat.cast_one, mul_one] at hR
    linarith
  · calc C * (Nat.totient (pprod u) : ℝ) ≤ max C 1 * (Nat.totient (pprod u) : ℝ) :=
          mul_le_mul_of_nonneg_right hCc hFpos.le
      _ < (1 + ∑ p ∈ u, 1 / ((p : ℕ) : ℝ)) * (Nat.totient (pprod u) : ℝ) :=
          mul_lt_mul_of_pos_right (by linarith) hFpos
      _ ≤ (pprod u : ℝ) := hR

/-- As `exists_ratio_gt`, with `φ(r) ≥ K0` in addition. -/
theorem exists_ratio_gt_big (C : ℝ) (K0 : ℕ) :
    ∃ r : ℕ, 2 ≤ r ∧ K0 ≤ Nat.totient r ∧ C * (Nat.totient r : ℝ) < r := by
  obtain ⟨r0, hr0, hr0C⟩ := exists_ratio_gt (max C 0)
  obtain ⟨q, hq, hqp⟩ := Nat.exists_infinite_primes (r0 + K0 + 2)
  have hcop : Nat.Coprime r0 q := by
    rw [Nat.coprime_comm, Nat.Prime.coprime_iff_not_dvd hqp]
    intro hd
    have := Nat.le_of_dvd (by omega) hd
    omega
  have hq2 := hqp.two_le
  refine ⟨r0 * q, ?_, ?_, ?_⟩
  · nlinarith
  · rw [Nat.totient_mul hcop, Nat.totient_prime hqp]
    have h1 : 1 ≤ Nat.totient r0 := Nat.totient_pos.mpr (by omega)
    have h2 : K0 ≤ q - 1 := by omega
    exact h2.trans (Nat.le_mul_of_pos_left _ h1)
  · rw [Nat.totient_mul hcop, Nat.totient_prime hqp, Nat.cast_mul, Nat.cast_mul]
    have hq1 : ((q - 1 : ℕ) : ℝ) ≤ (q : ℝ) := by exact_mod_cast Nat.sub_le q 1
    have hC0 : 0 ≤ max C 0 := le_max_right _ _
    have hF : (0 : ℝ) ≤ (Nat.totient r0 : ℝ) := Nat.cast_nonneg _
    have hQ : (0 : ℝ) ≤ ((q - 1 : ℕ) : ℝ) := Nat.cast_nonneg _
    have hqpos : (0 : ℝ) < (q : ℝ) := by exact_mod_cast (by omega : 0 < q)
    calc C * ((Nat.totient r0 : ℝ) * ((q - 1 : ℕ) : ℝ))
        ≤ max C 0 * ((Nat.totient r0 : ℝ) * ((q - 1 : ℕ) : ℝ)) :=
          mul_le_mul_of_nonneg_right (le_max_left _ _) (mul_nonneg hF hQ)
      _ ≤ max C 0 * ((Nat.totient r0 : ℝ) * (q : ℝ)) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hq1 hF) hC0
      _ = (max C 0 * (Nat.totient r0 : ℝ)) * (q : ℝ) := by ring
      _ < (r0 : ℝ) * (q : ℝ) := mul_lt_mul_of_pos_right hr0C hqpos

/-! ### The growth statement -/

/-- For every `C` and `K0` there is `k ≥ K0` and an exception at some `N > C k` with at most `k` added speeds
(i.e. `N0(k) > C k` in the finiteness-free sense). -/
theorem growth_unbounded (C : ℝ) (K0 : ℕ) :
    ∃ k : ℕ, K0 ≤ k ∧ ∃ N r : ℕ, ExcAt k N r ∧ C * (k : ℝ) < N := by
  obtain ⟨r, hr2, hK, hC⟩ := exists_ratio_gt_big C K0
  refine ⟨Nat.totient r, hK, 3 * r + lstar r, r, excAt_lastN hr2, ?_⟩
  have h : (r : ℝ) ≤ ((3 * r + lstar r : ℕ) : ℝ) := by
    exact_mod_cast (by omega : r ≤ 3 * r + lstar r)
  linarith

/-- `limsup N0(k)/k = ∞`, in the form: for every `C`, the set of `k` admitting an exception above `C k` is unbounded. -/
theorem growth_frequently (C : ℝ) :
    ∃ᶠ k in Filter.atTop, ∃ N r : ℕ, ExcAt k N r ∧ C * (k : ℝ) < N := by
  rw [Filter.frequently_atTop]
  intro a
  obtain ⟨k, hk, h⟩ := growth_unbounded C a
  exact ⟨k, hk, h⟩

/-- The same in terms of `N0Ge`: `N0(k) ≥ M` with `M > C k`. -/
theorem n0_growth (C : ℝ) (K0 : ℕ) : ∃ k : ℕ, K0 ≤ k ∧ ∃ M : ℕ, C * (k : ℝ) < M ∧ N0Ge k M := by
  obtain ⟨k, hk, N, r, hE, hN⟩ := growth_unbounded C K0
  refine ⟨k, hk, N + 1, ?_, N, r, le_rfl, hE⟩
  have : (N : ℝ) ≤ ((N + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.le_succ N
  linarith

end Gap
end Sext6
end LRSpectrumFull
