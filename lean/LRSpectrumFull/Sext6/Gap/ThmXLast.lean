import LRSpectrumFull.Sext6.Gap.ThmXPhi
import Mathlib.NumberTheory.Bertrand
import Mathlib.NumberTheory.Primorial
import Mathlib.Data.Nat.Log

/-!
# Theorem X, part 5: the last exceptional `N` and the bounds on `ell*(r)`  [2026-11-25]

Source: the accompanying notes on Theorem X, Sections 0 (iv) and 4.

* `RunOK r l`        : every `m ∈ [l+1, 2l]` shares a factor with `r` (`l = 0` counts).
* `lastN r`          : the largest `N` with `XHolds r N` (`Nat.findGreatest` on `[0, 4r]`); `lstar r := lastN r - 3 r`.
* `lastExc_lastN`    : `LastExc r (lastN r)` for `r ≥ 1`; `lastN r < 4 r`; `lastExc_unique`; `exceptional_finite`.
* `lstar_spec`       : `lstar r` is the greatest `l` with `RunOK r l`.
* odd `r`            : `lstar_odd` (`lstar r = 0`), `not_xholds_three_add_one_of_odd` (`N = 3r+1` fails the criterion).
* `lstar_lt_maxPrimeFactor` : `lstar r < P+(r)` for `r ≥ 2` (Bertrand).
* `le_lstar_of_least_prime_not_dvd` : `⌊(q-1)/2⌋ ≤ lstar r`, `q` the least prime not dividing `r`.
* `lstar_lt_jac`     : `lstar r < j(r)`, with `j(r)` the Jacobsthal function (`jac`).
* `lstar_eq_of_primorial_like`, `lstar_primorial` : `lstar r = ⌊(P'-1)/2⌋` for `r` the product of the primes below `P'`
  (general proof); examples `r = 2, 6, 30, 210, 2310, 30030`.
No `sorry`, no `axiom`.

Convention: `N` is the size of the ambient interval `[N]`; all quantities are natural numbers.
Hypotheses: those of the individual statements.
Axiom audit: covered by `Axioms25`.
-/

namespace LRSpectrumFull
namespace Sext6
namespace Gap

/-- The run condition: every `m ∈ [l+1, 2l]` has a common factor with `r`. -/
def RunOK (r l : ℕ) : Prop := ∀ m : ℕ, l + 1 ≤ m → m ≤ 2 * l → ¬ Nat.Coprime m r

/-- The last `N` with `XHolds r N` (searched on `[0, 4r]`, which suffices by `not_xholds_of_ge`). -/
def lastN (r : ℕ) : ℕ := Nat.findGreatest (fun N => XHolds r N) (4 * r)

/-- `ell*(r)`, defined as `lastN r - 3r`. -/
def lstar (r : ℕ) : ℕ := lastN r - 3 * r

theorem xholds_three (r : ℕ) : XHolds r (3 * r) := xholds_of_le_three le_rfl

theorem three_le_lastN (r : ℕ) : 3 * r ≤ lastN r := by
  unfold lastN
  exact Nat.le_findGreatest (P := fun N => XHolds r N) (by omega) (xholds_three r)

theorem xholds_lastN (r : ℕ) : XHolds r (lastN r) := by
  unfold lastN
  exact Nat.findGreatest_spec (P := fun N => XHolds r N) (m := 3 * r) (by omega) (xholds_three r)

theorem lastN_le (r : ℕ) : lastN r ≤ 4 * r := by
  unfold lastN
  exact Nat.findGreatest_le _

theorem lastN_lt {r : ℕ} (hr : 1 ≤ r) : lastN r < 4 * r := by
  have h1 := lastN_le r
  have h2 := xholds_lastN r
  by_contra hcon
  have h3 : lastN r = 4 * r := by omega
  rw [h3] at h2
  exact not_xholds_of_ge hr le_rfl h2

/-- (a) Existence of the last exceptional `N`: `LastExc r (lastN r)`. -/
theorem lastExc_lastN {r : ℕ} (hr : 1 ≤ r) : LastExc r (lastN r) := by
  refine ⟨xholds_lastN r, fun N hN => ?_⟩
  by_cases h : N ≤ 4 * r
  · exact Nat.findGreatest_is_greatest (P := fun N => XHolds r N) (n := 4 * r) hN h
  · exact not_xholds_of_ge hr (by omega)

/-- The last exceptional `N` is unique. -/
theorem lastExc_unique {r L L' : ℕ} (h : LastExc r L) (h' : LastExc r L') : L = L' := by
  by_contra hne
  rcases Nat.lt_or_gt_of_ne hne with hlt | hgt
  · exact h.2 L' hlt h'.1
  · exact h'.2 L hgt h.1

theorem lastN_eq_of_lastExc {r L : ℕ} (hr : 1 ≤ r) (h : LastExc r L) : lastN r = L :=
  lastExc_unique (lastExc_lastN hr) h

/-- The set of exceptional `N` is finite (contained in `[0, 4r)`). -/
theorem exceptional_finite {r : ℕ} (hr : 1 ≤ r) : {N : ℕ | XHolds r N}.Finite := by
  apply (Set.finite_Iio (4 * r)).subset
  intro N hN
  by_contra hcon
  simp only [Set.mem_Iio, not_lt] at hcon
  exact not_xholds_of_ge hr hcon hN

theorem lastN_eq (r : ℕ) : lastN r = 3 * r + lstar r := by
  have := three_le_lastN r
  unfold lstar
  omega

theorem lstar_lt_r {r : ℕ} (hr : 1 ≤ r) : lstar r < r := by
  have := lastN_lt hr
  have := lastN_eq r
  omega

theorem runOK_lstar (r : ℕ) : RunOK r (lstar r) :=
  (xholds_run (lastN_eq r)).mp (xholds_lastN r)

theorem not_runOK_of_gt {r l : ℕ} (hr : 1 ≤ r) (h : lstar r < l) : ¬ RunOK r l := by
  intro h'
  have hx : XHolds r (3 * r + l) := (xholds_run (r := r) (N := 3 * r + l) (l := l) rfl).mpr h'
  have := (lastExc_lastN hr).2 (3 * r + l) (by have := lastN_eq r; omega)
  exact this hx

theorem le_lstar_of_runOK {r l : ℕ} (hr : 1 ≤ r) (h : RunOK r l) : l ≤ lstar r := by
  by_contra hcon
  exact not_runOK_of_gt hr (not_le.mp hcon) h

/-- `ell*(r) = max {l : RunOK r l}`. -/
theorem lstar_spec {r : ℕ} (hr : 1 ≤ r) : IsGreatest {l | RunOK r l} (lstar r) :=
  ⟨runOK_lstar r, fun _ h => le_lstar_of_runOK hr h⟩

/-! ### Odd `r` -/

theorem not_runOK_of_odd {r l : ℕ} (hodd : Odd r) (hl : 1 ≤ l) : ¬ RunOK r l := by
  intro h
  have h1 : l < 2 ^ (Nat.log 2 l + 1) := Nat.lt_pow_succ_log_self (by norm_num) l
  have h2 : 2 ^ Nat.log 2 l ≤ l := Nat.pow_log_le_self 2 (by omega)
  have h3 : 2 ^ (Nat.log 2 l + 1) = 2 * 2 ^ Nat.log 2 l := by ring
  refine h (2 ^ (Nat.log 2 l + 1)) (by omega) (by omega) ?_
  exact Nat.Coprime.pow_left _ (Nat.coprime_two_left.mpr hodd)

/-- `N = 3r + 1` fails the criterion for odd `r`. -/
theorem not_xholds_three_add_one_of_odd {r : ℕ} (hodd : Odd r) : ¬ XHolds r (3 * r + 1) := by
  intro h
  exact not_runOK_of_odd hodd (le_refl 1) ((xholds_run (r := r) (N := 3 * r + 1) (l := 1) rfl).mp h)

/-- (b) For odd `r`, `ell*(r) = 0` and `lastN r = 3 r`. -/
theorem lstar_odd {r : ℕ} (hr : 1 ≤ r) (hodd : Odd r) : lstar r = 0 := by
  by_contra hne
  exact not_runOK_of_odd hodd (by omega) (runOK_lstar r)

theorem lastN_odd {r : ℕ} (hr : 1 ≤ r) (hodd : Odd r) : lastN r = 3 * r := by
  have := lastN_eq r
  have := lstar_odd hr hodd
  omega

/-! ### The upper bound `ell* < P+(r)` -/

/-- The largest prime factor of `r` (`0` if there is none). -/
def maxPrimeFactor (r : ℕ) : ℕ := r.primeFactors.sup id

theorem exists_prime_dvd_of_runOK {r l : ℕ} (hl : 1 ≤ l) (h : RunOK r l) :
    ∃ p, p.Prime ∧ p ∣ r ∧ l < p ∧ p ≤ 2 * l := by
  obtain ⟨p, hp, hlp, hp2⟩ := Nat.exists_prime_lt_and_le_two_mul l (by omega)
  have hnc := h p hlp hp2
  refine ⟨p, hp, ?_, hlp, hp2⟩
  by_contra hd
  exact hnc ((Nat.Prime.coprime_iff_not_dvd hp).mpr hd)

/-- (c) `ell*(r) < P+(r)` for `r ≥ 2`. -/
theorem lstar_lt_maxPrimeFactor {r : ℕ} (hr : 2 ≤ r) : lstar r < maxPrimeFactor r := by
  have hr0 : r ≠ 0 := by omega
  by_cases hl : lstar r = 0
  · rw [hl]
    obtain ⟨p, hp, hd⟩ := Nat.exists_prime_and_dvd (n := r) (by omega)
    have hmem : p ∈ r.primeFactors := Nat.mem_primeFactors.mpr ⟨hp, hd, hr0⟩
    have hle : p ≤ maxPrimeFactor r := Finset.le_sup (f := id) hmem
    have := hp.two_le
    omega
  · obtain ⟨p, hp, hd, hlp, _⟩ := exists_prime_dvd_of_runOK (by omega) (runOK_lstar r)
    have hmem : p ∈ r.primeFactors := Nat.mem_primeFactors.mpr ⟨hp, hd, hr0⟩
    have hle : p ≤ maxPrimeFactor r := Finset.le_sup (f := id) hmem
    omega

/-! ### The lower bound from the least prime not dividing `r` -/

theorem le_lstar_of_least_prime_not_dvd {r q : ℕ} (hr : 1 ≤ r) (hq : q.Prime)
    (hmin : ∀ p, p.Prime → p < q → p ∣ r) : (q - 1) / 2 ≤ lstar r := by
  apply le_lstar_of_runOK hr
  intro m h1 h2 hcop
  have hq2 := hq.two_le
  have hm1 : m ≠ 1 := by omega
  have hmpos : 0 < m := by omega
  have hp := Nat.minFac_prime hm1
  have hple : Nat.minFac m ≤ m := Nat.minFac_le hmpos
  have hpq : Nat.minFac m < q := by omega
  have hpr : Nat.minFac m ∣ r := hmin _ hp hpq
  have hpm : Nat.minFac m ∣ m := Nat.minFac_dvd m
  have h1' : Nat.minFac m ∣ Nat.gcd m r := Nat.dvd_gcd hpm hpr
  rw [Nat.Coprime.gcd_eq_one hcop] at h1'
  exact hp.one_lt.ne' (Nat.dvd_one.mp h1')

/-! ### The Jacobsthal function -/

/-- `m` such that every `m` consecutive integers contain one coprime to `r`. -/
def jacSet (r : ℕ) : Set ℕ := {m | 1 ≤ m ∧ ∀ a : ℕ, ∃ b, a ≤ b ∧ b < a + m ∧ Nat.Coprime b r}

/-- The Jacobsthal function `j(r)`: the least `m` such that every `m` consecutive integers contain one coprime to `r`. -/
noncomputable def jac (r : ℕ) : ℕ := sInf (jacSet r)

theorem r_mem_jacSet {r : ℕ} (hr : 1 ≤ r) : r ∈ jacSet r := by
  refine ⟨hr, fun a => ?_⟩
  have h := Nat.filter_coprime_Ico_eq_totient r a
  have hpos : 0 < Nat.totient r := Nat.totient_pos.mpr (by omega)
  rw [← h] at hpos
  obtain ⟨b, hb⟩ := Finset.card_pos.mp hpos
  rw [Finset.mem_filter, Finset.mem_Ico] at hb
  exact ⟨b, hb.1.1, hb.1.2, Nat.coprime_comm.mp hb.2⟩

theorem lstar_lt_of_mem_jacSet {r m : ℕ} (hr : 1 ≤ r) (hm : m ∈ jacSet r) : lstar r < m := by
  by_contra hcon
  have hle : m ≤ lstar r := not_lt.mp hcon
  obtain ⟨b, hb1, hb2, hb3⟩ := hm.2 (lstar r + 1)
  exact runOK_lstar r b hb1 (by omega) hb3

/-- (c) `ell*(r) ≤ j(r) - 1`. -/
theorem lstar_lt_jac {r : ℕ} (hr : 1 ≤ r) : lstar r < jac r :=
  lstar_lt_of_mem_jacSet hr (Nat.sInf_mem ⟨r, r_mem_jacSet hr⟩)

/-! ### Primorials -/

/-- For `r` divisible by every prime below the prime `P` and having only prime factors below `P`:
`ell*(r) = ⌊(P-1)/2⌋`. -/
theorem lstar_eq_of_primorial_like {r P : ℕ} (hr : 1 ≤ r) (hP : P.Prime)
    (hall : ∀ p, p.Prime → p < P → p ∣ r) (hfac : ∀ p, p.Prime → p ∣ r → p < P) :
    lstar r = (P - 1) / 2 := by
  have hP2 := hP.two_le
  have hPr : ¬ P ∣ r := fun h => lt_irrefl P (hfac P hP h)
  have hcopP : Nat.Coprime P r := (Nat.Prime.coprime_iff_not_dvd hP).mpr hPr
  apply le_antisymm
  · by_contra hcon
    have hgt : (P - 1) / 2 < lstar r := not_le.mp hcon
    have hl : P ≤ 2 * lstar r := by omega
    have hrun := runOK_lstar r
    by_cases hlP : lstar r < P
    · exact hrun P (by omega) hl hcopP
    · obtain ⟨p, hp, hlp, hp2⟩ := Nat.exists_prime_lt_and_le_two_mul (lstar r) (by omega)
      have hpr : ¬ p ∣ r := fun hd => by have := hfac p hp hd; omega
      exact hrun p hlp hp2 ((Nat.Prime.coprime_iff_not_dvd hp).mpr hpr)
  · exact le_lstar_of_least_prime_not_dvd hr hP hall

/-- A prime divides the primorial `n#` iff it is at most `n`. -/
theorem prime_dvd_primorial_iff {p n : ℕ} (hp : p.Prime) : p ∣ primorial n ↔ p ≤ n := by
  unfold primorial
  constructor
  · intro h
    obtain ⟨a, ha, hpa⟩ := (Prime.dvd_finsetProd_iff hp.prime _).mp h
    rw [Finset.mem_filter, Finset.mem_range] at ha
    have : p = a := (Nat.prime_dvd_prime_iff_eq hp ha.2).mp hpa
    omega
  · intro h
    exact Finset.dvd_prod_of_mem (fun x : ℕ => x)
      (Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), hp⟩)

/-- (iv) primorial formula: `ell*(n#) = ⌊(P'-1)/2⌋`, `P'` the next prime after `n`. -/
theorem lstar_primorial {n P : ℕ} (hP : P.Prime) (hn : n < P)
    (hmin : ∀ p, p.Prime → n < p → P ≤ p) : lstar (primorial n) = (P - 1) / 2 := by
  have hpr : 1 ≤ primorial n := by have := primorial_pos n; omega
  apply lstar_eq_of_primorial_like hpr hP
  · intro p hp hpP
    rw [prime_dvd_primorial_iff hp]
    by_contra h
    have := hmin p hp (by omega)
    omega
  · intro p hp hd
    have := (prime_dvd_primorial_iff hp).mp hd
    omega

/-- The six worked primorials, as statements about `primorial n`. -/
theorem lstar_primorial_2 : lstar (primorial 2) = 1 :=
  lstar_primorial (n := 2) (P := 3) (by norm_num) (by norm_num)
    (by intro p hp hnp; by_contra h; push_neg at h; interval_cases p <;> norm_num at hp)
theorem lstar_primorial_3 : lstar (primorial 3) = 2 :=
  lstar_primorial (n := 3) (P := 5) (by norm_num) (by norm_num)
    (by intro p hp hnp; by_contra h; push_neg at h; interval_cases p <;> norm_num at hp)
theorem lstar_primorial_5 : lstar (primorial 5) = 3 :=
  lstar_primorial (n := 5) (P := 7) (by norm_num) (by norm_num)
    (by intro p hp hnp; by_contra h; push_neg at h; interval_cases p <;> norm_num at hp)
theorem lstar_primorial_7 : lstar (primorial 7) = 5 :=
  lstar_primorial (n := 7) (P := 11) (by norm_num) (by norm_num)
    (by intro p hp hnp; by_contra h; push_neg at h; interval_cases p <;> norm_num at hp)
theorem lstar_primorial_11 : lstar (primorial 11) = 6 :=
  lstar_primorial (n := 11) (P := 13) (by norm_num) (by norm_num)
    (by intro p hp hnp; by_contra h; push_neg at h; interval_cases p <;> norm_num at hp)
theorem lstar_primorial_13 : lstar (primorial 13) = 8 :=
  lstar_primorial (n := 13) (P := 17) (by norm_num) (by norm_num)
    (by intro p hp hnp; by_contra h; push_neg at h; interval_cases p <;> norm_num at hp)

theorem primorial_vals :
    primorial 2 = 2 ∧ primorial 3 = 6 ∧ primorial 5 = 30 ∧ primorial 7 = 210 ∧
    primorial 11 = 2310 ∧ primorial 13 = 30030 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    first
    | norm_num [primorial, Finset.prod_filter, Finset.prod_range_succ]
    | decide +kernel
    | decide

/-- The same six values with the numerals `2, 6, 30, 210, 2310, 30030`. -/
theorem lstar_primorials :
    lstar 2 = 1 ∧ lstar 6 = 2 ∧ lstar 30 = 3 ∧ lstar 210 = 5 ∧ lstar 2310 = 6 ∧ lstar 30030 = 8 := by
  obtain ⟨h2, h3, h5, h7, h11, h13⟩ := primorial_vals
  have a2 := lstar_primorial_2
  have a3 := lstar_primorial_3
  have a5 := lstar_primorial_5
  have a7 := lstar_primorial_7
  have a11 := lstar_primorial_11
  have a13 := lstar_primorial_13
  rw [h2] at a2
  rw [h3] at a3
  rw [h5] at a5
  rw [h7] at a7
  rw [h11] at a11
  rw [h13] at a13
  exact ⟨a2, a3, a5, a7, a11, a13⟩

/-! ### Cross-check against the table of `ThmXTab` (independent route: finite check) -/

theorem lstar_r6_table : lstar 6 = 2 := by
  have := lastN_eq_of_lastExc (by norm_num) lastExc_r6
  have h := lastN_eq 6
  omega

theorem lstar_r30_table : lstar 30 = 3 := by
  have := lastN_eq_of_lastExc (by norm_num) lastExc_r30
  have h := lastN_eq 30
  omega

theorem lstar_r42_table : lstar 42 = 5 := by
  have := lastN_eq_of_lastExc (by norm_num) lastExc_r42
  have h := lastN_eq 42
  omega

end Gap
end Sext6
end LRSpectrumFull
