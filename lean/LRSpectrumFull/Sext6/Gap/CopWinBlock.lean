import Mathlib.Algebra.BigOperators.Associated
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Nat.GCD.BigOperators
import Mathlib.Data.Nat.Log
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Tactic

/-!
# CopWin, step 3: the two reusable block lemmas (B1 and C10 of the accompanying notes on the coprime-window route)  [2026-11-25]

* `block_coprime` (B1) : if every prime `q < m` divides `P`, then `P (a+i) + 1` and `P (a+j) + 1` are coprime
  for `i < j < m` (a common prime would divide `P (j - i)`, hence `j - i < m`, hence `P`, hence `1`).
* `bad_card_le`  (C10) : in a pairwise coprime family of integers `> 1`, at most `Nat.log 2 r` members share a
  factor with `r ≥ 1` (a shared prime of `gcd(p, r)` is distinct for distinct members and these primes
  multiply to a divisor of `r`).
Both are elementary; neither mentions primality of the family.  No `sorry`, no `axiom`.

Convention: No speed vector is involved in this module (number theory or real analysis); `N` denotes a natural number, the size of the ambient interval `[1,N]`.
Hypotheses: those of the individual statements (numerical bounds, structural conditions and, where named in the list above, window predicates such as `PrimeWin`, `CopWin`, `PrimeWindow7`, which later modules discharge for explicit ranges). The unproved predicates `DusartPi`, `LRCHyp`, `CopWinHyp` are not hypotheses of any statement in this module.
Axiom audit: covered by `CopWinAxioms11` (`#print axioms`; declarations not printed there are bricks of printed ones, so their axioms are bounded by the printed lines).
-/

namespace LRSpectrumFull
namespace Sext6
namespace Gap

/-- **B1.** An arithmetic-progression block: `P (a+i) + 1` for `i < m` is pairwise coprime when every prime
below `m` divides `P`. -/
theorem block_coprime {P m a i j : ℕ} (hP : ∀ q : ℕ, q.Prime → q < m → q ∣ P)
    (hij : i < j) (hjm : j < m) :
    Nat.Coprime (P * (a + i) + 1) (P * (a + j) + 1) := by
  by_contra hnc
  obtain ⟨q, hq, hq1, hq2⟩ := Nat.Prime.not_coprime_iff_dvd.mp hnc
  have e : P * (a + j) + 1 = (P * (a + i) + 1) + P * (j - i) := by
    obtain ⟨d, rfl⟩ : ∃ d, j = i + d := ⟨j - i, by omega⟩
    rw [Nat.add_sub_cancel_left]
    ring
  have h3 : q ∣ P * (j - i) := (Nat.dvd_add_right hq1).mp (by rw [← e]; exact hq2)
  have hqP : q ∣ P := by
    rcases (Nat.Prime.dvd_mul hq).mp h3 with h | h
    · exact h
    · have hle : q ≤ j - i := Nat.le_of_dvd (by omega) h
      exact hP q hq (by omega)
  have h4 : q ∣ 1 := (Nat.dvd_add_right (dvd_mul_of_dvd_left hqP _)).mp hq1
  exact Nat.Prime.not_dvd_one hq h4

/-- **C10.** In a pairwise coprime family of integers `> 1`, at most `Nat.log 2 r` members are not coprime
to `r ≥ 1`. -/
theorem bad_card_le {P : Finset ℕ} {r : ℕ} (hcop : (P : Set ℕ).Pairwise Nat.Coprime)
    (h1 : ∀ p ∈ P, 1 < p) (hr : 1 ≤ r) :
    (P.filter (fun p => ¬ Nat.Coprime p r)).card ≤ Nat.log 2 r := by
  classical
  set Q := P.filter (fun p => ¬ Nat.Coprime p r) with hQ
  have hQP : ∀ p ∈ Q, p ∈ P := fun p hp => (Finset.mem_filter.mp hp).1
  let f : ℕ → ℕ := fun p => Nat.minFac (Nat.gcd p r)
  have hf_prime : ∀ p ∈ Q, (f p).Prime := by
    intro p hp
    have hnc : ¬ Nat.Coprime p r := (Finset.mem_filter.mp hp).2
    exact Nat.minFac_prime hnc
  have hf_dvd_p : ∀ p ∈ Q, f p ∣ p := fun p _ => (Nat.minFac_dvd _).trans (Nat.gcd_dvd_left p r)
  have hf_dvd_r : ∀ p ∈ Q, f p ∣ r := fun p _ => (Nat.minFac_dvd _).trans (Nat.gcd_dvd_right p r)
  have hinj : Set.InjOn f (Q : Set ℕ) := by
    intro p hp q hq hfe
    by_contra hne
    have hpq : Nat.Coprime p q :=
      hcop (Finset.mem_coe.mpr (hQP p (Finset.mem_coe.mp hp)))
        (Finset.mem_coe.mpr (hQP q (Finset.mem_coe.mp hq))) hne
    have hdq : f p ∣ q := hfe ▸ hf_dvd_p q (Finset.mem_coe.mp hq)
    have hd : f p ∣ Nat.gcd p q := Nat.dvd_gcd (hf_dvd_p p (Finset.mem_coe.mp hp)) hdq
    rw [Nat.Coprime.gcd_eq_one hpq] at hd
    exact Nat.Prime.not_dvd_one (hf_prime p (Finset.mem_coe.mp hp)) hd
  have hcard : (Q.image f).card = Q.card := Finset.card_image_of_injOn hinj
  have himg_prime : ∀ a ∈ Q.image f, a.Prime := by
    intro a ha
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp ha
    exact hf_prime p hp
  have himg_dvd : ∀ a ∈ Q.image f, a ∣ r := by
    intro a ha
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp ha
    exact hf_dvd_r p hp
  have hprod : (∏ a ∈ Q.image f, a) ∣ r :=
    Finset.prod_primes_dvd r (fun a ha => (himg_prime a ha).prime) himg_dvd
  have hle : ∏ a ∈ Q.image f, a ≤ r := Nat.le_of_dvd (by omega) hprod
  have hpow : 2 ^ (Q.image f).card ≤ ∏ a ∈ Q.image f, a :=
    Finset.pow_card_le_prod (Q.image f) (fun a => a) 2 (fun a ha => (himg_prime a ha).two_le)
  rw [hcard] at hpow
  exact Nat.le_log_of_pow_le (by norm_num) (hpow.trans hle)

end Gap
end Sext6
end LRSpectrumFull
