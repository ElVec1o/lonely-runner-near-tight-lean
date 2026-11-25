import Mathlib.Algebra.BigOperators.Associated
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Tactic

/-!
# Theorem S (k-robustness of the one-entry theorem): spoiled-prime count and scale chain  [2026-11-25]

Source: the accompanying notes on Theorem S (Lemmas C and S).

* `prime_pow_card_le`   : distinct primes `≥ B` all dividing `M > 0` give `B ^ card ≤ M`.
* `card_dvd_le`         : hence `M < B^(c+1)` forces at most `c` such primes.
* `BadAt`, `spoilSet`   : a prime `p` is *spoiled by* the speed `w` if `p ∣ w`, `w - r`, or `w + r` (in `ℤ`).
* `spoil_single_card_le`: `w + r < (N+2)^(2j+1)`, window primes `≥ N+2`  ⟹  at most `6 j` spoiled primes.
* `chain`               : the scale split of Lemma C, by induction on the number of added speeds,
                          carrying the spoiled-prime budget `Σ_{a<i} 6 (a+1) = 3 i (i+1)`.
No `sorry`, no `axiom`.

Convention: No speed vector is involved in this module (number theory or real analysis); `N` denotes a natural number, the size of the ambient interval `[1,N]`.
Hypotheses: those of the individual statements (numerical bounds, structural conditions and, where named in the list above, window predicates such as `PrimeWin`, `CopWin`, `PrimeWindow7`, which later modules discharge for explicit ranges). The unproved predicates `DusartPi`, `LRCHyp`, `CopWinHyp` are not hypotheses of any statement in this module.
Axiom audit: covered by `Axioms7` (first); every later audit module imports this module (`#print axioms`; declarations not printed there are bricks of printed ones, so their axioms are bounded by the printed lines).
-/

namespace LRSpectrumFull
namespace Sext6
namespace Gap

/-- Distinct primes, each `≥ B`, dividing a positive `M`: `B ^ card ≤ M`. -/
theorem prime_pow_card_le {S : Finset ℕ} {B M : ℕ} (hprime : ∀ p ∈ S, p.Prime)
    (hB : ∀ p ∈ S, B ≤ p) (hM : 0 < M) (hdvd : ∀ p ∈ S, p ∣ M) : B ^ S.card ≤ M := by
  have h1 : (∏ p ∈ S, p) ∣ M := Finset.prod_primes_dvd M (fun p hp => (hprime p hp).prime) hdvd
  have h2 : ∏ p ∈ S, p ≤ M := Nat.le_of_dvd hM h1
  have h3 : B ^ S.card ≤ ∏ p ∈ S, p := Finset.pow_card_le_prod S (fun p => p) B hB
  exact h3.trans h2

/-- At most `c` primes `≥ B` divide a positive `M < B ^ (c+1)`. -/
theorem card_dvd_le {S : Finset ℕ} {B M c : ℕ} (hprime : ∀ p ∈ S, p.Prime)
    (hB : ∀ p ∈ S, B ≤ p) (hB1 : 0 < B) (hM : 0 < M) (hdvd : ∀ p ∈ S, p ∣ M)
    (hlt : M < B ^ (c + 1)) : S.card ≤ c := by
  by_contra h
  have h' : c < S.card := not_le.mp h
  have h1 := prime_pow_card_le hprime hB hM hdvd
  have h2 : B ^ (c + 1) ≤ B ^ S.card := Nat.pow_le_pow_right hB1 (by omega)
  omega

/-- `p` fails the witness test for the speed `w` (residue `0`, `r` or `-r` mod `p`). -/
def BadAt (r p w : ℕ) : Prop :=
  ((p : ℤ) ∣ (w : ℤ)) ∨ ((p : ℤ) ∣ (w : ℤ) - (r : ℤ)) ∨ ((p : ℤ) ∣ (w : ℤ) + (r : ℤ))

open Classical in
/-- The primes of `P` spoiled by some speed of `S`. -/
noncomputable def spoilSet (P : Finset ℕ) (r : ℕ) (S : Finset ℕ) : Finset ℕ :=
  P.filter (fun p => ∃ w ∈ S, BadAt r p w)

theorem mem_spoilSet {P : Finset ℕ} {r p : ℕ} {S : Finset ℕ} :
    p ∈ spoilSet P r S ↔ p ∈ P ∧ ∃ w ∈ S, BadAt r p w := by
  classical
  unfold spoilSet
  exact Finset.mem_filter

/-- **Lemma S (single speed).** Window primes `≥ N + 2`, `r < w`, `w + r < (N+2)^(2j+1)`:
at most `6 j` primes of `P` are spoiled by `w`. -/
theorem spoil_single_card_le {P : Finset ℕ} {N r w j : ℕ}
    (hP : ∀ p ∈ P, p.Prime ∧ N + 2 ≤ p) (hrw : r < w)
    (hwr : w + r < (N + 2) ^ (2 * j + 1)) :
    (spoilSet P r {w}).card ≤ 6 * j := by
  have key : ∀ M : ℕ, 0 < M → M ≤ w + r → (P.filter (fun p => p ∣ M)).card ≤ 2 * j := by
    intro M hM hMle
    exact card_dvd_le (B := N + 2) (c := 2 * j)
      (fun p hp => (hP p (Finset.mem_filter.mp hp).1).1)
      (fun p hp => (hP p (Finset.mem_filter.mp hp).1).2) (by omega) hM
      (fun p hp => (Finset.mem_filter.mp hp).2) (lt_of_le_of_lt hMle hwr)
  have hsub : spoilSet P r {w} ⊆ (P.filter (fun p => p ∣ w)) ∪ (P.filter (fun p => p ∣ w - r))
      ∪ (P.filter (fun p => p ∣ w + r)) := by
    intro p hp
    rw [mem_spoilSet] at hp
    obtain ⟨hpP, w', hw', hbad⟩ := hp
    rw [Finset.mem_singleton] at hw'
    rw [hw'] at hbad
    unfold BadAt at hbad
    simp only [Finset.mem_union, Finset.mem_filter]
    rcases hbad with h | h | h
    · exact Or.inl (Or.inl ⟨hpP, Int.natCast_dvd_natCast.mp h⟩)
    · refine Or.inl (Or.inr ⟨hpP, ?_⟩)
      have hcast : ((w - r : ℕ) : ℤ) = (w : ℤ) - (r : ℤ) := by omega
      exact Int.natCast_dvd_natCast.mp (by rw [hcast]; exact h)
    · refine Or.inr ⟨hpP, ?_⟩
      have hcast : ((w + r : ℕ) : ℤ) = (w : ℤ) + (r : ℤ) := by push_cast; ring
      exact Int.natCast_dvd_natCast.mp (by rw [hcast]; exact h)
  have hu1 := Finset.card_union_le (P.filter (fun p => p ∣ w)) (P.filter (fun p => p ∣ w - r))
  have hu2 := Finset.card_union_le ((P.filter (fun p => p ∣ w)) ∪ (P.filter (fun p => p ∣ w - r)))
    (P.filter (fun p => p ∣ w + r))
  have hc := Finset.card_le_card hsub
  have h0 := key w (by omega) (by omega)
  have h1 := key (w - r) (by omega) (by omega)
  have h2 := key (w + r) (by omega) le_rfl
  omega

/-- The spoiled primes of `insert w S`. -/
theorem spoilSet_insert_card {P : Finset ℕ} {r w : ℕ} {S : Finset ℕ} :
    (spoilSet P r (insert w S)).card ≤ (spoilSet P r {w}).card + (spoilSet P r S).card := by
  have hsub : spoilSet P r (insert w S) ⊆ spoilSet P r {w} ∪ spoilSet P r S := by
    intro p hp
    rw [mem_spoilSet] at hp
    obtain ⟨hpP, w', hw', hbad⟩ := hp
    rw [Finset.mem_union, mem_spoilSet, mem_spoilSet]
    rcases Finset.mem_insert.mp hw' with h | h
    · exact Or.inl ⟨hpP, w', Finset.mem_singleton.mpr h, hbad⟩
    · exact Or.inr ⟨hpP, w', h, hbad⟩
  exact (Finset.card_le_card hsub).trans (Finset.card_union_le _ _)

theorem spoilSet_empty (P : Finset ℕ) (r : ℕ) : spoilSet P r ∅ = ∅ := by
  ext p
  rw [mem_spoilSet]
  simp

/-- `N^n + r < (N+2)^n` for odd `n = 2m+1 ≥ 3`, `r ≤ N`. -/
theorem pow_add_lt {N r m : ℕ} (hN : 1 ≤ N) (hrN : r ≤ N) (hm : 1 ≤ m) :
    N ^ (2 * m + 1) + r < (N + 2) ^ (2 * m + 1) := by
  have h1 : N ^ (2 * m) ≤ (N + 2) ^ (2 * m) := Nat.pow_le_pow_left (by omega) _
  have h2 : N ≤ N ^ (2 * m) := Nat.le_self_pow (by omega) N
  have e1 : N ^ (2 * m + 1) = N ^ (2 * m) * N := pow_succ N (2 * m)
  have e2 : (N + 2) ^ (2 * m + 1) = (N + 2) ^ (2 * m) * (N + 2) := pow_succ (N + 2) (2 * m)
  rw [e1, e2]
  have h3 : N ^ (2 * m) * (N + 2) ≤ (N + 2) ^ (2 * m) * (N + 2) := Nat.mul_le_mul_right _ h1
  have h4 : N ^ (2 * m) * (N + 2) = N ^ (2 * m) * N + 2 * N ^ (2 * m) := by ring
  omega

/-- The conclusion of the scale split (Lemma C) together with the spoiled-prime budget. -/
def ChainConcl (N c : ℕ) (P : Finset ℕ) (r : ℕ) (R : Finset ℕ) (L j : ℕ) : Prop :=
  ∃ S ⊆ R, ∃ L' : ℕ, L ≤ L' ∧ (∀ x ∈ S, x ≤ L') ∧ L' ≤ c ^ (j + S.card) * N ∧
    (∀ u ∈ R, u ∉ S → c * L' < u) ∧
    (spoilSet P r S).card ≤ ∑ a ∈ Finset.range S.card, 6 * (j + a + 1)

theorem chain_nil {N c : ℕ} {P : Finset ℕ} {r : ℕ} (R : Finset ℕ) (L j : ℕ)
    (hLj : L ≤ c ^ j * N) (h : ∀ u ∈ R, c * L < u) : ChainConcl N c P r R L j := by
  refine ⟨∅, Finset.empty_subset R, L, le_rfl, by simp, by simpa using hLj,
    fun u hu _ => h u hu, ?_⟩
  rw [spoilSet_empty]
  simp

/-- **Lemma C + Lemma S budget (induction).**  Peel the smallest remaining speed `w`: if `w ≤ c L`
it joins the small speeds (index `j+1`, size `≤ c^(j+1) N ≤ N^(2(j+1)+1)`), otherwise every
remaining speed exceeds `c L`. -/
theorem chain {N r c : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ N + 2 ≤ p) (hN : 1 ≤ N)
    (hrN : r ≤ N) (hc : c ≤ N * N) :
    ∀ (n : ℕ) (R : Finset ℕ) (L j : ℕ), R.card ≤ n → N ≤ L → L ≤ c ^ j * N →
      (∀ x ∈ R, L < x) → ChainConcl N c P r R L j := by
  intro n
  induction n with
  | zero =>
    intro R L j hR hNL hLj hRL
    have hR0 : R = ∅ := Finset.card_eq_zero.mp (by omega)
    exact chain_nil R L j hLj (by rw [hR0]; simp)
  | succ n ih =>
    intro R L j hR hNL hLj hRL
    by_cases hne : R.Nonempty
    · have hwR : R.min' hne ∈ R := Finset.min'_mem R hne
      have hmin : ∀ x ∈ R, R.min' hne ≤ x := fun x hx => Finset.min'_le R x hx
      obtain ⟨w, hw⟩ : ∃ w, w = R.min' hne := ⟨_, rfl⟩
      rw [← hw] at hwR hmin
      by_cases hbig : c * L < w
      · exact chain_nil R L j hLj (fun u hu => lt_of_lt_of_le hbig (hmin u hu))
      · have hwL : L < w := hRL w hwR
        have hwle : w ≤ c ^ (j + 1) * N := by
          calc w ≤ c * L := not_lt.mp hbig
            _ ≤ c * (c ^ j * N) := Nat.mul_le_mul_left c hLj
            _ = c ^ (j + 1) * N := by ring
        have hR' : (R.erase w).card ≤ n := by
          have := Finset.card_erase_of_mem hwR
          omega
        obtain ⟨S', hS'R, L', hLL', hS'L, hL'c, hlarge, hsp⟩ :=
          ih (R.erase w) w (j + 1) hR' (by omega) hwle (by
            intro x hx
            have hx' := Finset.mem_erase.mp hx
            exact lt_of_le_of_ne (hmin x hx'.2) (Ne.symm hx'.1))
        have hnot : w ∉ S' := fun h => (Finset.mem_erase.mp (hS'R h)).1 rfl
        have hcpow : c ^ (j + 1) ≤ N ^ (2 * (j + 1)) := by
          calc c ^ (j + 1) ≤ (N * N) ^ (j + 1) := Nat.pow_le_pow_left hc _
            _ = N ^ (2 * (j + 1)) := by rw [← pow_two, ← pow_mul]
        have hw1 : w ≤ N ^ (2 * (j + 1) + 1) := by
          calc w ≤ c ^ (j + 1) * N := hwle
            _ ≤ N ^ (2 * (j + 1)) * N := Nat.mul_le_mul_right N hcpow
            _ = N ^ (2 * (j + 1) + 1) := (pow_succ N _).symm
        have hw2 := pow_add_lt (N := N) (r := r) (m := j + 1) hN hrN (by omega)
        have hsingle : (spoilSet P r {w}).card ≤ 6 * (j + 1) :=
          spoil_single_card_le hP (by omega) (by omega)
        have hsum : ∑ a ∈ Finset.range (S'.card + 1), 6 * (j + a + 1) =
            ∑ a ∈ Finset.range S'.card, 6 * (j + 1 + a + 1) + 6 * (j + 1) := by
          have h1 : ∑ a ∈ Finset.range S'.card, 6 * (j + (a + 1) + 1) =
              ∑ a ∈ Finset.range S'.card, 6 * (j + 1 + a + 1) :=
            Finset.sum_congr rfl (fun a _ => by ring)
          rw [Finset.sum_range_succ', h1]
        refine ⟨insert w S', ?_, L', by omega, ?_, ?_, ?_, ?_⟩
        · exact Finset.insert_subset_iff.mpr ⟨hwR, hS'R.trans (Finset.erase_subset w R)⟩
        · intro x hx
          rcases Finset.mem_insert.mp hx with h | h
          · rw [h]; exact hLL'
          · exact hS'L x h
        · rw [Finset.card_insert_of_notMem hnot]
          have e : j + (S'.card + 1) = j + 1 + S'.card := by ring
          rw [e]
          exact hL'c
        · intro u hu hu'
          have hne' : u ≠ w := fun h => hu' (by rw [h]; exact Finset.mem_insert_self _ _)
          have hnS : u ∉ S' := fun h => hu' (Finset.mem_insert_of_mem h)
          exact hlarge u (Finset.mem_erase.mpr ⟨hne', hu⟩) hnS
        · rw [Finset.card_insert_of_notMem hnot, hsum]
          have := spoilSet_insert_card (P := P) (r := r) (w := w) (S := S')
          omega
    · have hR0 : R = ∅ := Finset.not_nonempty_iff_eq_empty.mp hne
      exact chain_nil R L j hLj (by rw [hR0]; simp)

/-- `Σ_{a<i} 6 (0 + a + 1) = 3 i (i+1)`. -/
theorem sum_six (i : ℕ) : ∑ a ∈ Finset.range i, 6 * (0 + a + 1) = 3 * i * (i + 1) := by
  induction i with
  | zero => simp
  | succ i ih => rw [Finset.sum_range_succ, ih]; ring

end Gap
end Sext6
end LRSpectrumFull
