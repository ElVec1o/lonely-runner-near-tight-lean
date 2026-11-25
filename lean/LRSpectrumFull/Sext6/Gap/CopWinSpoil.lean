import LRSpectrumFull.Sext6.Gap.RobustSpoil

/-!
# CopWin, step 1: pairwise-coprime versions of the spoiled-modulus count and the scale chain  [2026-11-25]

Route G of the accompanying notes on the coprime-window route.  New file; `RobustSpoil.lean` is untouched.

* `prod_dvd_of_pairwise_coprime` : pairwise coprime divisors of `M` have a product dividing `M`.
* `cop_pow_card_le`   : pairwise coprime family, each `≥ B`, all dividing `M > 0`: `B ^ card ≤ M`.
* `cop_card_dvd_le`   : hence `M < B^(c+1)` forces at most `c` such members.
* `spoil_single_card_le_cop` : Lemma S with "pairwise coprime" in place of "prime".
* `chain_cop`         : Lemma C + budget, same induction as `chain`.
Primality is not used anywhere in this file.  No `sorry`, no `axiom`.

Convention: No speed vector is involved in this module (number theory or real analysis); `N` denotes a natural number, the size of the ambient interval `[1,N]`.
Hypotheses: those of the individual statements (numerical bounds, structural conditions and, where named in the list above, window predicates such as `PrimeWin`, `CopWin`, `PrimeWindow7`, which later modules discharge for explicit ranges). The unproved predicates `DusartPi`, `LRCHyp`, `CopWinHyp` are not hypotheses of any statement in this module.
Axiom audit: covered by `CopWinAxioms11` (first); every later audit module imports this module (`#print axioms`; declarations not printed there are bricks of printed ones, so their axioms are bounded by the printed lines).
-/

namespace LRSpectrumFull
namespace Sext6
namespace Gap

/-- Pairwise coprime divisors of `M`: their product divides `M`. -/
theorem prod_dvd_of_pairwise_coprime {S : Finset ℕ} {M : ℕ}
    (hcop : (S : Set ℕ).Pairwise Nat.Coprime) (hdvd : ∀ p ∈ S, p ∣ M) :
    (∏ p ∈ S, p) ∣ M := by
  classical
  induction S using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.prod_insert ha]
    have hs : (s : Set ℕ).Pairwise Nat.Coprime :=
      hcop.mono (Finset.coe_subset.mpr (Finset.subset_insert a s))
    have h1 := ih hs (fun p hp => hdvd p (Finset.mem_insert_of_mem hp))
    have h2 : Nat.Coprime a (∏ p ∈ s, p) := by
      apply Nat.Coprime.prod_right
      intro i hi
      have hne : a ≠ i := fun h => ha (h ▸ hi)
      exact hcop (Finset.mem_coe.mpr (Finset.mem_insert_self a s))
        (Finset.mem_coe.mpr (Finset.mem_insert_of_mem hi)) hne
    exact h2.mul_dvd_of_dvd_of_dvd (hdvd a (Finset.mem_insert_self a s)) h1

/-- Pairwise coprime family, each `≥ B`, all dividing a positive `M`: `B ^ card ≤ M`. -/
theorem cop_pow_card_le {S : Finset ℕ} {B M : ℕ} (hcop : (S : Set ℕ).Pairwise Nat.Coprime)
    (hB : ∀ p ∈ S, B ≤ p) (hM : 0 < M) (hdvd : ∀ p ∈ S, p ∣ M) : B ^ S.card ≤ M := by
  have h1 : (∏ p ∈ S, p) ∣ M := prod_dvd_of_pairwise_coprime hcop hdvd
  have h2 : ∏ p ∈ S, p ≤ M := Nat.le_of_dvd hM h1
  have h3 : B ^ S.card ≤ ∏ p ∈ S, p := Finset.pow_card_le_prod S (fun p => p) B hB
  exact h3.trans h2

/-- At most `c` members `≥ B` of a pairwise coprime family divide a positive `M < B ^ (c+1)`. -/
theorem cop_card_dvd_le {S : Finset ℕ} {B M c : ℕ} (hcop : (S : Set ℕ).Pairwise Nat.Coprime)
    (hB : ∀ p ∈ S, B ≤ p) (hB1 : 0 < B) (hM : 0 < M) (hdvd : ∀ p ∈ S, p ∣ M)
    (hlt : M < B ^ (c + 1)) : S.card ≤ c := by
  by_contra h
  have h' : c < S.card := not_le.mp h
  have h1 := cop_pow_card_le hcop hB hM hdvd
  have h2 : B ^ (c + 1) ≤ B ^ S.card := Nat.pow_le_pow_right hB1 (by omega)
  omega

/-- **Lemma S (single speed), pairwise coprime form.**  Window members pairwise coprime and `≥ N + 2`,
`r < w`, `w + r < (N+2)^(2j+1)`: at most `6 j` members of `P` are spoiled by `w`. -/
theorem spoil_single_card_le_cop {P : Finset ℕ} {N r w j : ℕ}
    (hPc : (P : Set ℕ).Pairwise Nat.Coprime) (hPB : ∀ p ∈ P, N + 2 ≤ p) (hrw : r < w)
    (hwr : w + r < (N + 2) ^ (2 * j + 1)) :
    (spoilSet P r {w}).card ≤ 6 * j := by
  have key : ∀ M : ℕ, 0 < M → M ≤ w + r → (P.filter (fun p => p ∣ M)).card ≤ 2 * j := by
    intro M hM hMle
    exact cop_card_dvd_le (B := N + 2) (c := 2 * j)
      (hPc.mono (Finset.coe_subset.mpr (Finset.filter_subset _ _)))
      (fun p hp => hPB p (Finset.mem_filter.mp hp).1) (by omega) hM
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

/-- **Lemma C + Lemma S budget (induction), pairwise coprime form.** -/
theorem chain_cop {N r c : ℕ} {P : Finset ℕ} (hPc : (P : Set ℕ).Pairwise Nat.Coprime)
    (hPB : ∀ p ∈ P, N + 2 ≤ p) (hN : 1 ≤ N)
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
          spoil_single_card_le_cop hPc hPB (by omega) (by omega)
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

end Gap
end Sext6
end LRSpectrumFull
