/-
# PairCount: the pair-agreement counting argument (F3)  [AL, 2026-11-24]

Central idea: a clean prime `p` that divides no speed labels the speeds by a signed permutation of `1..6`
(`PairLabel`).  Fix one such prime `p0`; every other such prime `q` agrees with the labeling of `p0`
(`PairAgree`), so every surviving prime divides the one integer `N_kl = eps_l (s_l+1) v_k - eps_k (s_k+1) v_l`
of size at most `11 B`.  If `N_kl != 0`, the product of the surviving primes is at most `11 B`; the count
of primes needed to exceed `11 B` is `kappa' = beta(11 B) + 1`.  The primes lost to the speeds are at most
`6 beta(B)`.  So `|P| >= 6 beta(B) + beta(11 B) + 1` forces `N_kl = 0` for all `k != l`, i.e. all ratios are `a/b`.

`betaOf P X` = largest `r <= |P|` with `(r smallest primes of P).prod <= X`  (sorted ascending list).
`prefix_prod_le`: any `r` distinct elements of `P` have product `>= (r smallest).prod`.
-/
import LRSpectrumFull.Sext6.PairLabel
import LRSpectrumFull.Sext6.Box

namespace LRSpectrumFull
namespace Sext6

/-! ### r distinct elements of a sorted list have product at least that of the r smallest -/

theorem take_prod_cons_le : ∀ (L : List ℕ) (a r : ℕ), (a :: L).Pairwise (· < ·) → r ≤ L.length →
    ((a :: L).take r).prod ≤ (L.take r).prod := by
  intro L
  induction L with
  | nil =>
    intro a r _ hr
    have : r = 0 := by simpa using hr
    subst this
    simp
  | cons b L ih =>
    intro a r hP hr
    cases r with
    | zero => simp
    | succ r =>
      have hab : a < b := (List.pairwise_cons.1 hP).1 b (by simp)
      have hP' : (b :: L).Pairwise (· < ·) := (List.pairwise_cons.1 hP).2
      have h1 := ih b r hP' (by simpa using hr)
      simp only [List.take_succ_cons, List.prod_cons]
      exact Nat.mul_le_mul hab.le h1

theorem prefix_prod_le (L : List ℕ) (hL : L.Pairwise (· < ·)) : ∀ (S : Finset ℕ),
    (∀ x ∈ S, x ∈ L) → (L.take S.card).prod ≤ ∏ x ∈ S, x := by
  induction L with
  | nil =>
    intro S hS
    have : S = ∅ := Finset.eq_empty_of_forall_notMem (fun x hx => by simpa using hS x hx)
    subst this
    simp
  | cons a L ih =>
    intro S hS
    have hL' : L.Pairwise (· < ·) := (List.pairwise_cons.1 hL).2
    by_cases ha : a ∈ S
    · have hS' : ∀ x ∈ S.erase a, x ∈ L := by
        intro x hx
        have h1 := Finset.mem_erase.1 hx
        have := hS x h1.2
        simpa [h1.1] using this
      have hc : S.card = (S.erase a).card + 1 := (Finset.card_erase_add_one ha).symm
      have h2 := ih hL' (S.erase a) hS'
      have e : ∏ x ∈ S, x = a * ∏ x ∈ S.erase a, x := (Finset.mul_prod_erase S (fun x => x) ha).symm
      rw [hc, List.take_succ_cons, List.prod_cons, e]
      exact Nat.mul_le_mul_left a h2
    · have hS' : ∀ x ∈ S, x ∈ L := by
        intro x hx
        have := hS x hx
        rcases List.mem_cons.1 this with h | h
        · exact absurd (h ▸ hx) ha
        · exact h
      have h1 := ih hL' S hS'
      have hcard : S.card ≤ L.length := by
        calc S.card ≤ L.toFinset.card :=
              Finset.card_le_card (fun x hx => List.mem_toFinset.2 (hS' x hx))
          _ ≤ L.length := List.toFinset_card_le L
      exact (take_prod_cons_le L a S.card hL hcard).trans h1

/-- `beta(X)`: the largest `r <= |P|` such that the product of the `r` smallest elements of `P` is `<= X`. -/
def betaOf (P : List ℕ) (X : ℕ) : ℕ := Nat.findGreatest (fun r => (P.take r).prod ≤ X) P.length

/-- At most `beta(X)` primes of the sorted list `P` divide a number `0 < m <= X`. -/
theorem card_le_betaOf (P : List ℕ) (hP : P.Pairwise (· < ·)) (S : Finset ℕ)
    (hSP : ∀ x ∈ S, x ∈ P) (hSp : ∀ x ∈ S, x.Prime) (m X : ℕ) (hm : 0 < m) (hmX : m ≤ X)
    (hd : ∀ p ∈ S, p ∣ m) : S.card ≤ betaOf P X := by
  have h1 : ∏ p ∈ S, p ∣ m := Finset.prod_primes_dvd m (fun p hp => (hSp p hp).prime) hd
  have h2 : ∏ p ∈ S, p ≤ X := (Nat.le_of_dvd hm h1).trans hmX
  have h3 := prefix_prod_le P hP S hSP
  have hcard : S.card ≤ P.length := by
    calc S.card ≤ P.toFinset.card :=
          Finset.card_le_card (fun x hx => List.mem_toFinset.2 (hSP x hx))
      _ ≤ P.length := List.toFinset_card_le P
  exact Nat.le_findGreatest hcard (h3.trans h2)

/-! ### the data and the pair lemma -/

/-- A strictly increasing list of primes `>= 313`, each clean. -/
structure PairData (P : List ℕ) : Prop where
  sorted : P.Pairwise (· < ·)
  prime : ∀ p ∈ P, p.Prime
  ge : ∀ p ∈ P, 313 ≤ p
  clean : ∀ p ∈ P, CleanPrime p

/-- `ResidueData` restricted to the listed primes (computed hypothesis, uncertified). -/
def ResidueDataSub (P : List ℕ) : Prop := ∀ p ∈ P, p.Prime ∧ CleanPrime p

theorem PairData.mk' (P : List ℕ) (hs : P.Pairwise (· < ·)) (hg : ∀ p ∈ P, 313 ≤ p)
    (hr : ResidueDataSub P) : PairData P :=
  ⟨hs, fun p hp => (hr p hp).1, hg, fun p hp => (hr p hp).2⟩

theorem pairs_of_data (P : List ℕ) (hP : PairData P) (B : ℕ)
    (hcnt : 6 * betaOf P B + betaOf P (11 * B) + 1 ≤ P.length) : PairsIn B := by
  intro v hpos hB hML i j hij
  have hnodup : P.Nodup := hP.sorted.imp (fun h => ne_of_lt h)
  set Pf := P.toFinset with hPf
  have hmem : ∀ x ∈ Pf, x ∈ P := fun x hx => List.mem_toFinset.1 hx
  have hcardP : Pf.card = P.length := List.toFinset_card_of_nodup hnodup
  have hBabs : ∀ k, |v k| ≤ (B : ℤ) := fun k => by rw [abs_of_pos (hpos k)]; exact hB k
  -- primes dividing a speed
  set D := Pf.filter (fun p : ℕ => ∃ k, (p : ℤ) ∣ v k) with hD
  set U := Pf.filter (fun p : ℕ => ¬ ∃ k, (p : ℤ) ∣ v k) with hU
  have hDcard : D.card ≤ 6 * betaOf P B := by
    have hsub : D ⊆ Finset.univ.biUnion (fun k : Fin 6 => Pf.filter (fun p : ℕ => (p : ℤ) ∣ v k)) := by
      intro p hp
      obtain ⟨hpP, k, hk⟩ := Finset.mem_filter.mp hp
      exact Finset.mem_biUnion.mpr ⟨k, Finset.mem_univ _, Finset.mem_filter.mpr ⟨hpP, hk⟩⟩
    have hk2 : ∀ k : Fin 6, (Pf.filter (fun p : ℕ => (p : ℤ) ∣ v k)).card ≤ betaOf P B := by
      intro k
      have h1 := hpos k
      have h2 := hB k
      exact card_le_betaOf P hP.sorted _ (fun x hx => hmem x (Finset.mem_filter.mp hx).1)
        (fun x hx => hP.prime x (hmem x (Finset.mem_filter.mp hx).1)) (v k).natAbs B (by omega)
        (by omega) (fun p hp => Int.ofNat_dvd_left.mp (Finset.mem_filter.mp hp).2)
    calc D.card ≤ (Finset.univ.biUnion (fun k : Fin 6 => Pf.filter (fun p : ℕ => (p : ℤ) ∣ v k))).card :=
          Finset.card_le_card hsub
      _ ≤ ∑ k : Fin 6, (Pf.filter (fun p : ℕ => (p : ℤ) ∣ v k)).card := Finset.card_biUnion_le
      _ ≤ ∑ k : Fin 6, betaOf P B := Finset.sum_le_sum (fun k _ => hk2 k)
      _ = 6 * betaOf P B := by simp
  have hUcard : betaOf P (11 * B) + 1 ≤ U.card := by
    have hcov : Pf ⊆ D ∪ U := by
      intro p hp
      by_cases hk : ∃ k, (p : ℤ) ∣ v k
      · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hp, hk⟩)
      · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hp, hk⟩)
    have := (Finset.card_le_card hcov).trans (Finset.card_union_le D U)
    omega
  obtain ⟨p0, hp0U⟩ := Finset.card_pos.1 (by omega : 0 < U.card)
  have hUprop : ∀ p ∈ U, p ∈ P ∧ ∀ k, ¬ (p : ℤ) ∣ v k := by
    intro p hp
    obtain ⟨h1, h2⟩ := Finset.mem_filter.mp hp
    exact ⟨hmem p h1, fun k hk => h2 ⟨k, hk⟩⟩
  have hlab : ∀ p ∈ U, HasLabel p v := by
    intro p hp
    obtain ⟨h1, h2⟩ := hUprop p hp
    exact hasLabel_of_clean p (hP.prime p h1) (by have := hP.ge p h1; omega) (hP.clean p h1) v hML h2
  obtain ⟨u0, ub0, s0, ε0, hu0, hε0, hv0⟩ := hlab p0 hp0U
  have hp0P := (hUprop p0 hp0U).1
  have hp0prime := hP.prime p0 hp0P
  set N : ℤ := ε0 j * (((s0 j : ℕ) : ℤ) + 1) * v i - ε0 i * (((s0 i : ℕ) : ℤ) + 1) * v j with hN
  have hdivN : ∀ q ∈ U, (q : ℤ) ∣ N := by
    intro q hq
    by_cases hqp : q = p0
    · subst hqp
      have := dvd_sub (Dvd.dvd.mul_left (hv0 i) (ε0 j * (((s0 j : ℕ) : ℤ) + 1)))
        (Dvd.dvd.mul_left (hv0 j) (ε0 i * (((s0 i : ℕ) : ℤ) + 1)))
      rw [hN]
      convert this using 1
      ring
    · obtain ⟨u1, ub1, s1, ε1, hu1, hε1, hv1⟩ := hlab q hq
      have hqP := (hUprop q hq).1
      have hqprime := hP.prime q hqP
      have hcop : Nat.Coprime p0 q := (Nat.coprime_primes hp0prime hqprime).2 (Ne.symm hqp)
      have h := label_pair_divides p0 q (by have := hP.ge p0 hp0P; omega)
        (by have := hP.ge q hqP; omega) hcop v hML u0 ub0 s0 ε0 hu0 hε0 hv0 u1 ub1 s1 ε1 hu1 hε1 hv1
        (B : ℤ) hBabs i j hij
      have h2 : (q : ℤ) ∣ ((p0 * q : ℕ) : ℤ) := ⟨p0, by push_cast; ring⟩
      exact dvd_trans h2 h
  have hNle : |N| ≤ 11 * (B : ℤ) := N_bound s0 ε0 hε0 v (B : ℤ) hBabs i j hij
  have hN0 : N = 0 := by
    by_contra hne
    have hle := abs_le.1 hNle
    have hmpos : 0 < N.natAbs := by omega
    have hmle : N.natAbs ≤ 11 * B := by omega
    have := card_le_betaOf P hP.sorted U (fun x hx => (hUprop x hx).1)
      (fun x hx => hP.prime x (hUprop x hx).1) N.natAbs (11 * B) hmpos hmle
      (fun p hp => Int.ofNat_dvd_left.mp (hdivN p hp))
    omega
  have hi6 := (s0 i).isLt
  have hj6 := (s0 j).isLt
  have ha : 0 < ((s0 i : ℕ) : ℤ) + 1 := by positivity
  have hb : 0 < ((s0 j : ℕ) : ℤ) + 1 := by positivity
  have hvi := hpos i
  have hvj := hpos j
  refine ⟨((s0 i : ℕ) : ℤ) + 1, ((s0 j : ℕ) : ℤ) + 1, ?_, ?_, ?_, ?_⟩
  · rw [Finset.mem_Icc]; constructor <;> omega
  · rw [Finset.mem_Icc]; constructor <;> omega
  · intro h
    apply hij
    have : ((s0 i : Fin 6) : ℕ) = ((s0 j : Fin 6) : ℕ) := by omega
    exact s0.injective (Fin.ext this)
  · rw [hN] at hN0
    rcases hε0 i with h1 | h1 <;> rcases hε0 j with h2 | h2 <;> rw [h1, h2] at hN0
    · linarith
    · exfalso; nlinarith [mul_pos hb hvi, mul_pos ha hvj]
    · exfalso; nlinarith [mul_pos hb hvi, mul_pos ha hvj]
    · linarith

/-- **Box theorem from pair data.**  `P` strictly increasing list of clean primes `>= 313`;
`|P| >= 6 beta(B) + kappa'` with `kappa' = beta(11 B) + 1` (the least `r` whose `r` smallest primes
have product `> 11 B`). -/
theorem TheoremBoxPair (P : List ℕ) (hP : PairData P) (B : ℕ) (_hB : 1 ≤ B)
    (hcnt : 6 * betaOf P B + betaOf P (11 * B) + 1 ≤ P.length) : TheoremBox B :=
  box_of_pairs B (pairs_of_data P hP B hcnt)

theorem TheoremBox.mono {B B' : ℕ} (h : B' ≤ B) (hB : TheoremBox B) : TheoremBox B' :=
  fun v hinj hpos hle hML => hB v hinj hpos (fun i => (hle i).trans (by exact_mod_cast h)) hML

/-- Theorem A from a box theorem covering the height bound. -/
theorem TheoremA_of_box (B : ℕ) (hB : 17010000 ≤ B + 1) (hbox : TheoremBox B) :
    HeightBound → TheoremA := by
  intro hH v hinj hpos hML
  obtain ⟨g, v', hg, hv, hpos', hinj', hprim'⟩ := gcd_reduce v hinj hpos
  have hML' := ML_reduce g hg v v' hv hML
  have hbd := hH v' hpos' hprim' hML'
  obtain ⟨c, σ, hc, hσ⟩ := hbox v' hinj' hpos' (fun i => by have := hbd i; omega) hML'
  exact ⟨g * c, σ, mul_pos hg hc, fun i => by rw [hv i, hσ i]; ring⟩

end Sext6
end LRSpectrumFull

#print axioms LRSpectrumFull.Sext6.prefix_prod_le
#print axioms LRSpectrumFull.Sext6.card_le_betaOf
#print axioms LRSpectrumFull.Sext6.pairs_of_data
#print axioms LRSpectrumFull.Sext6.TheoremBoxPair
#print axioms LRSpectrumFull.Sext6.TheoremA_of_box
