/-
# L2 (piece 4): pair counting.  PROVED from `ResidueData` (no HeightBound needed beyond `v_i < 17,010,000`).

Central idea: each clean prime p not dividing any speed forces v_i ≡ ± u s(i) (s a permutation of 1..6),
hence p | s(j) v_i ∓ s(i) v_j; after cancelling gcd(s i, s j) this puts p among the prime divisors of
one of 44 integers (22 coprime pairs a ≠ b, two signs).  If the ratio v_i/v_j is not a/b, all 44 are
nonzero of size < 2.1e8 < 313^4, so each has at most 3 prime factors among primes ≥ 313; the speeds
themselves absorb at most 2 each (313^3 > 1.7e7).  12 + 44*3 = 144 < 150 primes: contradiction.
-/
import LRSpectrumFull.Sext6.L1prime
import Mathlib.Algebra.BigOperators.Associated
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.LinearCombination
import Mathlib.Data.Finset.Max
import Mathlib.Data.Nat.Prime.Int
import Mathlib.Algebra.Order.BigOperators.Group.Finset

namespace LRSpectrumFull
namespace Sext6

/-- two nonzero residue classes `x, y ∈ 1..6` that are `±`-related mod a prime `p > 12` coincide. -/
theorem sign_rigid (p : ℕ) (hpz : Prime (p : ℤ)) (hp12 : 12 < p) (u a x y : ℤ)
    (hu : ¬ (p : ℤ) ∣ u) (hx1 : 1 ≤ x) (hx6 : x ≤ 6) (hy1 : 1 ≤ y) (hy6 : y ≤ 6)
    (h1 : (p : ℤ) ∣ a - u * x ∨ (p : ℤ) ∣ a + u * x)
    (h2 : (p : ℤ) ∣ a - u * y ∨ (p : ℤ) ∣ a + u * y) : x = y := by
  have hp' : (12 : ℤ) < p := by exact_mod_cast hp12
  have key : ∀ z : ℤ, (p : ℤ) ∣ u * z → |z| < p → z = 0 := by
    intro z hz hzp
    rcases hpz.dvd_or_dvd hz with h | h
    · exact absurd h hu
    · exact Int.eq_zero_of_abs_lt_dvd h hzp
  rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2
  · have := key (y - x) (by
      have := dvd_sub h1 h2
      have e : a - u * x - (a - u * y) = u * (y - x) := by ring
      rwa [e] at this) (by rw [abs_lt]; constructor <;> omega)
    omega
  · have := key (x + y) (by
      have := dvd_sub h2 h1
      have e : a + u * y - (a - u * x) = u * (x + y) := by ring
      rwa [e] at this) (by rw [abs_lt]; constructor <;> omega)
    omega
  · have := key (x + y) (by
      have := dvd_sub h1 h2
      have e : a + u * x - (a - u * y) = u * (x + y) := by ring
      rwa [e] at this) (by rw [abs_lt]; constructor <;> omega)
    omega
  · have := key (x - y) (by
      have := dvd_sub h1 h2
      have e : a + u * x - (a + u * y) = u * (x - y) := by ring
      rwa [e] at this) (by rw [abs_lt]; constructor <;> omega)
    omega

/-- **L1' in bijection form.** A clean prime `p > 12` not dividing any speed gives a unit `u` and an
injective `s : Fin 6 → {1..6}` with `v_i ≡ ± u · s(i) (mod p)`. -/
theorem L1bij (p : ℕ) (hp : p.Prime) (hp12 : 12 < p) (hclean : CleanPrime p) (v : Fin 6 → ℤ)
    (hML : ML v ≤ 1 / 7) (hnd : ∀ i, ¬ (p : ℤ) ∣ v i) :
    ∃ u : ℤ, ¬ (p : ℤ) ∣ u ∧ ∃ s : Fin 6 → ℤ, (∀ i, s i ∈ Finset.Icc (1 : ℤ) 6) ∧
      Function.Injective s ∧ ∀ i, (p : ℤ) ∣ v i - u * s i ∨ (p : ℤ) ∣ v i + u * s i := by
  obtain ⟨u, hu, h⟩ := L1prime p hp.pos hclean v hML hnd
  have hpz : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp
  have h' : ∀ k : Fin 6, ∃ j : Fin 6, (p : ℤ) ∣ v j - u * (((k : ℕ) : ℤ) + 1) ∨
      (p : ℤ) ∣ v j + u * (((k : ℕ) : ℤ) + 1) := by
    intro k
    apply h
    have := k.isLt
    rw [Finset.mem_Icc]; omega
  choose j hj using h'
  have hji : Function.Injective j := by
    intro k k' hkk
    have hk := hj k
    have hk' := hj k'
    rw [← hkk] at hk'
    have := sign_rigid p hpz hp12 u (v (j k)) (((k : ℕ) : ℤ) + 1) (((k' : ℕ) : ℤ) + 1) hu
      (by omega) (by have := k.isLt; omega) (by omega) (by have := k'.isLt; omega) hk hk'
    exact Fin.ext (by omega)
  have hsurj : Function.Surjective j := Finite.injective_iff_surjective.mp hji
  refine ⟨u, hu, fun i => (((Function.surjInv hsurj i : Fin 6) : ℕ) : ℤ) + 1, ?_, ?_, ?_⟩
  · intro i
    have := (Function.surjInv hsurj i).isLt
    rw [Finset.mem_Icc]; beta_reduce; omega
  · intro i i' h
    have h1 : Function.surjInv hsurj i = Function.surjInv hsurj i' := Fin.ext (by simpa using h)
    rw [← Function.surjInv_eq hsurj i, ← Function.surjInv_eq hsurj i', h1]
  · intro i
    have hk := hj (Function.surjInv hsurj i)
    rw [Function.surjInv_eq hsurj i] at hk
    exact hk

/-- At most `k` primes `≥ 313` divide a number `0 < m ≤ X < 313^(k+1)`. -/
theorem card_dvd_le (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime ∧ 313 ≤ p) (m X k : ℕ) (hm : 0 < m)
    (hmX : m ≤ X) (hX : X < 313 ^ (k + 1)) (hd : ∀ p ∈ S, p ∣ m) : S.card ≤ k := by
  by_contra hcon
  have hcon' : k + 1 ≤ S.card := by omega
  have h1 : 313 ^ S.card ≤ ∏ p ∈ S, p :=
    Finset.pow_card_le_prod S (fun p => p) 313 (fun p hp => (hS p hp).2)
  have h2 : ∏ p ∈ S, p ∣ m := Finset.prod_primes_dvd m (fun p hp => (hS p hp).1.prime) hd
  have h3 : ∏ p ∈ S, p ≤ m := Nat.le_of_dvd hm h2
  have h4 : 313 ^ (k + 1) ≤ 313 ^ S.card := Nat.pow_le_pow_right (by norm_num) hcon'
  exact absurd (lt_of_le_of_lt (h4.trans (h1.trans (h3.trans hmX))) hX) (lt_irrefl _)

/-- The 22 coprime pairs `a ≠ b` in `{1..6}`. -/
def F' : Finset (ℤ × ℤ) :=
  (Finset.Icc (1 : ℤ) 6 ×ˢ Finset.Icc (1 : ℤ) 6).filter (fun ab => ab.1 ≠ ab.2 ∧ Int.gcd ab.1 ab.2 = 1)

theorem F'_card : F'.card = 22 := by decide +kernel

theorem red : ∀ x ∈ Finset.Icc (1 : ℤ) 6, ∀ y ∈ Finset.Icc (1 : ℤ) 6, x ≠ y →
    ∃ g ∈ Finset.Icc (1 : ℤ) 6, ∃ ab ∈ F', x = g * ab.1 ∧ y = g * ab.2 := by
  decide +kernel

/-- The index set of the 44 integers: coprime pair times a sign. -/
def Tset : Finset ((ℤ × ℤ) × ℤ) := F' ×ˢ ({1, -1} : Finset ℤ)

theorem Tset_card : Tset.card = 44 := by
  rw [Tset, Finset.card_product, F'_card]; rfl

/-- The integer `b v_i - ε a v_j` attached to `t = ((a,b),ε)`. -/
def Nval (v : Fin 6 → ℤ) (i j : Fin 6) (t : (ℤ × ℤ) × ℤ) : ℤ :=
  t.1.2 * v i - t.2 * (t.1.1 * v j)

/-- Every clean prime `p ≥ 313` not dividing any speed divides one of the 44 integers. -/
theorem cover (p : ℕ) (hp : p.Prime) (h313 : 313 ≤ p) (hclean : CleanPrime p) (v : Fin 6 → ℤ)
    (hML : ML v ≤ 1 / 7) (hnd : ∀ i, ¬ (p : ℤ) ∣ v i) (i j : Fin 6) (hij : i ≠ j) :
    ∃ t ∈ Tset, (p : ℤ) ∣ Nval v i j t := by
  have hpz : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp
  obtain ⟨u, hu, s, hs, hsinj, hdv⟩ := L1bij p hp (by omega) hclean v hML hnd
  have hsij : s i ≠ s j := fun e => hij (hsinj e)
  obtain ⟨g, hg, ab, hab, hx, hy⟩ := red (s i) (hs i) (s j) (hs j) hsij
  have hε : ∃ ε : ℤ, (ε = 1 ∨ ε = -1) ∧ (p : ℤ) ∣ s j * v i - ε * (s i * v j) := by
    rcases hdv i with h1 | h1 <;> rcases hdv j with h2 | h2 <;>
      obtain ⟨k1, hk1⟩ := h1 <;> obtain ⟨k2, hk2⟩ := h2
    · exact ⟨1, Or.inl rfl, ⟨s j * k1 - s i * k2, by linear_combination (s j) * hk1 - (s i) * hk2⟩⟩
    · exact ⟨-1, Or.inr rfl, ⟨s j * k1 + s i * k2, by linear_combination (s j) * hk1 + (s i) * hk2⟩⟩
    · exact ⟨-1, Or.inr rfl, ⟨s j * k1 + s i * k2, by linear_combination (s j) * hk1 + (s i) * hk2⟩⟩
    · exact ⟨1, Or.inl rfl, ⟨s j * k1 - s i * k2, by linear_combination (s j) * hk1 - (s i) * hk2⟩⟩
  obtain ⟨ε, hε1, hdiv⟩ := hε
  refine ⟨(ab, ε), ?_, ?_⟩
  · rw [Tset, Finset.mem_product]
    refine ⟨hab, ?_⟩
    simpa using hε1
  · have hg' := Finset.mem_Icc.mp hg
    have e : s j * v i - ε * (s i * v j) = g * Nval v i j (ab, ε) := by
      rw [hx, hy, Nval]; ring
    rw [e] at hdiv
    rcases hpz.dvd_or_dvd hdiv with h | h
    · exfalso
      have := Int.le_of_dvd (by omega) h
      have : (313 : ℤ) ≤ p := by exact_mod_cast h313
      omega
    · exact h

/-- **L2.** -/
theorem L2 (hres : ResidueData) (v : Fin 6 → ℤ) (hpos : ∀ i, 0 < v i)
    (hH : ∀ i, v i < 17010000) (hML : ML v ≤ 1 / 7) :
    ∀ i j, i ≠ j → ∃ a b : ℤ, a ∈ Finset.Icc (1 : ℤ) 6 ∧ b ∈ Finset.Icc (1 : ℤ) 6 ∧
      a ≠ b ∧ b * v i = a * v j := by
  intro i j hij
  by_contra hcon
  have hcon' : ∀ a ∈ Finset.Icc (1 : ℤ) 6, ∀ b ∈ Finset.Icc (1 : ℤ) 6, a ≠ b →
      b * v i ≠ a * v j := by
    intro a ha b hb hab h
    exact hcon ⟨a, b, ha, hb, hab, h⟩
  obtain ⟨hlen, hPcl⟩ := hres
  have hnodup : cleanPrimes150.Nodup := by decide +kernel
  have hge : ∀ p ∈ cleanPrimes150, 313 ≤ p := by decide +kernel
  have hPcard : cleanPrimes150.toFinset.card = 150 := by
    rw [List.toFinset_card_of_nodup hnodup, hlen]
  have hPprop : ∀ p ∈ cleanPrimes150.toFinset, p.Prime ∧ 313 ≤ p ∧ CleanPrime p := by
    intro p hp
    rw [List.mem_toFinset] at hp
    exact ⟨(hPcl p hp).1, hge p hp, (hPcl p hp).2⟩
  set P := cleanPrimes150.toFinset with hP
  -- primes dividing a speed
  have hB : (P.filter (fun p : ℕ => ∃ k, (p : ℤ) ∣ v k)).card ≤ 12 := by
    have hsub : P.filter (fun p : ℕ => ∃ k, (p : ℤ) ∣ v k) ⊆
        Finset.univ.biUnion (fun k : Fin 6 => P.filter (fun p : ℕ => (p : ℤ) ∣ v k)) := by
      intro p hp
      obtain ⟨hpP, k, hk⟩ := Finset.mem_filter.mp hp
      exact Finset.mem_biUnion.mpr ⟨k, Finset.mem_univ _, Finset.mem_filter.mpr ⟨hpP, hk⟩⟩
    have hk2 : ∀ k : Fin 6, (P.filter (fun p : ℕ => (p : ℤ) ∣ v k)).card ≤ 2 := by
      intro k
      have h1 := hpos k
      have h2 := hH k
      refine card_dvd_le _ (fun p hp => ⟨(hPprop p (Finset.mem_filter.mp hp).1).1,
        (hPprop p (Finset.mem_filter.mp hp).1).2.1⟩) (v k).natAbs 17010000 2 (by omega)
        (by omega) (by norm_num) (fun p hp => Int.ofNat_dvd_left.mp (Finset.mem_filter.mp hp).2)
    calc (P.filter (fun p : ℕ => ∃ k, (p : ℤ) ∣ v k)).card
        ≤ (Finset.univ.biUnion (fun k : Fin 6 => P.filter (fun p : ℕ => (p : ℤ) ∣ v k))).card :=
          Finset.card_le_card hsub
      _ ≤ ∑ k : Fin 6, (P.filter (fun p : ℕ => (p : ℤ) ∣ v k)).card := Finset.card_biUnion_le
      _ ≤ ∑ k : Fin 6, 2 := Finset.sum_le_sum (fun k _ => hk2 k)
      _ = 12 := by simp
  -- primes dividing one of the 44 integers
  have hD : ∀ t ∈ Tset, (P.filter (fun p : ℕ => (p : ℤ) ∣ Nval v i j t)).card ≤ 3 := by
    intro t ht
    obtain ⟨hab, hε⟩ := Finset.mem_product.mp ht
    simp only [F', Finset.mem_filter, Finset.mem_product, Finset.mem_Icc] at hab
    obtain ⟨⟨⟨ha1, ha6⟩, hb1, hb6⟩, hne, _⟩ := hab
    have hvi := hpos i
    have hvj := hpos j
    have hvi' := hH i
    have hvj' := hH j
    have hbv : t.1.2 * v i ≤ 6 * v i := mul_le_mul_of_nonneg_right hb6 hvi.le
    have hav : t.1.1 * v j ≤ 6 * v j := mul_le_mul_of_nonneg_right ha6 hvj.le
    have hbv0 : 0 < t.1.2 * v i := mul_pos (by omega) hvi
    have hav0 : 0 < t.1.1 * v j := mul_pos (by omega) hvj
    have hne0 : Nval v i j t ≠ 0 ∧ (Nval v i j t).natAbs ≤ 204120000 := by
      rcases Finset.mem_insert.mp hε with h | h
      · have h1 : t.2 = 1 := h
        have hneq := hcon' t.1.1 (Finset.mem_Icc.mpr ⟨ha1, ha6⟩) t.1.2
          (Finset.mem_Icc.mpr ⟨hb1, hb6⟩) hne
        unfold Nval
        rw [h1]
        constructor
        · intro h0; apply hneq; linarith
        · omega
      · have h1 : t.2 = -1 := by simpa using h
        unfold Nval
        rw [h1]
        constructor
        · omega
        · omega
    refine card_dvd_le _ (fun p hp => ⟨(hPprop p (Finset.mem_filter.mp hp).1).1,
      (hPprop p (Finset.mem_filter.mp hp).1).2.1⟩) (Nval v i j t).natAbs 204120000 3
      (by omega) hne0.2 (by norm_num) (fun p hp => Int.ofNat_dvd_left.mp (Finset.mem_filter.mp hp).2)
  -- cover
  have hcov : P ⊆ P.filter (fun p : ℕ => ∃ k, (p : ℤ) ∣ v k) ∪
      Tset.biUnion (fun t => P.filter (fun p : ℕ => (p : ℤ) ∣ Nval v i j t)) := by
    intro p hp
    by_cases hk : ∃ k, (p : ℤ) ∣ v k
    · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hp, hk⟩)
    · apply Finset.mem_union_right
      push Not at hk
      obtain ⟨hpp, hp313, hcl⟩ := hPprop p hp
      obtain ⟨t, ht, hdt⟩ := cover p hpp hp313 hcl v hML hk i j hij
      exact Finset.mem_biUnion.mpr ⟨t, ht, Finset.mem_filter.mpr ⟨hp, hdt⟩⟩
  have hfin : P.card ≤ 144 := by
    calc P.card ≤ (P.filter (fun p : ℕ => ∃ k, (p : ℤ) ∣ v k) ∪
          Tset.biUnion (fun t => P.filter (fun p : ℕ => (p : ℤ) ∣ Nval v i j t))).card :=
          Finset.card_le_card hcov
      _ ≤ (P.filter (fun p : ℕ => ∃ k, (p : ℤ) ∣ v k)).card +
          (Tset.biUnion (fun t => P.filter (fun p : ℕ => (p : ℤ) ∣ Nval v i j t))).card :=
          Finset.card_union_le _ _
      _ ≤ 12 + ∑ t ∈ Tset, (P.filter (fun p : ℕ => (p : ℤ) ∣ Nval v i j t)).card :=
          Nat.add_le_add hB Finset.card_biUnion_le
      _ ≤ 12 + ∑ t ∈ Tset, 3 := Nat.add_le_add_left (Finset.sum_le_sum hD) _
      _ = 144 := by rw [Finset.sum_const, Tset_card]; simp
  omega

end Sext6
end LRSpectrumFull

#print axioms LRSpectrumFull.Sext6.L2
