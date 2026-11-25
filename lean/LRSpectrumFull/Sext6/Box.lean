/-
# BOX THEOREM: no HeightBound.

`TheoremBox B`: six distinct positive integers, all `≤ B`, with `ML ≤ 1/7`, are `c·(1,…,6)` up to order.
Hypotheses: only `ResidueData` (150 primes) or `ResidueData111` (111 primes).

Central idea: the L2 counting argument needs only that every speed (and every pair integer
`b v_i ∓ a v_j`, of size `≤ 11 B` since `a ≠ b ≤ 6`) has few prime factors among the clean primes;
those counts come from the sizes of the products of the smallest clean primes, not from a height bound.
Parametric lemma `box_pairs`; the two instances only supply the arithmetic:
* 150 primes, `B = 41,912,890 = 313·359·373 - 1`: beta = 2, kappa = 3, `6·2 + 44·3 = 144 < 150`;
* 111 primes, `B = 17,581,557` (`11 B < 571·577·587 = 193,397,129`): beta = 2, kappa = 2, `12 + 88 = 100 < 111`.
-/
import LRSpectrumFull.Sext6.Prime111
import LRSpectrumFull.Sext6.L2
import LRSpectrumFull.Sext6.L3
import LRSpectrumFull.Sext6.L4
import LRSpectrumFull.Sext6.Dilation
import Mathlib.Algebra.GCDMonoid.Finset
import Mathlib.Algebra.GCDMonoid.Nat
import Mathlib.Data.Finset.Sort

namespace LRSpectrumFull
namespace Sext6

/-! ### prime-factor counting lemmas -/

/-- At most `k` primes `≥ q0` divide a number `0 < m ≤ X < q0^(k+1)`. -/
theorem card_dvd_le' (q0 : ℕ) (hq0 : 0 < q0) (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime ∧ q0 ≤ p)
    (m X k : ℕ) (hm : 0 < m) (hmX : m ≤ X) (hX : X < q0 ^ (k + 1)) (hd : ∀ p ∈ S, p ∣ m) :
    S.card ≤ k := by
  by_contra hcon
  have hcon' : k + 1 ≤ S.card := by omega
  have h1 : q0 ^ S.card ≤ ∏ p ∈ S, p :=
    Finset.pow_card_le_prod S (fun p => p) q0 (fun p hp => (hS p hp).2)
  have h2 : ∏ p ∈ S, p ∣ m := Finset.prod_primes_dvd m (fun p hp => (hS p hp).1.prime) hd
  have h3 : ∏ p ∈ S, p ≤ m := Nat.le_of_dvd hm h2
  have h4 : q0 ^ (k + 1) ≤ q0 ^ S.card := Nat.pow_le_pow_right hq0 hcon'
  exact absurd (lt_of_le_of_lt (h4.trans (h1.trans (h3.trans hmX))) hX) (lt_irrefl _)

/-- Three distinct primes dividing `m` have product dividing `m`; if every ordered triple from the set
has product `≥ N`, then at most two primes of the set divide any `0 < m < N`. -/
theorem card_dvd_le_two (S : Finset ℕ) (N : ℕ) (hS : ∀ p ∈ S, p.Prime)
    (htrip : ∀ x ∈ S, ∀ y ∈ S, ∀ z ∈ S, x < y → y < z → N ≤ x * y * z)
    (m : ℕ) (hm : 0 < m) (hmN : m < N) (hd : ∀ p ∈ S, p ∣ m) : S.card ≤ 2 := by
  by_contra hcon
  have hc : 3 ≤ S.card := by omega
  let e := S.orderEmbOfFin rfl
  have hx : e ⟨0, by omega⟩ ∈ S := Finset.orderEmbOfFin_mem S rfl _
  have hy : e ⟨1, by omega⟩ ∈ S := Finset.orderEmbOfFin_mem S rfl _
  have hz : e ⟨2, by omega⟩ ∈ S := Finset.orderEmbOfFin_mem S rfl _
  have hxy : e ⟨0, by omega⟩ < e ⟨1, by omega⟩ := e.strictMono (by simp [Fin.lt_def])
  have hyz : e ⟨1, by omega⟩ < e ⟨2, by omega⟩ := e.strictMono (by simp [Fin.lt_def])
  generalize e ⟨0, by omega⟩ = x at *
  generalize e ⟨1, by omega⟩ = y at *
  generalize e ⟨2, by omega⟩ = z at *
  have px := hS x hx
  have py := hS y hy
  have pz := hS z hz
  have cxy : Nat.Coprime x y := (Nat.coprime_primes px py).mpr (by omega)
  have cxz : Nat.Coprime x z := (Nat.coprime_primes px pz).mpr (by omega)
  have cyz : Nat.Coprime y z := (Nat.coprime_primes py pz).mpr (by omega)
  have h1 : x * y ∣ m := Nat.Coprime.mul_dvd_of_dvd_of_dvd cxy (hd x hx) (hd y hy)
  have h2 : x * y * z ∣ m :=
    Nat.Coprime.mul_dvd_of_dvd_of_dvd (Nat.coprime_mul_iff_left.mpr ⟨cxz, cyz⟩) h1 (hd z hz)
  have h3 := Nat.le_of_dvd hm h2
  have h4 := htrip x hx y hy z hz hxy hyz
  omega

/-- staged lower bounds give the triple bound. -/
theorem triple_of_stages (P : Finset ℕ) (a1 a2 a3 : ℕ) (h1 : ∀ x ∈ P, a1 ≤ x)
    (h2 : ∀ y ∈ P, a1 < y → a2 ≤ y) (h3 : ∀ z ∈ P, a2 < z → a3 ≤ z) :
    ∀ x ∈ P, ∀ y ∈ P, ∀ z ∈ P, x < y → y < z → a1 * a2 * a3 ≤ x * y * z := by
  intro x hx y hy z hz hxy hyz
  have hx' := h1 x hx
  have hy' := h2 y hy (by omega)
  have hz' := h3 z hz (by omega)
  exact Nat.mul_le_mul (Nat.mul_le_mul hx' hy') hz'

/-! ### the parametric pair lemma -/

theorem cover' (q0 : ℕ) (hq : 13 ≤ q0) (p : ℕ) (hp : p.Prime) (hpq : q0 ≤ p) (hclean : CleanPrime p)
    (v : Fin 6 → ℤ) (hML : ML v ≤ 1 / 7) (hnd : ∀ i, ¬ (p : ℤ) ∣ v i) (i j : Fin 6) (hij : i ≠ j) :
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
      have : (13 : ℤ) ≤ p := by exact_mod_cast (hq.trans hpq)
      omega
    · exact h

/-- **Parametric L2 in a box.**  `P` a finite set of clean primes `≥ q0 ≥ 13`; prime-factor counts
`β` (for numbers `≤ B`) and `κ` (for numbers `≤ 11 B`); `6β + 44κ < |P|`. -/
theorem box_pairs (P : Finset ℕ) (q0 B β κ : ℕ) (hq : 13 ≤ q0)
    (hP : ∀ p ∈ P, p.Prime ∧ q0 ≤ p ∧ CleanPrime p)
    (hβ : ∀ S ⊆ P, ∀ m : ℕ, 0 < m → m ≤ B → (∀ p ∈ S, p ∣ m) → S.card ≤ β)
    (hκ : ∀ S ⊆ P, ∀ m : ℕ, 0 < m → m ≤ 11 * B → (∀ p ∈ S, p ∣ m) → S.card ≤ κ)
    (hcnt : 6 * β + 44 * κ < P.card)
    (v : Fin 6 → ℤ) (hpos : ∀ i, 0 < v i) (hB : ∀ i, v i ≤ B) (hML : ML v ≤ 1 / 7) :
    ∀ i j, i ≠ j → ∃ a b : ℤ, a ∈ Finset.Icc (1 : ℤ) 6 ∧ b ∈ Finset.Icc (1 : ℤ) 6 ∧
      a ≠ b ∧ b * v i = a * v j := by
  intro i j hij
  by_contra hcon
  have hcon' : ∀ a ∈ Finset.Icc (1 : ℤ) 6, ∀ b ∈ Finset.Icc (1 : ℤ) 6, a ≠ b →
      b * v i ≠ a * v j := by
    intro a ha b hb hab h
    exact hcon ⟨a, b, ha, hb, hab, h⟩
  -- primes dividing a speed
  have hBs : (P.filter (fun p : ℕ => ∃ k, (p : ℤ) ∣ v k)).card ≤ 6 * β := by
    have hsub : P.filter (fun p : ℕ => ∃ k, (p : ℤ) ∣ v k) ⊆
        Finset.univ.biUnion (fun k : Fin 6 => P.filter (fun p : ℕ => (p : ℤ) ∣ v k)) := by
      intro p hp
      obtain ⟨hpP, k, hk⟩ := Finset.mem_filter.mp hp
      exact Finset.mem_biUnion.mpr ⟨k, Finset.mem_univ _, Finset.mem_filter.mpr ⟨hpP, hk⟩⟩
    have hk2 : ∀ k : Fin 6, (P.filter (fun p : ℕ => (p : ℤ) ∣ v k)).card ≤ β := by
      intro k
      have h1 := hpos k
      have h2 := hB k
      exact hβ _ (Finset.filter_subset _ _) (v k).natAbs (by omega) (by omega)
        (fun p hp => Int.ofNat_dvd_left.mp (Finset.mem_filter.mp hp).2)
    calc (P.filter (fun p : ℕ => ∃ k, (p : ℤ) ∣ v k)).card
        ≤ (Finset.univ.biUnion (fun k : Fin 6 => P.filter (fun p : ℕ => (p : ℤ) ∣ v k))).card :=
          Finset.card_le_card hsub
      _ ≤ ∑ k : Fin 6, (P.filter (fun p : ℕ => (p : ℤ) ∣ v k)).card := Finset.card_biUnion_le
      _ ≤ ∑ k : Fin 6, β := Finset.sum_le_sum (fun k _ => hk2 k)
      _ = 6 * β := by simp
  -- primes dividing one of the 44 integers
  have hD : ∀ t ∈ Tset, (P.filter (fun p : ℕ => (p : ℤ) ∣ Nval v i j t)).card ≤ κ := by
    intro t ht
    obtain ⟨hab, hε⟩ := Finset.mem_product.mp ht
    simp only [F', Finset.mem_filter, Finset.mem_product, Finset.mem_Icc] at hab
    obtain ⟨⟨⟨ha1, ha6⟩, hb1, hb6⟩, hne, _⟩ := hab
    have hvi := hpos i
    have hvj := hpos j
    have hvi' := hB i
    have hvj' := hB j
    have hBnn : (0 : ℤ) ≤ (B : ℤ) := by positivity
    have hbv : t.1.2 * v i ≤ t.1.2 * (B : ℤ) := mul_le_mul_of_nonneg_left hvi' (by omega)
    have hav : t.1.1 * v j ≤ t.1.1 * (B : ℤ) := mul_le_mul_of_nonneg_left hvj' (by omega)
    have hsum : (t.1.1 + t.1.2) * (B : ℤ) ≤ 11 * (B : ℤ) :=
      mul_le_mul_of_nonneg_right (by omega) hBnn
    have hbv0 : 0 < t.1.2 * v i := mul_pos (by omega) hvi
    have hav0 : 0 < t.1.1 * v j := mul_pos (by omega) hvj
    have hb6' : t.1.2 * (B : ℤ) ≤ 6 * (B : ℤ) := mul_le_mul_of_nonneg_right hb6 hBnn
    have ha6' : t.1.1 * (B : ℤ) ≤ 6 * (B : ℤ) := mul_le_mul_of_nonneg_right ha6 hBnn
    have hexp : (t.1.1 + t.1.2) * (B : ℤ) = t.1.1 * (B : ℤ) + t.1.2 * (B : ℤ) := by ring
    have hne0 : Nval v i j t ≠ 0 ∧ (Nval v i j t).natAbs ≤ 11 * B := by
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
    exact hκ _ (Finset.filter_subset _ _) (Nval v i j t).natAbs (by omega) hne0.2
      (fun p hp => Int.ofNat_dvd_left.mp (Finset.mem_filter.mp hp).2)
  -- cover
  have hcov : P ⊆ P.filter (fun p : ℕ => ∃ k, (p : ℤ) ∣ v k) ∪
      Tset.biUnion (fun t => P.filter (fun p : ℕ => (p : ℤ) ∣ Nval v i j t)) := by
    intro p hp
    by_cases hk : ∃ k, (p : ℤ) ∣ v k
    · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hp, hk⟩)
    · apply Finset.mem_union_right
      push Not at hk
      obtain ⟨hpp, hpq, hcl⟩ := hP p hp
      obtain ⟨t, ht, hdt⟩ := cover' q0 hq p hpp hpq hcl v hML hk i j hij
      exact Finset.mem_biUnion.mpr ⟨t, ht, Finset.mem_filter.mpr ⟨hp, hdt⟩⟩
  have hfin : P.card ≤ 6 * β + 44 * κ := by
    calc P.card ≤ (P.filter (fun p : ℕ => ∃ k, (p : ℤ) ∣ v k) ∪
          Tset.biUnion (fun t => P.filter (fun p : ℕ => (p : ℤ) ∣ Nval v i j t))).card :=
          Finset.card_le_card hcov
      _ ≤ (P.filter (fun p : ℕ => ∃ k, (p : ℤ) ∣ v k)).card +
          (Tset.biUnion (fun t => P.filter (fun p : ℕ => (p : ℤ) ∣ Nval v i j t))).card :=
          Finset.card_union_le _ _
      _ ≤ 6 * β + ∑ t ∈ Tset, (P.filter (fun p : ℕ => (p : ℤ) ∣ Nval v i j t)).card :=
          Nat.add_le_add hBs Finset.card_biUnion_le
      _ ≤ 6 * β + ∑ t ∈ Tset, κ := Nat.add_le_add_left (Finset.sum_le_sum hD) _
      _ = 6 * β + 44 * κ := by rw [Finset.sum_const, Tset_card]; simp
  omega

/-! ### gcd reduction and the primitive classification -/

theorem gcd_reduce (v : Fin 6 → ℤ) (hinj : Function.Injective v) (hpos : ∀ i, 0 < v i) :
    ∃ (g : ℤ) (v' : Fin 6 → ℤ), 0 < g ∧ (∀ i, v i = g * v' i) ∧ (∀ i, 0 < v' i) ∧
      Function.Injective v' ∧ Primitive v' := by
  set g : ℕ := Finset.univ.gcd (fun i => (v i).natAbs) with hg
  have hgdvd : ∀ i, (g : ℤ) ∣ v i := by
    intro i
    apply Int.ofNat_dvd_left.mpr
    exact Finset.gcd_dvd (Finset.mem_univ i)
  have hgpos : 0 < g := by
    rcases Nat.eq_zero_or_pos g with h0 | h0
    · exfalso
      have := hgdvd 0
      rw [h0] at this
      have := zero_dvd_iff.mp (by simpa using this)
      have := hpos 0
      omega
    · exact h0
  have hgz : (0 : ℤ) < g := by exact_mod_cast hgpos
  choose v' hv' using hgdvd
  have hpos' : ∀ i, 0 < v' i := by
    intro i
    by_contra h
    push Not at h
    have h1 : (g : ℤ) * v' i ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hgz.le h
    have := hpos i
    rw [hv' i] at this
    linarith
  have hinj' : Function.Injective v' := by
    intro i j h
    apply hinj
    rw [hv' i, hv' j, h]
  have hprim' : Primitive v' := by
    intro d hd
    have hd0 : d ≠ 0 := by
      rintro rfl
      have := hd 0
      have := zero_dvd_iff.mp (by simpa using this)
      have := hpos' 0
      omega
    have hdg : d * g ∣ g := by
      have : ∀ i ∈ Finset.univ, d * g ∣ (fun i => (v i).natAbs) i := by
        intro i _
        obtain ⟨c, hc⟩ := hd i
        apply Int.ofNat_dvd_left.mp
        refine ⟨c, ?_⟩
        push_cast
        rw [hv' i, hc]; ring
      exact Finset.dvd_gcd this
    have := Nat.le_of_dvd hgpos hdg
    have h1 : 1 ≤ d := Nat.pos_of_ne_zero hd0
    nlinarith
  exact ⟨g, v', hgz, hv', hpos', hinj', hprim'⟩

theorem classify_primitive (v : Fin 6 → ℤ) (hinj : Function.Injective v) (hpos : ∀ i, 0 < v i)
    (hprim : Primitive v) (hML : ML v ≤ 1 / 7)
    (hpair : ∀ i j, i ≠ j → ∃ a b : ℤ, a ∈ Finset.Icc (1 : ℤ) 6 ∧ b ∈ Finset.Icc (1 : ℤ) 6 ∧
      a ≠ b ∧ b * v i = a * v j) :
    ∃ σ : Equiv.Perm (Fin 6), ∀ i, v i = (σ i : ℕ) + 1 := by
  rcases L3 v hinj hpos hprim hpair with ⟨σ, hσ⟩ | ⟨σ, hσ⟩
  · exact ⟨σ, hσ⟩
  · exact absurd hML (L4 v (fun i => ⟨σ i, hσ i⟩))

/-- If `ML(g v') ≤ 1/7`, then `ML v' ≤ 1/7`. -/
theorem ML_reduce (g : ℤ) (hg : 0 < g) (v v' : Fin 6 → ℤ) (hv : ∀ i, v i = g * v' i)
    (hML : ML v ≤ 1 / 7) : ML v' ≤ 1 / 7 := by
  have hvg : (fun i => g * v' i) = v := funext (fun i => (hv i).symm)
  rw [← ML_smul g hg.ne' v', hvg]
  exact hML

/-- a primitive part is at most the vector. -/
theorem prim_le (g : ℤ) (hg : 0 < g) (v v' : Fin 6 → ℤ) (hv : ∀ i, v i = g * v' i)
    (hpos' : ∀ i, 0 < v' i) (i : Fin 6) : v' i ≤ v i := by
  have := hv i
  have := hpos' i
  nlinarith

/-! ### the statement and the instances -/

/-- **Box theorem (statement).** Six distinct positive integers, all `≤ B`, with `ML ≤ 1/7`
are `c·(1,…,6)` up to order. -/
def TheoremBox (B : ℕ) : Prop :=
  ∀ v : Fin 6 → ℤ, Function.Injective v → (∀ i, 0 < v i) → (∀ i, v i ≤ B) → ML v ≤ 1 / 7 →
    ∃ (c : ℤ) (σ : Equiv.Perm (Fin 6)), 0 < c ∧ ∀ i, v i = c * ((σ i : ℕ) + 1)

/-- the pair conclusion of L2, in a box. -/
def PairsIn (B : ℕ) : Prop :=
  ∀ v : Fin 6 → ℤ, (∀ i, 0 < v i) → (∀ i, v i ≤ B) → ML v ≤ 1 / 7 →
    ∀ i j, i ≠ j → ∃ a b : ℤ, a ∈ Finset.Icc (1 : ℤ) 6 ∧ b ∈ Finset.Icc (1 : ℤ) 6 ∧
      a ≠ b ∧ b * v i = a * v j

/-- generic box theorem from the pair lemma. -/
theorem box_of_pairs (B : ℕ) (hpairs : PairsIn B) : TheoremBox B := by
  intro v hinj hpos hB hML
  obtain ⟨g, v', hg, hv, hpos', hinj', hprim'⟩ := gcd_reduce v hinj hpos
  have hML' := ML_reduce g hg v v' hv hML
  have hB' : ∀ i, v' i ≤ B := fun i => (prim_le g hg v v' hv hpos' i).trans (hB i)
  obtain ⟨σ, hσ⟩ := classify_primitive v' hinj' hpos' hprim' hML'
    (hpairs v' hpos' hB' hML')
  exact ⟨g, σ, hg, fun i => by rw [hv i, hσ i]⟩

/-! #### 150 primes, B = 41,912,890 -/

theorem arith150 : 313 * 359 * 373 = 41912891 ∧ 41912890 < 41912891 ∧
    11 * 41912890 < 313 ^ (3 + 1) ∧ 6 * 2 + 44 * 3 < 150 := by norm_num

theorem pairs_150 (hres : ResidueData) : PairsIn 41912890 := by
  obtain ⟨hlen, hPcl⟩ := hres
  have hnodup : cleanPrimes150.Nodup := by decide +kernel
  have hge : ∀ p ∈ cleanPrimes150, 313 ≤ p := by decide +kernel
  have hs2 : ∀ y ∈ cleanPrimes150, 313 < y → 359 ≤ y := by decide +kernel
  have hs3 : ∀ z ∈ cleanPrimes150, 359 < z → 373 ≤ z := by decide +kernel
  have hPcard : cleanPrimes150.toFinset.card = 150 := by
    rw [List.toFinset_card_of_nodup hnodup, hlen]
  have hP : ∀ p ∈ cleanPrimes150.toFinset, p.Prime ∧ 313 ≤ p ∧ CleanPrime p := by
    intro p hp
    rw [List.mem_toFinset] at hp
    exact ⟨(hPcl p hp).1, hge p hp, (hPcl p hp).2⟩
  have htrip := triple_of_stages cleanPrimes150.toFinset 313 359 373
    (fun x hx => hge x (List.mem_toFinset.mp hx))
    (fun y hy => hs2 y (List.mem_toFinset.mp hy))
    (fun z hz => hs3 z (List.mem_toFinset.mp hz))
  intro v hpos hB hML
  refine box_pairs cleanPrimes150.toFinset 313 41912890 2 3 (by norm_num) hP ?_ ?_
    (by rw [hPcard]; norm_num) v hpos hB hML
  · intro S hS m hm hmB hd
    exact card_dvd_le_two S (313 * 359 * 373) (fun p hp => (hP p (hS hp)).1) (fun x hx y hy z hz => htrip x (hS hx) y (hS hy) z (hS hz))
      m hm (by norm_num; omega) hd
  · intro S hS m hm hmB hd
    exact card_dvd_le' 313 (by norm_num) S (fun p hp => ⟨(hP p (hS hp)).1, (hP p (hS hp)).2.1⟩)
      m (11 * 41912890) 3 hm hmB (by norm_num) hd

theorem TheoremBox_150 (hres : ResidueData) : TheoremBox 41912890 :=
  box_of_pairs _ (pairs_150 hres)

/-! #### 111 primes, B = 17,581,557 -/

theorem arith111 : 571 * 577 * 587 = 193397129 ∧ 11 * 17581557 < 193397129 ∧
    193397129 ≤ 11 * 17581558 ∧ 6 * 2 + 44 * 2 < 111 := by norm_num

theorem pairs_111 (hres : ResidueData111) : PairsIn 17581557 := by
  obtain ⟨hlen, hPcl⟩ := hres
  have hnodup : cleanPrimes111.Nodup := cleanPrimes111_nodup
  have hge : ∀ p ∈ cleanPrimes111, 571 ≤ p := by decide +kernel
  have hs2 : ∀ y ∈ cleanPrimes111, 571 < y → 577 ≤ y := by decide +kernel
  have hs3 : ∀ z ∈ cleanPrimes111, 577 < z → 587 ≤ z := by decide +kernel
  have hPcard : cleanPrimes111.toFinset.card = 111 := by
    rw [List.toFinset_card_of_nodup hnodup, hlen]
  have hP : ∀ p ∈ cleanPrimes111.toFinset, p.Prime ∧ 571 ≤ p ∧ CleanPrime p := by
    intro p hp
    rw [List.mem_toFinset] at hp
    exact ⟨(hPcl p hp).1, hge p hp, (hPcl p hp).2⟩
  have htrip := triple_of_stages cleanPrimes111.toFinset 571 577 587
    (fun x hx => hge x (List.mem_toFinset.mp hx))
    (fun y hy => hs2 y (List.mem_toFinset.mp hy))
    (fun z hz => hs3 z (List.mem_toFinset.mp hz))
  intro v hpos hB hML
  refine box_pairs cleanPrimes111.toFinset 571 17581557 2 2 (by norm_num) hP ?_ ?_
    (by rw [hPcard]; norm_num) v hpos hB hML
  · intro S hS m hm hmB hd
    exact card_dvd_le_two S (571 * 577 * 587) (fun p hp => (hP p (hS hp)).1) (fun x hx y hy z hz => htrip x (hS hx) y (hS hy) z (hS hz))
      m hm (by norm_num; omega) hd
  · intro S hS m hm hmB hd
    exact card_dvd_le_two S (571 * 577 * 587) (fun p hp => (hP p (hS hp)).1) (fun x hx y hy z hz => htrip x (hS hx) y (hS hy) z (hS hz))
      m hm (by norm_num; omega) hd

theorem TheoremBox_111 (hres : ResidueData111) : TheoremBox 17581557 :=
  box_of_pairs _ (pairs_111 hres)

end Sext6
end LRSpectrumFull

#print axioms LRSpectrumFull.Sext6.box_pairs
#print axioms LRSpectrumFull.Sext6.TheoremBox_150
#print axioms LRSpectrumFull.Sext6.TheoremBox_111
#print axioms LRSpectrumFull.Sext6.arith150
#print axioms LRSpectrumFull.Sext6.arith111
