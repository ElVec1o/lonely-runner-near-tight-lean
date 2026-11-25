/-
# PairLabel: from `CleanPrime` to the residue-label form consumed by `PairAgree`  [AL, 2026-11-24]

(1) `hasLabel_of_clean`: p prime, p > 12, `CleanPrime p`, `ML v <= 1/7`, p divides no speed.
    Then the speeds mod p are a signed permutation of `1..6` times a unit: there are `u, ub` (inverse),
    `s : Perm (Fin 6)` and signs `eps` with `p | v_i - u * (eps_i * (s_i + 1))` for all i.
    Proof: `L1bij` (L2.lean) gives the injective label `s : Fin 6 -> {1..6}`; it is turned into a permutation.
(2) `label_pair_divides`: two coprime moduli `p, q >= 253` with labels as in (1) and `ML v <= 1/7` give
    `p q | eps_l (s_l+1) v_k - eps_k (s_k+1) v_l` (reindexing by `s` and applying `PairAgree.agreement_divides`).
(3) `N_bound`: `|eps_l (s_l+1) v_k - eps_k (s_k+1) v_l| <= 11 B` when `|v| <= B`, `k != l`.
No sorry, no axiom, no native_decide.
-/
import LRSpectrumFull.Sext6.PairAgree
import LRSpectrumFull.Sext6.L2

namespace LRSpectrumFull
namespace Sext6

/-- The speeds `v`, read modulo `p`, are a signed permutation of `1..6` times a unit `u`. -/
def HasLabel (p : ℕ) (v : Fin 6 → ℤ) : Prop :=
  ∃ (u ub : ℤ) (s : Equiv.Perm (Fin 6)) (ε : Fin 6 → ℤ),
    (p : ℤ) ∣ u * ub - 1 ∧ (∀ i, ε i = 1 ∨ ε i = -1) ∧
    ∀ i, (p : ℤ) ∣ v i - u * (ε i * (((s i : ℕ) : ℤ) + 1))

theorem exists_inv (p : ℕ) (hp : p.Prime) (u : ℤ) (hu : ¬ (p : ℤ) ∣ u) :
    ∃ ub : ℤ, (p : ℤ) ∣ u * ub - 1 := by
  have hc : IsCoprime (p : ℤ) u := by
    rw [Int.isCoprime_iff_gcd_eq_one]
    have h : Nat.Coprime p u.natAbs :=
      (Nat.Prime.coprime_iff_not_dvd hp).2 (fun h => hu (Int.ofNat_dvd_left.mpr h))
    exact h
  obtain ⟨a, b, h⟩ := hc
  exact ⟨b, ⟨-a, by linear_combination h⟩⟩

/-- **Label extraction.** -/
theorem hasLabel_of_clean (p : ℕ) (hp : p.Prime) (hp12 : 12 < p) (hclean : CleanPrime p)
    (v : Fin 6 → ℤ) (hML : ML v ≤ 1 / 7) (hnd : ∀ i, ¬ (p : ℤ) ∣ v i) : HasLabel p v := by
  obtain ⟨u, hu, s, hs, hsinj, hdv⟩ := L1bij p hp hp12 hclean v hML hnd
  obtain ⟨ub, hub⟩ := exists_inv p hp u hu
  have hs' : ∀ i, 1 ≤ s i ∧ s i ≤ 6 := fun i => Finset.mem_Icc.mp (hs i)
  let f : Fin 6 → Fin 6 := fun i => ⟨(s i - 1).toNat, by have := hs' i; omega⟩
  have hf : Function.Injective f := by
    intro i j h
    have h1 : (s i - 1).toNat = (s j - 1).toNat := congrArg Fin.val h
    have := hs' i
    have := hs' j
    exact hsinj (by omega)
  let e : Equiv.Perm (Fin 6) := Equiv.ofBijective f (Finite.injective_iff_bijective.mp hf)
  have he : ∀ i, (((e i : Fin 6) : ℕ) : ℤ) + 1 = s i := by
    intro i
    have h1 : ((e i : Fin 6) : ℕ) = (s i - 1).toNat := rfl
    have := hs' i
    omega
  refine ⟨u, ub, e, fun i => if (p : ℤ) ∣ v i - u * s i then 1 else -1, hub, ?_, ?_⟩
  · intro i
    by_cases h : (p : ℤ) ∣ v i - u * s i
    · left; exact if_pos h
    · right; exact if_neg h
  · intro i
    beta_reduce
    by_cases h : (p : ℤ) ∣ v i - u * s i
    · have h1 : (if (p : ℤ) ∣ v i - u * s i then (1 : ℤ) else -1) = 1 := if_pos h
      rw [h1, he i, one_mul]
      exact h
    · have h1 : (if (p : ℤ) ∣ v i - u * s i then (1 : ℤ) else -1) = -1 := if_neg h
      rw [h1, he i]
      have h2 := (hdv i).resolve_left h
      have e2 : v i - u * (-1 * s i) = v i + u * s i := by ring
      rw [e2]
      exact h2

/-- **Pair divisibility.** -/
theorem label_pair_divides (p q : ℕ) (hp : 253 ≤ p) (hq : 253 ≤ q) (hpq : Nat.Coprime p q)
    (v : Fin 6 → ℤ) (hML : ML v ≤ 1 / 7)
    (u ub : ℤ) (s : Equiv.Perm (Fin 6)) (ε : Fin 6 → ℤ)
    (hu : (p : ℤ) ∣ u * ub - 1) (hε : ∀ i, ε i = 1 ∨ ε i = -1)
    (hv : ∀ i, (p : ℤ) ∣ v i - u * (ε i * (((s i : ℕ) : ℤ) + 1)))
    (u' ub' : ℤ) (s' : Equiv.Perm (Fin 6)) (ε' : Fin 6 → ℤ)
    (hu' : (q : ℤ) ∣ u' * ub' - 1) (hε' : ∀ i, ε' i = 1 ∨ ε' i = -1)
    (hv' : ∀ i, (q : ℤ) ∣ v i - u' * (ε' i * (((s' i : ℕ) : ℤ) + 1)))
    (B : ℤ) (hB : ∀ i, |v i| ≤ B) (k l : Fin 6) (hkl : k ≠ l) :
    ((p * q : ℕ) : ℤ) ∣ ε l * (((s l : ℕ) : ℤ) + 1) * v k - ε k * (((s k : ℕ) : ℤ) + 1) * v l := by
  set w : Fin 6 → ℤ := fun m => v (s.symm m) with hw
  have hit : Hit (p * q) (Finset.univ.image w) := by
    have h0 := L1 v hML (p * q) (Nat.mul_pos (by omega) (by omega))
    have himg : Finset.univ.image w = Finset.univ.image v := by
      ext x
      simp only [Finset.mem_image, Finset.mem_univ, true_and]
      constructor
      · rintro ⟨m, rfl⟩
        exact ⟨_, rfl⟩
      · rintro ⟨i, rfl⟩
        exact ⟨s i, by simp [hw]⟩
    rw [himg]
    exact h0
  have hwp : ∀ m, (p : ℤ) ∣ w m - u * ((fun m => ε (s.symm m)) m * (((m : ℕ) : ℤ) + 1)) := by
    intro m
    simpa [hw] using hv (s.symm m)
  have hwq : ∀ m, (q : ℤ) ∣ w m - u' * ((fun m => ε' (s.symm m)) m *
      ((((s.symm.trans s') m : ℕ) : ℤ) + 1)) := by
    intro m
    simpa [hw] using hv' (s.symm m)
  have := (agreement_divides p q hp hq hpq w u ub u' ub' (fun m => ε (s.symm m))
    (fun m => ε' (s.symm m)) (fun m => hε _) (fun m => hε' _) (s.symm.trans s') hu hu' hwp hwq hit B
    (fun i => hB _) (s k) (s l) (fun h => hkl (s.injective h))).1
  simpa [hw] using this

/-- The size bound for the pair integer. -/
theorem N_bound (s : Equiv.Perm (Fin 6)) (ε : Fin 6 → ℤ) (hε : ∀ i, ε i = 1 ∨ ε i = -1)
    (v : Fin 6 → ℤ) (B : ℤ) (hB : ∀ i, |v i| ≤ B) (k l : Fin 6) (hkl : k ≠ l) :
    |ε l * (((s l : ℕ) : ℤ) + 1) * v k - ε k * (((s k : ℕ) : ℤ) + 1) * v l| ≤ 11 * B := by
  have hm := (s k).isLt
  have hn := (s l).isLt
  have hmn' : ((s k : Fin 6) : ℕ) ≠ ((s l : Fin 6) : ℕ) := fun h => hkl (s.injective (Fin.ext h))
  have bm := hB k
  have bn := hB l
  have e1 : |ε l * (((s l : ℕ) : ℤ) + 1) * v k| ≤ (((s l : ℕ) : ℤ) + 1) * B := by
    rw [abs_mul, abs_mul]
    have : |ε l| = 1 := by rcases hε l with h | h <;> simp [h]
    rw [this, one_mul, abs_of_nonneg (by positivity)]
    exact mul_le_mul_of_nonneg_left bm (by positivity)
  have e2 : |ε k * (((s k : ℕ) : ℤ) + 1) * v l| ≤ (((s k : ℕ) : ℤ) + 1) * B := by
    rw [abs_mul, abs_mul]
    have : |ε k| = 1 := by rcases hε k with h | h <;> simp [h]
    rw [this, one_mul, abs_of_nonneg (by positivity)]
    exact mul_le_mul_of_nonneg_left bn (by positivity)
  have hB0 : 0 ≤ B := le_trans (abs_nonneg _) bm
  have hsum : (((s k : ℕ) : ℤ) + 1) + (((s l : ℕ) : ℤ) + 1) ≤ 11 := by
    have : ((s k : Fin 6) : ℕ) + ((s l : Fin 6) : ℕ) ≤ 9 := by omega
    have : (((s k : Fin 6) : ℕ) : ℤ) + (((s l : Fin 6) : ℕ) : ℤ) ≤ 9 := by exact_mod_cast this
    linarith
  have hs : ((((s k : ℕ) : ℤ) + 1) + (((s l : ℕ) : ℤ) + 1)) * B ≤ 11 * B :=
    mul_le_mul_of_nonneg_right hsum hB0
  have := abs_sub (ε l * (((s l : ℕ) : ℤ) + 1) * v k) (ε k * (((s k : ℕ) : ℤ) + 1) * v l)
  linarith

end Sext6
end LRSpectrumFull

#print axioms LRSpectrumFull.Sext6.hasLabel_of_clean
#print axioms LRSpectrumFull.Sext6.label_pair_divides
#print axioms LRSpectrumFull.Sext6.N_bound
