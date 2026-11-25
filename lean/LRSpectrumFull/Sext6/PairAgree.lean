/-
# PairAgree: pair-agreement lemma at the level of residue labels (F2 part 3).  [AK, 2026-11-24]

`pair_round_all`: PairGrid + PairRound for a non-identical labeling (any naturals p, q >= 253).
`agreement`: if the speeds `w m` (reindexed so that the label at `p` is `eps_m * (m+1)`) have label at `q` equal
to `eps'_m * (sigma m + 1)`, both up to a unit (`u`, `u'` invertible mod `p`, `q`), and `p, q` are coprime
and `>= 253`, and the speeds form a hitting set mod `p*q` (this is what `ML <= 1/7` gives via L1), then
`sigma = id` and `eps_m * eps'_m` is constant.  The label EXTRACTION from `CleanPrime` (that the residues of
the speeds are a signed permutation of 1..6 times a unit) is NOT done here.
`agreement_divides`: then `p*q` divides `eps_n (n+1) w_m - eps_m (m+1) w_n` (for m, n), of size `<= 11 B`.
-/
import LRSpectrumFull.Sext6.PairRound
import Mathlib.Data.ZMod.Basic
import Mathlib.RingTheory.Coprime.Basic
import Mathlib.RingTheory.Coprime.Lemmas

namespace LRSpectrumFull
namespace Sext6

theorem pair_round_all (p q : ℕ) (hp : 253 ≤ p) (hq : 253 ≤ q) (σ : Equiv.Perm (Fin 6)) (η : Fin 6 → ℤ)
    (hη : ∀ m, η m = 1 ∨ η m = -1) (h0 : η 0 = 1)
    (hne : ∃ m : Fin 6, η m * (((σ m : ℕ) : ℤ) + 1) ≠ ((m : ℕ) : ℤ) + 1) :
    ∃ x y : ℤ, ∀ m : Fin 6, ((p * q : ℕ) : ℤ) <
      7 * bdist (p * q) (x * (((m : ℕ) : ℤ) + 1) * q + (η m * (((σ m : ℕ) : ℤ) + 1)) * y * p) := by
  obtain ⟨a, b, hg⟩ := pair_excl σ η hη h0 hne
  refine ⟨(2 * (p : ℤ) * a + 30) / 60, (2 * (q : ℤ) * b + 30) / 60, fun m => ?_⟩
  have hlt : ((σ m : ℕ) : ℤ) < 6 := by exact_mod_cast (σ m).isLt
  have hm : ((m : ℕ) : ℤ) < 6 := by exact_mod_cast m.isLt
  have hσ0 : (0 : ℤ) ≤ ((σ m : ℕ) : ℤ) := by positivity
  have hm0 : (0 : ℤ) ≤ ((m : ℕ) : ℤ) := by positivity
  have := round_slot p q hp hq a b (((m : ℕ) : ℤ) + 1) (η m * (((σ m : ℕ) : ℤ) + 1))
    ⟨by linarith, by linarith⟩
    (by rcases hη m with h | h <;> rw [h] <;> constructor <;> linarith) (hg m)
  simpa [mul_comm, mul_assoc, mul_left_comm] using this

theorem bdist_dvd (N : ℕ) (x y : ℤ) (h : (N : ℤ) ∣ x - y) : bdist N x = bdist N y := by
  have : x % (N : ℤ) = y % (N : ℤ) := (Int.modEq_iff_dvd.2 (by simpa using h)).symm
  unfold bdist; rw [this]

theorem bdist_neg (N : ℕ) (hN : 0 < N) (z : ℤ) : bdist N (-z) = bdist N z := by
  unfold bdist
  have hN' : (0 : ℤ) < N := by exact_mod_cast hN
  have h1 := Int.emod_nonneg z hN'.ne'
  have h2 := Int.emod_lt_of_pos z hN'
  have h3 := Int.mul_ediv_add_emod z N
  rcases eq_or_lt_of_le h1 with h | h
  · have : (-z) % (N : ℤ) = 0 := by
      apply Int.emod_eq_zero_of_dvd
      refine ⟨-(z / N), ?_⟩
      rw [← h] at h3; linarith
    rw [this, ← h]
  · have : (-z) % (N : ℤ) = (N : ℤ) - z % N := by
      have : -z = (N - z % N) + N * (-(z / N) - 1) := by linarith
      rw [this, Int.add_mul_emod_self_left, Int.emod_eq_of_lt (by linarith) (by linarith)]
    rw [this]
    rcases le_total (z % (N : ℤ)) ((N : ℤ) - z % N) with h' | h'
    · rw [min_eq_left h', min_eq_right (by linarith)]; ring_nf
    · rw [min_eq_right h', min_eq_left (by linarith)]

theorem bdist_sign (N : ℕ) (hN : 0 < N) (e z : ℤ) (he : e = 1 ∨ e = -1) : bdist N (e * z) = bdist N z := by
  rcases he with rfl | rfl
  · simp
  · simpa using bdist_neg N hN z

theorem crt_two (P Q : ℤ) (hc : IsCoprime P Q) (A B : ℤ) : ∃ a0 : ℤ, P ∣ a0 - A ∧ Q ∣ a0 - B := by
  obtain ⟨s, t, h⟩ := hc
  refine ⟨A * (t * Q) + B * (s * P), ⟨s * (B - A), ?_⟩, ⟨t * (A - B), ?_⟩⟩
  · linear_combination A * h
  · linear_combination B * h

theorem dvd_part (m w u ub e X a0 R : ℤ) (h1 : m ∣ w - u * e) (h2 : m ∣ u * ub - 1)
    (h3 : m ∣ a0 - ub * X) (h4 : m ∣ R) : m ∣ w * a0 - e * X - R := by
  obtain ⟨k1, hk1⟩ := h1
  obtain ⟨k2, hk2⟩ := h2
  obtain ⟨k3, hk3⟩ := h3
  obtain ⟨k4, hk4⟩ := h4
  refine ⟨e * X * k2 + u * e * k3 + k1 * a0 - k4, ?_⟩
  linear_combination a0 * hk1 + (u * e) * hk3 + (e * X) * hk2 - hk4

/-- **Pair agreement (residue-label level).** -/
theorem agreement (p q : ℕ) (hp : 253 ≤ p) (hq : 253 ≤ q) (hpq : Nat.Coprime p q)
    (w : Fin 6 → ℤ) (u ub u' ub' : ℤ) (ε ε' : Fin 6 → ℤ)
    (hε : ∀ m, ε m = 1 ∨ ε m = -1) (hε' : ∀ m, ε' m = 1 ∨ ε' m = -1) (σ : Equiv.Perm (Fin 6))
    (hu : (p : ℤ) ∣ u * ub - 1) (hu' : (q : ℤ) ∣ u' * ub' - 1)
    (hwp : ∀ m, (p : ℤ) ∣ w m - u * (ε m * (((m : ℕ) : ℤ) + 1)))
    (hwq : ∀ m, (q : ℤ) ∣ w m - u' * (ε' m * (((σ m : ℕ) : ℤ) + 1)))
    (hit : Hit (p * q) (Finset.univ.image w)) :
    (∀ m, σ m = m) ∧ ∀ m, ε m * ε' m = ε 0 * ε' 0 := by
  by_contra hcon
  set g : ℤ := ε 0 * ε' 0 with hg
  have hgpm : g = 1 ∨ g = -1 := by
    rcases hε 0 with h | h <;> rcases hε' 0 with h' | h' <;> simp [hg, h, h']
  set η : Fin 6 → ℤ := fun m => g * (ε m * ε' m) with hη
  have hηpm : ∀ m, η m = 1 ∨ η m = -1 := by
    intro m
    rcases hgpm with h | h <;> rcases hε m with h1 | h1 <;> rcases hε' m with h2 | h2 <;>
      simp [hη, h, h1, h2]
  have hη0 : η 0 = 1 := by
    rcases hgpm with h | h <;> simp [hη, hg] at * <;> rcases hε 0 with h1 | h1 <;> rcases hε' 0 with h2 | h2 <;>
      simp_all
  have hne : ∃ m : Fin 6, η m * (((σ m : ℕ) : ℤ) + 1) ≠ ((m : ℕ) : ℤ) + 1 := by
    by_contra hall
    push Not at hall
    apply hcon
    have key : ∀ m, σ m = m ∧ ε m * ε' m = g := by
      intro m
      have h := hall m
      have hl := (σ m).isLt
      rcases hηpm m with h1 | h1
      · rw [h1] at h
        refine ⟨Fin.ext (by omega), ?_⟩
        rcases hgpm with h2 | h2 <;> simp only [hη] at h1 <;> rcases hε m with h3 | h3 <;>
          rcases hε' m with h4 | h4 <;> simp_all
      · rw [h1] at h; omega
    exact ⟨fun m => (key m).1, fun m => (key m).2⟩
  have hNp : (p : ℤ) ≠ 0 := by omega
  obtain ⟨x, y, hxy⟩ := pair_round_all p q hp hq σ η hηpm hη0 hne
  have hcop : IsCoprime (p : ℤ) (q : ℤ) := by exact_mod_cast Nat.isCoprime_iff_coprime.2 hpq
  obtain ⟨a0, ha1, ha2⟩ := crt_two (p : ℤ) q hcop (ub * (x * q)) (ub' * (g * y * p))
  have hNpos : 0 < p * q := by positivity
  have hc7 : ∀ m : Fin 6, ((p * q : ℕ) : ℤ) < 7 * bdist (p * q) (w m * a0) := by
    intro m
    have hdp : (p : ℤ) ∣ w m * a0 - (ε m * (((m : ℕ) : ℤ) + 1)) * (x * q) -
        (ε' m * (((σ m : ℕ) : ℤ) + 1)) * (g * y * p) := by
      apply dvd_part p (w m) u ub (ε m * (((m : ℕ) : ℤ) + 1)) (x * q) a0 _ (hwp m) hu ha1
      exact ⟨(ε' m * (((σ m : ℕ) : ℤ) + 1)) * (g * y), by ring⟩
    have hdq : (q : ℤ) ∣ w m * a0 - (ε' m * (((σ m : ℕ) : ℤ) + 1)) * (g * y * p) -
        (ε m * (((m : ℕ) : ℤ) + 1)) * (x * q) := by
      apply dvd_part q (w m) u' ub' (ε' m * (((σ m : ℕ) : ℤ) + 1)) (g * y * p) a0 _ (hwq m) hu' ha2
      exact ⟨(ε m * (((m : ℕ) : ℤ) + 1)) * x, by ring⟩
    have hdq' : (q : ℤ) ∣ w m * a0 - (ε m * (((m : ℕ) : ℤ) + 1)) * (x * q) -
        (ε' m * (((σ m : ℕ) : ℤ) + 1)) * (g * y * p) := by
      have := hdq; rw [show w m * a0 - (ε' m * (((σ m : ℕ) : ℤ) + 1)) * (g * y * p) -
        (ε m * (((m : ℕ) : ℤ) + 1)) * (x * q) = w m * a0 - (ε m * (((m : ℕ) : ℤ) + 1)) * (x * q) -
        (ε' m * (((σ m : ℕ) : ℤ) + 1)) * (g * y * p) by ring] at this
      exact this
    have hdN := IsCoprime.mul_dvd hcop hdp hdq'
    have hdN' : ((p * q : ℕ) : ℤ) ∣ w m * a0 - ((ε m * (((m : ℕ) : ℤ) + 1)) * (x * q) +
        (ε' m * (((σ m : ℕ) : ℤ) + 1)) * (g * y * p)) := by
      push_cast; convert hdN using 1; ring
    rw [bdist_dvd (p * q) _ _ hdN']
    have hV : (ε m * (((m : ℕ) : ℤ) + 1)) * (x * q) + (ε' m * (((σ m : ℕ) : ℤ) + 1)) * (g * y * p)
        = ε m * (x * (((m : ℕ) : ℤ) + 1) * q + (η m * (((σ m : ℕ) : ℤ) + 1)) * y * p) := by
      have hsq : ε m * ε m = 1 := by rcases hε m with h | h <;> simp [h]
      simp only [hη]
      linear_combination (-(ε' m * (((σ m : ℕ) : ℤ) + 1)) * g * y * p) * hsq
    rw [hV, bdist_sign (p * q) hNpos _ _ (hε m)]
    exact hxy m
  have hN0 : ¬ ((p * q : ℕ) : ℤ) ∣ a0 := by
    intro hd
    have := hc7 0
    have h0 : ((p * q : ℕ) : ℤ) ∣ w 0 * a0 := Dvd.dvd.mul_left hd _
    have : bdist (p * q) (w 0 * a0) = 0 := by
      unfold bdist; rw [Int.emod_eq_zero_of_dvd h0]; simp; positivity
    have := hc7 0
    rw [‹bdist (p * q) (w 0 * a0) = 0›] at this
    have hpos : (0 : ℤ) < ((p * q : ℕ) : ℤ) := by exact_mod_cast hNpos
    linarith
  obtain ⟨r, hr, hle⟩ := hit a0 hN0
  obtain ⟨m, -, rfl⟩ := Finset.mem_image.1 hr
  have := hc7 m
  have hpos : ((p * q : ℕ) : ℤ) = ((p * q : ℕ) : ℤ) := rfl
  have hle' : 7 * bdist (p * q) (w m * a0) ≤ ((p * q : ℕ) : ℤ) := by exact_mod_cast hle
  linarith

/-- **Consequence.** Under the hypotheses of `agreement`, for `m ≠ n` the product `p*q` divides
`N_mn = ε_n (n+1) w_m - ε_m (m+1) w_n`, and `|N_mn| ≤ 11 B` when `|w i| ≤ B`. -/
theorem agreement_divides (p q : ℕ) (hp : 253 ≤ p) (hq : 253 ≤ q) (hpq : Nat.Coprime p q)
    (w : Fin 6 → ℤ) (u ub u' ub' : ℤ) (ε ε' : Fin 6 → ℤ)
    (hε : ∀ m, ε m = 1 ∨ ε m = -1) (hε' : ∀ m, ε' m = 1 ∨ ε' m = -1) (σ : Equiv.Perm (Fin 6))
    (hu : (p : ℤ) ∣ u * ub - 1) (hu' : (q : ℤ) ∣ u' * ub' - 1)
    (hwp : ∀ m, (p : ℤ) ∣ w m - u * (ε m * (((m : ℕ) : ℤ) + 1)))
    (hwq : ∀ m, (q : ℤ) ∣ w m - u' * (ε' m * (((σ m : ℕ) : ℤ) + 1)))
    (hit : Hit (p * q) (Finset.univ.image w)) (B : ℤ) (hB : ∀ i, |w i| ≤ B) (m n : Fin 6) (hmn : m ≠ n) :
    ((p * q : ℕ) : ℤ) ∣ ε n * (((n : ℕ) : ℤ) + 1) * w m - ε m * (((m : ℕ) : ℤ) + 1) * w n ∧
    |ε n * (((n : ℕ) : ℤ) + 1) * w m - ε m * (((m : ℕ) : ℤ) + 1) * w n| ≤ 11 * B := by
  obtain ⟨hσ, hg⟩ := agreement p q hp hq hpq w u ub u' ub' ε ε' hε hε' σ hu hu' hwp hwq hit
  have hcop : IsCoprime (p : ℤ) (q : ℤ) := by exact_mod_cast Nat.isCoprime_iff_coprime.2 hpq
  have hε'g : ∀ i, ε' i = (ε 0 * ε' 0) * ε i := by
    intro i
    have := hg i
    rcases hε i with h | h <;> rcases hε' i with h' | h' <;> rw [← this] <;> simp [h, h']
  refine ⟨?_, ?_⟩
  · have h1 : (p : ℤ) ∣ ε n * (((n : ℕ) : ℤ) + 1) * w m - ε m * (((m : ℕ) : ℤ) + 1) * w n := by
      have := dvd_sub (Dvd.dvd.mul_left (hwp m) (ε n * (((n : ℕ) : ℤ) + 1)))
        (Dvd.dvd.mul_left (hwp n) (ε m * (((m : ℕ) : ℤ) + 1)))
      convert this using 1; ring
    have h2 : (q : ℤ) ∣ ε n * (((n : ℕ) : ℤ) + 1) * w m - ε m * (((m : ℕ) : ℤ) + 1) * w n := by
      have e : ∀ i, w i - u' * (ε i * (((i : ℕ) : ℤ) + 1) * (ε 0 * ε' 0)) =
          w i - u' * (ε' i * (((σ i : ℕ) : ℤ) + 1)) := by
        intro i
        rw [hσ i, hε'g i]; ring
      have a1 := hwq m
      have a2 := hwq n
      rw [← e] at a1 a2
      have := dvd_sub (Dvd.dvd.mul_left a1 (ε n * (((n : ℕ) : ℤ) + 1)))
        (Dvd.dvd.mul_left a2 (ε m * (((m : ℕ) : ℤ) + 1)))
      convert this using 1; ring
    exact_mod_cast IsCoprime.mul_dvd hcop h1 h2
  · have hm := m.isLt
    have hn := n.isLt
    have hmn' : (m : ℕ) ≠ n := fun h => hmn (Fin.ext h)
    have bm := hB m
    have bn := hB n
    have e1 : |ε n * (((n : ℕ) : ℤ) + 1) * w m| ≤ (((n : ℕ) : ℤ) + 1) * B := by
      rw [abs_mul, abs_mul]
      have : |ε n| = 1 := by rcases hε n with h | h <;> simp [h]
      rw [this, one_mul, abs_of_nonneg (by positivity)]
      exact mul_le_mul_of_nonneg_left bm (by positivity)
    have e2 : |ε m * (((m : ℕ) : ℤ) + 1) * w n| ≤ (((m : ℕ) : ℤ) + 1) * B := by
      rw [abs_mul, abs_mul]
      have : |ε m| = 1 := by rcases hε m with h | h <;> simp [h]
      rw [this, one_mul, abs_of_nonneg (by positivity)]
      exact mul_le_mul_of_nonneg_left bn (by positivity)
    have hB0 : 0 ≤ B := le_trans (abs_nonneg _) bm
    have hsum : (((m : ℕ) : ℤ) + 1) + (((n : ℕ) : ℤ) + 1) ≤ 11 := by
      have : (m : ℕ) + n ≤ 9 := by omega
      have : ((m : ℕ) : ℤ) + ((n : ℕ) : ℤ) ≤ 9 := by exact_mod_cast this
      linarith
    have hs : ((((m : ℕ) : ℤ) + 1) + (((n : ℕ) : ℤ) + 1)) * B ≤ 11 * B :=
      mul_le_mul_of_nonneg_right hsum hB0
    have := abs_sub (ε n * (((n : ℕ) : ℤ) + 1) * w m) (ε m * (((m : ℕ) : ℤ) + 1) * w n)
    linarith

end Sext6
end LRSpectrumFull

#print axioms LRSpectrumFull.Sext6.identical_not_excl30
#print axioms LRSpectrumFull.Sext6.pair_round_all
#print axioms LRSpectrumFull.Sext6.agreement
#print axioms LRSpectrumFull.Sext6.agreement_divides
