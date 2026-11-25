import Mathlib.Combinatorics.Pigeonhole
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Nat.GCD.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

/-!
# Theorem OE-low, Lemma P (pigeonhole on the three bad residue classes)  [2026-11-24]

Source: the accompanying notes on Theorem OE section 3 (Lemma P) and section 7 (LR-4).

Seven primes `p ≥ B := N + 1 + r`, each dividing one of `w`, `w - r`, `w + r`: three of them divide the
same one of the three numbers, hence their product `≥ B^3` divides it, hence `B^3 ≤ w + r`.

* `three_primes_cube_le` : three distinct primes `≥ B` dividing a positive `M` force `B^3 ≤ M`.
* `pigeon_small`         : the seven-prime pigeonhole, in the integer divisibility form used by
                           `ML_ge_inv_fam`.
No `sorry`, no `axiom`.

Convention: `N = k + 1` is the number of entries (speeds) of the one-entry vector `wFam k r w = ([1,N] \ {r}) ∪ {w}`. Speeds are the moving runners; the runner at rest is not counted, so a vector of `N` speeds means `N + 1` runners and the Lonely Runner value is `1/(N+1)`.
Hypotheses: those of the individual statements (numerical bounds, structural conditions and, where named in the list above, window predicates such as `PrimeWin`, `CopWin`, `PrimeWindow7`, which later modules discharge for explicit ranges). The unproved predicates `DusartPi`, `LRCHyp`, `CopWinHyp` are not hypotheses of any statement in this module.
Axiom audit: covered by `Axioms5` (first); every later audit module imports this module (`#print axioms`; declarations not printed there are bricks of printed ones, so their axioms are bounded by the printed lines).
-/

namespace LRSpectrumFull
namespace Sext6
namespace Gap

/-- Three distinct primes, each `≥ B`, dividing a positive `M`, force `B ^ 3 ≤ M`. -/
theorem three_primes_cube_le {S : Finset ℕ} {B M : ℕ} (hcard : 2 < S.card)
    (hprime : ∀ p ∈ S, p.Prime) (hB : ∀ p ∈ S, B ≤ p) (hM : 0 < M)
    (hdvd : ∀ p ∈ S, p ∣ M) : B ^ 3 ≤ M := by
  obtain ⟨a, ha, b, hb, c, hc, hab, hac, hbc⟩ := Finset.two_lt_card.mp hcard
  have hab' : Nat.Coprime a b := (Nat.coprime_primes (hprime a ha) (hprime b hb)).mpr hab
  have hac' : Nat.Coprime a c := (Nat.coprime_primes (hprime a ha) (hprime c hc)).mpr hac
  have hbc' : Nat.Coprime b c := (Nat.coprime_primes (hprime b hb) (hprime c hc)).mpr hbc
  have h1 : a * b ∣ M := Nat.Coprime.mul_dvd_of_dvd_of_dvd hab' (hdvd a ha) (hdvd b hb)
  have h2 : a * b * c ∣ M :=
    Nat.Coprime.mul_dvd_of_dvd_of_dvd (Nat.Coprime.mul_left hac' hbc') h1 (hdvd c hc)
  have h3 : a * b * c ≤ M := Nat.le_of_dvd hM h2
  have h4 : B * B * B ≤ a * b * c :=
    Nat.mul_le_mul (Nat.mul_le_mul (hB a ha) (hB b hb)) (hB c hc)
  calc B ^ 3 = B * B * B := by ring
    _ ≤ M := h4.trans h3

open Classical in
/-- Which of the three bad classes `p` divides: `0` for `w`, `1` for `w - r`, `2` otherwise. -/
noncomputable def failClass (w r p : ℕ) : ℕ :=
  if (p : ℤ) ∣ (w : ℤ) then 0 else if (p : ℤ) ∣ (w : ℤ) - (r : ℤ) then 1 else 2

theorem failClass_le (w r p : ℕ) : failClass w r p < 3 := by
  unfold failClass
  by_cases h0 : (p : ℤ) ∣ (w : ℤ)
  · rw [if_pos h0]; norm_num
  · rw [if_neg h0]
    by_cases h1 : (p : ℤ) ∣ (w : ℤ) - (r : ℤ)
    · rw [if_pos h1]; norm_num
    · rw [if_neg h1]; norm_num

theorem failClass_zero {w r p : ℕ} (h : failClass w r p = 0) : (p : ℤ) ∣ (w : ℤ) := by
  unfold failClass at h
  by_cases h0 : (p : ℤ) ∣ (w : ℤ)
  · exact h0
  · rw [if_neg h0] at h
    by_cases h1 : (p : ℤ) ∣ (w : ℤ) - (r : ℤ)
    · rw [if_pos h1] at h; exact absurd h (by norm_num)
    · rw [if_neg h1] at h; exact absurd h (by norm_num)

theorem failClass_one {w r p : ℕ} (h : failClass w r p = 1) : (p : ℤ) ∣ (w : ℤ) - (r : ℤ) := by
  unfold failClass at h
  by_cases h0 : (p : ℤ) ∣ (w : ℤ)
  · rw [if_pos h0] at h; exact absurd h (by norm_num)
  · rw [if_neg h0] at h
    by_cases h1 : (p : ℤ) ∣ (w : ℤ) - (r : ℤ)
    · exact h1
    · rw [if_neg h1] at h; exact absurd h (by norm_num)

theorem failClass_two {w r p : ℕ} (h : failClass w r p = 2) :
    ¬ ((p : ℤ) ∣ (w : ℤ)) ∧ ¬ ((p : ℤ) ∣ (w : ℤ) - (r : ℤ)) := by
  unfold failClass at h
  by_cases h0 : (p : ℤ) ∣ (w : ℤ)
  · rw [if_pos h0] at h; exact absurd h (by norm_num)
  · rw [if_neg h0] at h
    by_cases h1 : (p : ℤ) ∣ (w : ℤ) - (r : ℤ)
    · rw [if_pos h1] at h; exact absurd h (by norm_num)
    · exact ⟨h0, h1⟩

/-- **Lemma P (pigeonhole).**  If `S` is a set of at least seven primes `≥ N + 1 + r` and every `p ∈ S`
divides one of `w`, `w - r`, `w + r` (in `ℤ`), then `(N + 1 + r)^3 ≤ w + r`. -/
theorem pigeon_small {N r w : ℕ} (S : Finset ℕ) (hprime : ∀ p ∈ S, p.Prime)
    (hge : ∀ p ∈ S, N + 1 + r ≤ p) (hcard : 7 ≤ S.card) (hrN : r ≤ N) (hw : N < w)
    (hfail : ∀ p ∈ S, ((p : ℤ) ∣ (w : ℤ)) ∨ ((p : ℤ) ∣ (w : ℤ) - (r : ℤ)) ∨
      ((p : ℤ) ∣ (w : ℤ) + (r : ℤ))) :
    (N + 1 + r) ^ 3 ≤ w + r := by
  have hmaps : ∀ p ∈ S, failClass w r p ∈ Finset.range 3 := by
    intro p _
    exact Finset.mem_range.mpr (failClass_le w r p)
  have hn : (Finset.range 3).card * 2 < S.card := by
    rw [Finset.card_range]; omega
  obtain ⟨y, hy, hlt⟩ := Finset.exists_lt_card_fiber_of_mul_lt_card_of_maps_to hmaps hn
  have hy3 : y = 0 ∨ y = 1 ∨ y = 2 := by
    have := Finset.mem_range.mp hy
    omega
  have key : ∀ M : ℕ, 0 < M → (∀ p, p ∈ S → failClass w r p = y → p ∣ M) →
      (N + 1 + r) ^ 3 ≤ M := by
    intro M hM hdvd
    refine three_primes_cube_le (S := S.filter (fun x => failClass w r x = y)) hlt ?_ ?_ hM ?_
    · intro p hp
      exact hprime p (Finset.mem_filter.mp hp).1
    · intro p hp
      exact hge p (Finset.mem_filter.mp hp).1
    · intro p hp
      have := Finset.mem_filter.mp hp
      exact hdvd p this.1 this.2
  rcases hy3 with rfl | rfl | rfl
  · have h := key w (by omega) (fun p _ hp =>
      Int.natCast_dvd_natCast.mp (failClass_zero hp))
    omega
  · have hcast : ((w - r : ℕ) : ℤ) = (w : ℤ) - (r : ℤ) := by omega
    have h := key (w - r) (by omega) (fun p _ hp => by
      apply Int.natCast_dvd_natCast.mp
      rw [hcast]
      exact failClass_one hp)
    omega
  · have hcast : ((w + r : ℕ) : ℤ) = (w : ℤ) + (r : ℤ) := by push_cast; ring
    have h := key (w + r) (by omega) (fun p hpS hp => by
      apply Int.natCast_dvd_natCast.mp
      rw [hcast]
      obtain ⟨n0, n1⟩ := failClass_two hp
      rcases hfail p hpS with h0 | h1 | h2
      · exact absurd h0 n0
      · exact absurd h1 n1
      · exact h2)
    exact h

end Gap
end Sext6
end LRSpectrumFull
