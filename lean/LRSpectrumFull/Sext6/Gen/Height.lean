/-
# Gen/Height: generic height bound `heightBound_gen`  

Generalises `T2Height.T2_entry` (k = 5, Q = 21, tau = 1/7) to `Fin (k+1)` speeds, `Sext6.LRC k`, any `Q`:

  `Sext6.LRC k`, `v` positive primitive, `tau + 1/(2Q) <= 1/(k+1)`, `ML v <= tau`  ==>  every `v m <= Q^k`.

Proof = T2_entry verbatim (strict simultaneous Dirichlet with n = Q gives `0 < q <= Q^k`, `delta < 1/Q`; the rounded
`w` is not parallel to `v` by primitivity and `q < v m`; `two_dir_gen` gives `ML v >= 1/(k+1) - delta/2 > tau`).
Instances (all with equality `tau + 1/(2Q) = 1/(k+1)`, strictness from Dirichlet):
* N=6, tau=1/7 : k=5, Q=21, box 21^5 = 4,084,101   (`heightBound21_gen`, same Prop as T2Height.HeightBound21)
* N=6, tau=5/33: k=5, Q=33, box 33^5 = 39,135,393  (`HeightBound33`)
* N=7, tau=1/8 : k=6, Q=28, box 28^6 = 481,890,304 (`HeightBound28`, needs `Sext6.LRC 6`)
-/
import LRSpectrumFull.Sext6.Gen.TwoDir
import LRSpectrumFull.Sext6.T2Height
import LRSpectrumFull.GoNUpstream

namespace LRSpectrumFull
namespace Sext6

theorem heightBound_gen (k Q : ℕ) (hk : 1 ≤ k) (hQ : 0 < Q) (hL : Sext6.LRC k) (τ : ℝ)
    (hτ : τ + 1 / (2 * (Q : ℝ)) ≤ 1 / ((k : ℝ) + 1))
    (v : Fin (k + 1) → ℤ) (hpos : ∀ i, 0 < v i) (hprim : Primitive v)
    (hML : ML v ≤ τ) (m : Fin (k + 1)) : v m ≤ (Q : ℤ) ^ k := by
  by_contra hlt
  push_neg at hlt
  have hQr : (0 : ℝ) < (Q : ℝ) := by exact_mod_cast hQ
  have hvm : (0 : ℝ) < (v m : ℝ) := by exact_mod_cast hpos m
  have hvm' : (v m : ℝ) ≠ 0 := hvm.ne'
  obtain ⟨q, hq0, hq1, hq⟩ := exists_simultaneous_abs_mul_sub_round_lt
      (fun j : Fin k => (v (m.succAbove j) : ℝ) / (v m : ℝ)) (n := Q) hQ
  obtain ⟨t, ht⟩ : ∃ t : ℝ, t = (q : ℝ) / (v m : ℝ) := ⟨_, rfl⟩
  obtain ⟨w, hw⟩ : ∃ w : Fin (k + 1) → ℤ, w = fun i => round (t * (v i : ℝ)) := ⟨_, rfl⟩
  have htm : t * (v m : ℝ) = (q : ℝ) := by rw [ht]; field_simp
  have hwk : ∀ i, w i = round (t * (v i : ℝ)) := fun i => by rw [hw]
  have hwm : w m = q := by rw [hwk, htm]; exact round_intCast q
  have hbound : ∀ i, |(w i : ℝ) - t * v i| < 1 / (Q : ℝ) := by
    intro i
    by_cases hi : i = m
    · subst hi
      rw [hwm, htm, sub_self, abs_zero]
      exact one_div_pos.2 hQr
    · obtain ⟨j, hj⟩ := Fin.exists_succAbove_eq hi
      have h1 := hq j
      have h2 : (v (m.succAbove j) : ℝ) / (v m : ℝ) * (q : ℝ) = t * (v i : ℝ) := by
        rw [hj, ht]; ring
      simp only at h1
      rw [h2] at h1
      rw [hwk i, abs_sub_comm]
      exact h1
  obtain ⟨k0, -, hk0⟩ := Finset.exists_max_image (Finset.univ : Finset (Fin (k + 1)))
    (fun i => |(w i : ℝ) - t * v i|) ⟨0, Finset.mem_univ _⟩
  have hδ : |(w k0 : ℝ) - t * v k0| < 1 / (Q : ℝ) := hbound k0
  have he : ∀ i, |(w i : ℝ) - t * v i| ≤ |(w k0 : ℝ) - t * v k0| :=
    fun i => hk0 i (Finset.mem_univ _)
  have hnp : ∃ i j, v i * w j - v j * w i ≠ 0 := by
    by_contra hcon
    push_neg at hcon
    have hpar : ∀ i, v m * w i = q * v i := fun i => by
      have := hcon i m
      rw [hwm] at this
      linear_combination (-1 : ℤ) * this
    have hg : 0 < Int.gcd (v m) q := Int.gcd_pos_of_ne_zero_left _ (hpos m).ne'
    obtain ⟨g, a, b, hg0, hab, hva, hqb⟩ := Int.exists_gcd_one' hg
    have hcop : IsCoprime a b := Int.isCoprime_iff_gcd_eq_one.2 hab
    have hdiv : ∀ i, a ∣ v i := by
      intro i
      have h1 : (g : ℤ) * (a * w i) = (g : ℤ) * (b * v i) := by
        have := hpar i
        rw [hva, hqb] at this
        linear_combination this
      have h2 : a * w i = b * v i := mul_left_cancel₀ (by exact_mod_cast hg0.ne') h1
      have : a ∣ b * v i := ⟨w i, h2.symm⟩
      exact hcop.dvd_of_dvd_mul_left this
    have ha1 : a.natAbs = 1 := hprim a.natAbs (fun i => Int.natAbs_dvd.2 (hdiv i))
    have hvm0 := hpos m
    have hg1 : (0 : ℤ) < g := by exact_mod_cast hg0
    have ha' : a = 1 ∨ a = -1 := by omega
    rcases ha' with h | h
    · rw [h] at hva
      have hdq : v m ∣ q := ⟨b, by rw [hva, hqb]; ring⟩
      have hle := Int.le_of_dvd hq0 hdq
      linarith
    · rw [h] at hva
      omega
  have hfin := two_dir_gen k hk hL v w (fun i => (hpos i).ne') t _ he hnp
  have e2 : (1 : ℝ) / (2 * (Q : ℝ)) = (1 / (Q : ℝ)) / 2 := by
    rw [div_div, mul_comm (Q : ℝ) 2]
  linarith

/-- N = 6, `ML <= 1/7`: same statement as `T2Height.HeightBound21`, via the generic lemma. -/
theorem heightBound21_gen (h5 : Sext6.LRC 5) : HeightBound21 := by
  intro v hpos hprim hML i
  have := heightBound_gen 5 21 (by norm_num) (by norm_num) h5 (1 / 7) (by norm_num) v hpos hprim hML i
  simpa using this

/-- N = 6, sharp-gap threshold `5/33`: primitive positive `v` with `ML v <= 5/33` has all entries `<= 33^5`. -/
def HeightBound33 : Prop :=
  ∀ v : Fin 6 → ℤ, (∀ i, 0 < v i) → Primitive v → ML v ≤ 5 / 33 → ∀ i, v i ≤ 33 ^ 5

theorem heightBound33_of_LRC5 (h5 : Sext6.LRC 5) : HeightBound33 := by
  intro v hpos hprim hML i
  have := heightBound_gen 5 33 (by norm_num) (by norm_num) h5 (5 / 33) (by norm_num) v hpos hprim hML i
  simpa using this

/-- N = 7, `ML <= 1/8`: primitive positive `v : Fin 7 -> Z` has all entries `<= 28^6 = 481,890,304`. -/
def HeightBound28 : Prop :=
  ∀ v : Fin 7 → ℤ, (∀ i, 0 < v i) → Primitive v → ML v ≤ 1 / 8 → ∀ i, v i ≤ 28 ^ 6

theorem heightBound28_of_LRC6 (h6 : Sext6.LRC 6) : HeightBound28 := by
  intro v hpos hprim hML i
  have := heightBound_gen 6 28 (by norm_num) (by norm_num) h6 (1 / 8) (by norm_num) v hpos hprim hML i
  simpa using this

theorem box28_eq : (28 : ℤ) ^ 6 = 481890304 := by norm_num
theorem box33_eq : (33 : ℤ) ^ 5 = 39135393 := by norm_num

end Sext6
end LRSpectrumFull

#print axioms LRSpectrumFull.Sext6.heightBound_gen
#print axioms LRSpectrumFull.Sext6.heightBound21_gen
#print axioms LRSpectrumFull.Sext6.heightBound33_of_LRC5
#print axioms LRSpectrumFull.Sext6.heightBound28_of_LRC6
