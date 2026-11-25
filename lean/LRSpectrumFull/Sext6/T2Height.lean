/-
# T2Height: the height bound from `LRC 5`, and Theorem A from `LRC 5` and 16 clean primes 

Central idea: a speed `v_m` larger than `21^5` allows a Dirichlet time `t = q / v_m` (`q <= 21^5`) at which all
six speeds are within `1/21` of integers; the rounded vector `w` is not parallel to `v` (primitivity and
`q < v_m`), so `two_dir` gives `ML v > 1/6 - 1/42 = 1/7`.

* `T2_entry`            : `LRC 5`, `v` positive primitive, `ML v <= 1/7`  =>  every `v m <= 21^5 = 4,084,101`.
* `HeightBound21`       : that statement as a `Prop`; `heightBound21_of_LRC5 : LRC 5 -> HeightBound21`.
* `heightBound_of_LRC5` : the older entry bound `< 17,010,000` of `Statement.HeightBound`, from `LRC 5` alone.
* `TheoremA16_LRC5`     : `LRC 5 -> ResidueDataSub P16 -> TheoremA`  (no YGB, no `LRC 4`).
Pair-route count at `B = 21^5 = 4,084,101`: `beta(B) = 2`, `beta(11 B) = 3`, `kappa' = 4`, so `6*2+3+1 = 16`
primes are needed (15 fail: `count_P15_T2_fails`).
-/
import LRSpectrumFull.Sext6.T2Core
import LRSpectrumFull.Sext6.PairFinal
import LRSpectrumFull.GoNUpstream

namespace LRSpectrumFull
namespace Sext6

theorem T2_entry (h5 : LRC 5) (v : Fin 6 → ℤ) (hpos : ∀ i, 0 < v i) (hprim : Primitive v)
    (hML : ML v ≤ 1 / 7) (m : Fin 6) : v m ≤ 21 ^ 5 := by
  by_contra hlt
  push_neg at hlt
  have hvm : (0 : ℝ) < (v m : ℝ) := by exact_mod_cast hpos m
  have hvm' : (v m : ℝ) ≠ 0 := hvm.ne'
  obtain ⟨q, hq0, hq1, hq⟩ := exists_simultaneous_abs_mul_sub_round_lt
      (fun j : Fin 5 => (v (m.succAbove j) : ℝ) / (v m : ℝ)) (n := 21) (by norm_num)
  obtain ⟨t, ht⟩ : ∃ t : ℝ, t = (q : ℝ) / (v m : ℝ) := ⟨_, rfl⟩
  obtain ⟨w, hw⟩ : ∃ w : Fin 6 → ℤ, w = fun k => round (t * (v k : ℝ)) := ⟨_, rfl⟩
  have htm : t * (v m : ℝ) = (q : ℝ) := by rw [ht]; field_simp
  have hwk : ∀ k, w k = round (t * (v k : ℝ)) := fun k => by rw [hw]
  have hwm : w m = q := by rw [hwk, htm]; exact round_intCast q
  have hbound : ∀ k, |(w k : ℝ) - t * v k| < 1 / 21 := by
    intro k
    by_cases hk : k = m
    · subst hk; rw [hwm, htm]; simp
    · obtain ⟨j, hj⟩ := Fin.exists_succAbove_eq hk
      have h1 := hq j
      have h2 : (v (m.succAbove j) : ℝ) / (v m : ℝ) * (q : ℝ) = t * (v k : ℝ) := by
        rw [hj, ht]; ring
      simp only at h1
      rw [h2] at h1
      rw [hwk k, abs_sub_comm]
      calc |t * (v k : ℝ) - ((round (t * (v k : ℝ)) : ℤ) : ℝ)| < 1 / ((21 : ℕ) : ℝ) := h1
        _ = 1 / 21 := by norm_num
  obtain ⟨k0, -, hk0⟩ := Finset.exists_max_image (Finset.univ : Finset (Fin 6))
    (fun k => |(w k : ℝ) - t * v k|) ⟨0, Finset.mem_univ _⟩
  have hδ : |(w k0 : ℝ) - t * v k0| < 1 / 21 := hbound k0
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
      norm_num at hq1 hlt
      omega
    · rw [h] at hva
      omega
  have hfin := two_dir h5 v w (fun k => (hpos k).ne') t _ he hnp
  linarith

/-- Entry-wise height bound at the YGB threshold `1/7` (`n = 6`), from `LRC 5` alone. -/
def HeightBound21 : Prop :=
  ∀ v : Fin 6 → ℤ, (∀ i, 0 < v i) → Primitive v → ML v ≤ 1 / 7 → ∀ i, v i ≤ 21 ^ 5

theorem heightBound21_of_LRC5 (h5 : LRC 5) : HeightBound21 :=
  fun v hpos hprim hML i => T2_entry h5 v hpos hprim hML i

/-- The older entry bound `< 17,010,000` of `Statement.HeightBound`, from `LRC 5` alone (no YGB, no `LRC 4`). -/
theorem heightBound_of_LRC5 (h5 : LRC 5) : HeightBound := by
  intro v hpos hprim hML i
  have h := T2_entry h5 v hpos hprim hML i
  have h21 : (21 : ℤ) ^ 5 = 4084101 := by norm_num
  rw [h21] at h
  omega

/-- Theorem A from a box covering the height bound `21^5`. -/
theorem TheoremA_of_box21 (B : ℕ) (hB : 4084101 ≤ B) (hbox : TheoremBox B) :
    HeightBound21 → TheoremA := by
  intro hH v hinj hpos hML
  obtain ⟨g, v', hg, hv, hpos', hinj', hprim'⟩ := gcd_reduce v hinj hpos
  have hML' := ML_reduce g hg v v' hv hML
  have hbd := hH v' hpos' hprim' hML'
  have h21 : (21 : ℤ) ^ 5 = 4084101 := by norm_num
  obtain ⟨c, σ, hc, hσ⟩ := hbox v' hinj' hpos' (fun i => by
    have := hbd i
    rw [h21] at this
    omega) hML'
  exact ⟨g * c, σ, mul_pos hg hc, fun i => by rw [hv i, hσ i]; ring⟩

def P15 : List ℕ := cleanPrimes150.take 15

theorem betaOf_P16_T2 : betaOf P16 4084101 = 2 := by decide +kernel
theorem betaOf_P16_11T2 : betaOf P16 (11 * 4084101) = 3 := by decide +kernel
/-- the arithmetic of the pair-route count at `B = 21^5`: 16 primes suffice. -/
theorem count_P16_T2 : 6 * betaOf P16 4084101 + betaOf P16 (11 * 4084101) + 1 ≤ P16.length := by
  decide +kernel
/-- and 15 do not: the pair route needs 16 primes at `B = 21^5` (`6*2 + 3 + 1 = 16`). -/
theorem count_P15_T2_fails :
    P15.length < 6 * betaOf P15 4084101 + betaOf P15 (11 * 4084101) + 1 := by decide +kernel

theorem TheoremBox_P16_T2 (h : ResidueDataSub P16) : TheoremBox 4084101 :=
  TheoremBoxPair P16 (pairData_P16 h) 4084101 (by norm_num) count_P16_T2

/-- **Theorem A from `LRC 5` and the 16 smallest clean primes.**  Only hypotheses: `LRC 5` (proved in this
development as `Sext6.LRC5`) and `ResidueDataSub P16` (a hypothesis here; discharged in `K313.Discharge16`). -/
theorem TheoremA16_LRC5 : LRC 5 → ResidueDataSub P16 → TheoremA :=
  fun h5 hres => TheoremA_of_box21 4084101 le_rfl (TheoremBox_P16_T2 hres) (heightBound21_of_LRC5 h5)

end Sext6
end LRSpectrumFull

#print axioms LRSpectrumFull.Sext6.T2_entry
#print axioms LRSpectrumFull.Sext6.heightBound21_of_LRC5
#print axioms LRSpectrumFull.Sext6.heightBound_of_LRC5
#print axioms LRSpectrumFull.Sext6.TheoremA_of_box21
#print axioms LRSpectrumFull.Sext6.count_P16_T2
#print axioms LRSpectrumFull.Sext6.count_P15_T2_fails
#print axioms LRSpectrumFull.Sext6.TheoremA16_LRC5
