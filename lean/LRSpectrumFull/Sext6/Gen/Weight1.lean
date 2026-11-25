/-
# Gen/Weight1: proof of the weight-1 lemma  

* `coset_far`   : for `q >= 2`, `gcd c q = 1`, any real `s0`, some integer `n` has
                  `(q-1)/(2q) <= ||c (s0+n)/q||`  (a coset of `(1/q)Z` meets a closed arc of length `1/q`).
* `weight1_main`: the lemma, `min (1/(k+1)) ((q-1)/(2q)) <= ML v`.
* `weight1_holds : Weight1Statement`,  `weight1_gt`: strict form `tau < 1/(k+1)`, `tau < (q-1)/(2q)` gives `tau < ML v`.
Numerics for the tower: N=7 tau=1/8 and q in {2,3,5}: 1/8 < (q-1)/(2q) holds; N=6 tau=5/33 and tau=1/7 likewise.
Needs only `Sext6.LRC k` (k = N-1).
-/
import LRSpectrumFull.Sext6.Gen.Weight1Stmt

namespace LRSpectrumFull
namespace Sext6

theorem coset_far (q : ℕ) (hq : 2 ≤ q) (c : ℤ) (hc : IsCoprime c (q : ℤ)) (s0 : ℝ) :
    ∃ n : ℤ, ((q : ℝ) - 1) / (2 * (q : ℝ)) ≤
      nearestIntDist ((c : ℝ) * ((s0 + (n : ℝ)) / (q : ℝ))) := by
  have hqr : (2 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq
  have hq0 : (0 : ℝ) < (q : ℝ) := by linarith
  obtain ⟨u, w, huw⟩ := hc
  have huwR : (u : ℝ) * c + w * q = 1 := by exact_mod_cast huw
  have hiq : (q : ℝ) * (q : ℝ)⁻¹ = 1 := mul_inv_cancel₀ hq0.ne'
  obtain ⟨x, hx⟩ : ∃ x : ℝ, x = s0 * c / q := ⟨_, rfl⟩
  obtain ⟨y, hy⟩ : ∃ y : ℝ, y = ((q : ℝ) - 1) / 2 - q * x := ⟨_, rfl⟩
  obtain ⟨r, hr⟩ : ∃ r : ℤ, r = ⌈y⌉ := ⟨_, rfl⟩
  have hr1 : y ≤ (r : ℝ) := by rw [hr]; exact Int.le_ceil y
  have hr2 : (r : ℝ) < y + 1 := by rw [hr]; exact Int.ceil_lt_add_one y
  refine ⟨r * u, ?_⟩
  have hid : (c : ℝ) * ((s0 + ((r * u : ℤ) : ℝ)) / q) = (x + (r : ℝ) / q) + ((-(r * w) : ℤ) : ℝ) := by
    rw [hx]
    push_cast
    linear_combination ((r : ℝ) * (q : ℝ)⁻¹) * huwR - ((r : ℝ) * w) * hiq
  rw [hid, nearestIntDist_add_int]
  obtain ⟨z, hz⟩ : ∃ z : ℝ, z = x + (r : ℝ) / q := ⟨_, rfl⟩
  rw [← hz]
  have hqz : (q : ℝ) * z = q * x + r := by
    rw [hz]; linear_combination (r : ℝ) * hiq
  have hz1 : ((q : ℝ) - 1) / 2 ≤ (q : ℝ) * z := by rw [hqz]; linarith
  have hz2 : (q : ℝ) * z < ((q : ℝ) + 1) / 2 := by rw [hqz]; linarith
  have h2q : (0 : ℝ) < 2 * (q : ℝ) := by linarith
  have hzB : ((q : ℝ) - 1) / (2 * (q : ℝ)) ≤ z := by
    rw [div_le_iff₀ h2q]; linarith
  have hB0 : (0 : ℝ) ≤ ((q : ℝ) - 1) / (2 * (q : ℝ)) := div_nonneg (by linarith) h2q.le
  have hz0 : 0 ≤ z := le_trans hB0 hzB
  have hzlt : z < 1 := by
    by_contra h
    push_neg at h
    have := mul_nonneg hq0.le (sub_nonneg.2 h)
    linarith
  unfold nearestIntDist
  rw [Int.fract_eq_self.2 ⟨hz0, hzlt⟩]
  refine le_min hzB ?_
  rw [div_le_iff₀ h2q]
  linarith

theorem weight1_main (k q : ℕ) (hk : 1 ≤ k) (hq : 2 ≤ q) (hL : Sext6.LRC k)
    (v : Fin (k + 1) → ℤ) (hinj : Function.Injective v) (hpos : ∀ i, 0 < v i)
    (e : Fin (k + 1)) (hmul : ∀ i, i ≠ e → (q : ℤ) ∣ v i) (hcop : IsCoprime (v e) (q : ℤ)) :
    min ((1 : ℝ) / ((k : ℝ) + 1)) (((q : ℝ) - 1) / (2 * (q : ℝ))) ≤ ML v := by
  obtain ⟨j0, rfl⟩ : ∃ j0, k = j0 + 1 := ⟨k - 1, by omega⟩
  have hq0 : (0 : ℤ) < (q : ℤ) := by exact_mod_cast (by omega : 0 < q)
  have hqR0 : (0 : ℝ) < (q : ℝ) := by exact_mod_cast (by omega : 0 < q)
  have hiq : (q : ℝ) * (q : ℝ)⁻¹ = 1 := mul_inv_cancel₀ hqR0.ne'
  have hex : ∀ j : Fin (j0 + 1), ∃ c : ℤ, v (e.succAbove j) = (q : ℤ) * c :=
    fun j => hmul _ (Fin.succAbove_ne e j)
  choose a ha using hex
  have hapos : ∀ j, 0 < a j := fun j => by
    have h := hpos (e.succAbove j)
    rw [ha j] at h
    by_contra hle
    push_neg at hle
    nlinarith
  have hainj : Function.Injective a := fun j j' h => by
    have : v (e.succAbove j) = v (e.succAbove j') := by rw [ha j, ha j', h]
    exact Fin.succAbove_right_injective (hinj this)
  have hLa := hL j0 rfl a hainj hapos
  have hcore : ∀ s0 : ℝ, min (gap a s0) (((q : ℝ) - 1) / (2 * (q : ℝ))) ≤ ML v := by
    intro s0
    obtain ⟨n, hn⟩ := coset_far q hq (v e) hcop s0
    have key : ∀ i, min (gap a s0) (((q : ℝ) - 1) / (2 * (q : ℝ))) ≤
        nearestIntDist ((v i : ℝ) * ((s0 + (n : ℝ)) / (q : ℝ))) := by
      intro i
      by_cases hi : i = e
      · rw [hi]
        exact (min_le_right _ _).trans hn
      · obtain ⟨j, hj⟩ := Fin.exists_succAbove_eq hi
        have h1 := gap_le a s0 j
        have hrep : (v i : ℝ) * ((s0 + (n : ℝ)) / (q : ℝ)) = (a j : ℝ) * s0 + ((a j * n : ℤ) : ℝ) := by
          rw [← hj, ha j]
          push_cast
          linear_combination ((a j : ℝ) * (s0 + n)) * hiq
        rw [hrep, nearestIntDist_add_int]
        exact (min_le_left _ _).trans h1
    have hge := le_gap v ((s0 + (n : ℝ)) / (q : ℝ)) _ key
    exact hge.trans (le_csSup (bddAbove_range_gap v) ⟨_, rfl⟩)
  by_contra hcon
  have hlt := not_le.1 hcon
  have h1 : ML v < sSup (Set.range (gap a)) :=
    lt_of_lt_of_le hlt ((min_le_left _ _).trans hLa)
  obtain ⟨_, ⟨s0, rfl⟩, hs0⟩ := exists_lt_of_lt_csSup (Set.range_nonempty _) h1
  have hB : ML v < ((q : ℝ) - 1) / (2 * (q : ℝ)) := lt_of_lt_of_le hlt (min_le_right _ _)
  have := hcore s0
  have := lt_min hs0 hB
  linarith

theorem weight1_holds : Weight1Statement :=
  fun k q hk hq hL v hinj hpos e hmul hcop => weight1_main k q hk hq hL v hinj hpos e hmul hcop

/-- Strict form used by the tower: `tau < 1/(k+1)` and `tau < (q-1)/(2q)` give `tau < ML v`. -/
theorem weight1_gt (k q : ℕ) (hk : 1 ≤ k) (hq : 2 ≤ q) (hL : Sext6.LRC k)
    (v : Fin (k + 1) → ℤ) (hinj : Function.Injective v) (hpos : ∀ i, 0 < v i)
    (e : Fin (k + 1)) (hmul : ∀ i, i ≠ e → (q : ℤ) ∣ v i) (hcop : IsCoprime (v e) (q : ℤ))
    (τ : ℝ) (h1 : τ < 1 / ((k : ℝ) + 1)) (h2 : τ < ((q : ℝ) - 1) / (2 * (q : ℝ))) : τ < ML v :=
  lt_of_lt_of_le (lt_min h1 h2) (weight1_main k q hk hq hL v hinj hpos e hmul hcop)

end Sext6
end LRSpectrumFull

#print axioms LRSpectrumFull.Sext6.coset_far
#print axioms LRSpectrumFull.Sext6.weight1_main
#print axioms LRSpectrumFull.Sext6.weight1_holds
#print axioms LRSpectrumFull.Sext6.weight1_gt
