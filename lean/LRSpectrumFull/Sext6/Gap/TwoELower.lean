import LRSpectrumFull.Sext6.Gap.MultiLower

/-!
# Two-entry sandwich, part 1: arc values and the lower bounds  [2026-11-25]

Setting: `N`, two removed entries `r1, r2 ∈ (N/2, N]`, two inserted speeds `w1, w2`.
`Within2` : every speed of `v` is a retained speed `x ∈ [1,N] \ {r1,r2}` or one of `w1, w2`.

Arc values (the finite one-variable problem of the notes, without a candidate list): for an entry `r`,
an integer `c`, a block `X ∈ [N+1-r, N]` with `r ∣ c X + 1` (the largest element of `[1,N]` in the class
`-c⁻¹ mod r`) and an offset `η ∈ [0, 1/(N+1)]`,
  `arcVal r w1 w2 c X η = min (tent, saw1, saw2)`,
  `tent = (1 - X η)/r`, `saw_j = ‖w_j (c + η)/r‖`.
`ArcSet` is the set of all such values over `r ∈ {r1, r2}`, `c` coprime to `r`.

* `arcVal_le_ML`    : every arc value is `≤ ML v` (no gcd hypothesis; only `Within2`).
* `ML_ge_floor2`    : `1/(N+1) ≤ ML v` when `N+1` divides neither `w1` nor `w2`.
No `sorry`, no `axiom`.

Convention: `N` is the size of the ambient interval `[1,N]`; the speed vector `v : Fin (k+1) → ℤ` is a finite family (repetitions allowed). Speeds are the moving runners; the runner at rest is not counted, so a vector of `N` speeds means `N + 1` runners and the Lonely Runner value is `1/(N+1)`.
Axiom audit: covered by `Axioms23`.
-/

namespace LRSpectrumFull
namespace Sext6
namespace Gap

/-- `X` is the block representative: `X ∈ [N+1-r, N]` and `r ∣ c X + 1`. -/
def IsBlock (N r : ℕ) (c X : ℤ) : Prop :=
  (N : ℤ) + 1 - r ≤ X ∧ X ≤ N ∧ (r : ℤ) ∣ c * X + 1

/-- `min (tent, saw1, saw2)` at the time `(c + η)/r`. -/
noncomputable def arcVal (r w1 w2 : ℕ) (c X : ℤ) (η : ℝ) : ℝ :=
  min ((1 - (X : ℝ) * η) / r)
    (min (nearestIntDist ((w1 : ℝ) * (((c : ℝ) + η) / r)))
         (nearestIntDist ((w2 : ℝ) * (((c : ℝ) + η) / r))))

/-- All arc values of the two-entry set. -/
def ArcSet (N r1 r2 w1 w2 : ℕ) : Set ℝ :=
  {y | ∃ r : ℕ, (r = r1 ∨ r = r2) ∧ ∃ (c X : ℤ) (η : ℝ), IsCoprime c (r : ℤ) ∧ IsBlock N r c X ∧
      0 ≤ η ∧ η ≤ 1 / ((N : ℝ) + 1) ∧ y = arcVal r w1 w2 c X η}

/-- Every speed of `v` is a retained speed or one of the two inserted speeds. -/
def Within2 {k : ℕ} (N r1 r2 w1 w2 : ℕ) (v : Fin (k + 1) → ℤ) : Prop :=
  ∀ i, (∃ x : ℕ, 1 ≤ x ∧ x ≤ N ∧ x ≠ r1 ∧ x ≠ r2 ∧ v i = (x : ℤ)) ∨ v i = (w1 : ℤ) ∨ v i = (w2 : ℤ)

theorem far_shift (ξ : ℝ) (hξ0 : 0 ≤ ξ) (hξ1 : ξ < 1) (z : ℤ) (hz : z ≠ 0) :
    1 - ξ ≤ |(z : ℝ) + ξ| := by
  have h : 1 ≤ z ∨ z = -1 ∨ z ≤ -2 := by omega
  rcases h with h | h | h
  · have h' : (1 : ℝ) ≤ z := by exact_mod_cast h
    rw [abs_of_nonneg (by linarith)]
    linarith
  · subst h
    push_cast
    rw [abs_of_nonpos (by linarith)]
    linarith
  · have h' : (z : ℝ) ≤ -2 := by exact_mod_cast h
    rw [abs_of_nonpos (by linarith)]
    linarith

theorem far_shift2 (ξ : ℝ) (hξ0 : 0 ≤ ξ) (hξ1 : ξ < 1) (z : ℤ) (hz : z ≠ 0) (hz' : z ≠ -1) :
    1 ≤ |(z : ℝ) + ξ| := by
  have h : 1 ≤ z ∨ z ≤ -2 := by omega
  rcases h with h | h
  · have h' : (1 : ℝ) ≤ z := by exact_mod_cast h
    rw [abs_of_nonneg (by linarith)]
    linarith
  · have h' : (z : ℝ) ≤ -2 := by exact_mod_cast h
    rw [abs_of_nonpos (by linarith)]
    linarith

theorem sub_int_eq {r : ℕ} (hr : 2 ≤ r) (c : ℤ) (x : ℕ) (η t : ℝ)
    (ht : (r : ℝ) * t = c + η) (n : ℤ) :
    (x : ℝ) * t - n = ((((x : ℤ) * c - n * r : ℤ) : ℝ) + (x : ℝ) * η) / r := by
  have hr0 : (r : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  rw [eq_div_iff hr0]
  push_cast
  linear_combination (x : ℝ) * ht

theorem xeta_lt_one {N : ℕ} {x η : ℝ} (hx0 : 0 ≤ x) (hx : x ≤ N) (hη0 : 0 ≤ η)
    (hη1 : η ≤ 1 / ((N : ℝ) + 1)) : x * η < 1 := by
  have hNR : (0 : ℝ) < (N : ℝ) + 1 := by positivity
  have hη2 : η * ((N : ℝ) + 1) ≤ 1 := (le_div_iff₀ hNR).mp hη1
  rcases hη0.eq_or_lt with h | h
  · rw [← h]; norm_num
  · have h3 := mul_le_mul_of_nonneg_right hx hη0
    nlinarith

theorem nid_class_A {r : ℕ} (hr : 2 ≤ r) (c : ℤ) (x : ℕ) (η t : ℝ)
    (ht : (r : ℝ) * t = c + η) (hξ0 : 0 ≤ (x : ℝ) * η) (hξ1 : (x : ℝ) * η < 1)
    (hd : (r : ℤ) ∣ (x : ℤ) * c + 1) :
    (1 - (x : ℝ) * η) / r ≤ nearestIntDist ((x : ℝ) * t) := by
  have hrpos : (0 : ℝ) < r := by exact_mod_cast (by omega : 0 < r)
  apply nid_ge_of_int
  intro n
  rw [sub_int_eq hr c x η t ht n, abs_div, abs_of_pos hrpos]
  refine div_le_div_of_nonneg_right ?_ hrpos.le
  apply far_shift _ hξ0 hξ1
  intro hz
  have h1 : (r : ℤ) ∣ (x : ℤ) * c - n * r + 1 := by
    have e : (x : ℤ) * c - n * r + 1 = ((x : ℤ) * c + 1) - r * n := by ring
    rw [e]
    exact dvd_sub hd (dvd_mul_right _ _)
  have e1 : (x : ℤ) * c - n * r + 1 = 1 := by rw [hz]; norm_num
  rw [e1] at h1
  have h3 := Int.le_of_dvd (by norm_num) h1
  omega

theorem nid_class_B {r : ℕ} (hr : 2 ≤ r) (c : ℤ) (x : ℕ) (η t : ℝ)
    (ht : (r : ℝ) * t = c + η) (hξ0 : 0 ≤ (x : ℝ) * η) (hξ1 : (x : ℝ) * η < 1)
    (hd0 : ¬ (r : ℤ) ∣ (x : ℤ) * c) (hd1 : ¬ (r : ℤ) ∣ (x : ℤ) * c + 1) :
    1 / (r : ℝ) ≤ nearestIntDist ((x : ℝ) * t) := by
  have hrpos : (0 : ℝ) < r := by exact_mod_cast (by omega : 0 < r)
  apply nid_ge_of_int
  intro n
  rw [sub_int_eq hr c x η t ht n, abs_div, abs_of_pos hrpos]
  refine div_le_div_of_nonneg_right ?_ hrpos.le
  apply far_shift2 _ hξ0 hξ1
  · intro hz
    apply hd0
    have e : (x : ℤ) * c = n * r := by linarith
    rw [e]
    exact dvd_mul_left _ _
  · intro hz
    apply hd1
    have e : (x : ℤ) * c + 1 = n * r := by linarith
    rw [e]
    exact dvd_mul_left _ _

/-- Lower bound: every arc value is at most `ML v`. Needs `Within2` only. -/
theorem arcVal_le_ML {k N r1 r2 w1 w2 : ℕ} (hN : 2 ≤ N)
    (h1 : N < 2 * r1) (h1' : r1 ≤ N) (h2 : N < 2 * r2) (h2' : r2 ≤ N)
    (v : Fin (k + 1) → ℤ) (hw : Within2 N r1 r2 w1 w2 v)
    {y : ℝ} (hy : y ∈ ArcSet N r1 r2 w1 w2) : y ≤ ML v := by
  obtain ⟨r, hr, c, X, η, hcop, hblk, hη0, hη1, rfl⟩ := hy
  unfold IsBlock at hblk
  obtain ⟨hX1, hX2, hXd⟩ := hblk
  have hrN : r ≤ N := by rcases hr with h | h <;> omega
  have hrlt : N < 2 * r := by rcases hr with h | h <;> omega
  have hrr : 2 ≤ r := by omega
  have hrpos : (0 : ℝ) < r := by exact_mod_cast (by omega : 0 < r)
  have hr0 : (r : ℝ) ≠ 0 := hrpos.ne'
  have ht : (r : ℝ) * (((c : ℝ) + η) / r) = c + η := by field_simp
  have hX0 : (0 : ℝ) ≤ X := by exact_mod_cast (by omega : (0 : ℤ) ≤ X)
  apply ML_ge_of_far v _ (((c : ℝ) + η) / r)
  intro i
  rcases hw i with ⟨x, hx1, hxN, hxr1, hxr2, hvx⟩ | hv | hv
  · have hxr : x ≠ r := by rcases hr with h | h <;> omega
    have e : ((v i : ℤ) : ℝ) = (x : ℝ) := by rw [hvx]; norm_cast
    rw [e]
    have hxR : (x : ℝ) ≤ N := by exact_mod_cast hxN
    have hξ1 : (x : ℝ) * η < 1 := xeta_lt_one (by positivity) hxR hη0 hη1
    have hξ0 : 0 ≤ (x : ℝ) * η := by positivity
    by_cases hd1 : (r : ℤ) ∣ (x : ℤ) * c + 1
    · have hdx : (r : ℤ) ∣ (x : ℤ) - X := by
        have h3 : (r : ℤ) ∣ c * ((x : ℤ) - X) := by
          have h4 := dvd_sub hd1 hXd
          have e2 : (x : ℤ) * c + 1 - (c * X + 1) = c * ((x : ℤ) - X) := by ring
          rwa [e2] at h4
        exact hcop.symm.dvd_of_dvd_mul_left h3
      have hxX : (x : ℤ) ≤ X := by
        by_contra hlt
        push Not at hlt
        have h5 := Int.le_of_dvd (by omega) hdx
        omega
      have hxX' : (x : ℝ) ≤ X := by exact_mod_cast hxX
      have hA := nid_class_A hrr c x η (((c : ℝ) + η) / r) ht hξ0 hξ1 hd1
      have hB : (1 - (X : ℝ) * η) / r ≤ (1 - (x : ℝ) * η) / r := by
        refine div_le_div_of_nonneg_right ?_ hrpos.le
        have := mul_le_mul_of_nonneg_right hxX' hη0
        linarith
      unfold arcVal
      exact (min_le_left _ _).trans (hB.trans hA)
    · by_cases hd0 : (r : ℤ) ∣ (x : ℤ) * c
      · exfalso
        have hdx : (r : ℤ) ∣ (x : ℤ) := hcop.symm.dvd_of_dvd_mul_right hd0
        obtain ⟨q, hq⟩ := hdx
        have hr0' : (0 : ℤ) < r := by omega
        have hx1' : (1 : ℤ) ≤ x := by exact_mod_cast hx1
        have hxN' : (x : ℤ) ≤ N := by exact_mod_cast hxN
        have hrlt' : (N : ℤ) < 2 * r := by exact_mod_cast hrlt
        have hq1 : 1 ≤ q := by
          by_contra hq0
          push Not at hq0
          have h6 : (r : ℤ) * q ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hr0'.le (by omega)
          linarith
        have hq2 : q ≤ 1 := by
          by_contra hq0
          push Not at hq0
          have h6 : (r : ℤ) * 2 ≤ r * q := mul_le_mul_of_nonneg_left (by omega) hr0'.le
          linarith
        have hq3 : q = 1 := by omega
        rw [hq3] at hq
        exact hxr (by omega)
      · have hB := nid_class_B hrr c x η (((c : ℝ) + η) / r) ht hξ0 hξ1 hd0 hd1
        have hC : (1 - (X : ℝ) * η) / r ≤ 1 / (r : ℝ) := by
          refine div_le_div_of_nonneg_right ?_ hrpos.le
          have := mul_nonneg hX0 hη0
          linarith
        unfold arcVal
        exact (min_le_left _ _).trans (hC.trans hB)
  · have e : ((v i : ℤ) : ℝ) = (w1 : ℝ) := by rw [hv]; norm_cast
    rw [e]
    unfold arcVal
    exact (min_le_right _ _).trans (min_le_left _ _)
  · have e : ((v i : ℤ) : ℝ) = (w2 : ℝ) := by rw [hv]; norm_cast
    rw [e]
    unfold arcVal
    exact (min_le_right _ _).trans (min_le_right _ _)

/-- The floor: `N+1` dividing neither inserted speed gives `ML v ≥ 1/(N+1)` (time `1/(N+1)`). -/
theorem ML_ge_floor2 {k N r1 r2 w1 w2 : ℕ} (hN : 1 ≤ N)
    (v : Fin (k + 1) → ℤ) (hw : Within2 N r1 r2 w1 w2 v)
    (hd1 : ¬ (((N + 1 : ℕ) : ℤ) ∣ ((w1 : ℕ) : ℤ)))
    (hd2 : ¬ (((N + 1 : ℕ) : ℤ) ∣ ((w2 : ℕ) : ℤ))) :
    1 / ((N : ℝ) + 1) ≤ ML v := by
  have hpos : 0 < N + 1 := by omega
  have hc : 1 / ((N : ℝ) + 1) = ((1 : ℕ) : ℝ) / ((N + 1 : ℕ) : ℝ) := by push_cast; ring
  rw [hc]
  apply ML_ge_of_far v _ (((1 : ℤ) : ℝ) / ((N + 1 : ℕ) : ℝ))
  intro i
  rcases hw i with ⟨x, hx1, hxN, -, -, hvx⟩ | hv | hv
  · have e : ((v i : ℤ) : ℝ) * (((1 : ℤ) : ℝ) / ((N + 1 : ℕ) : ℝ)) =
        ((((x : ℤ)) : ℤ) : ℝ) / ((N + 1 : ℕ) : ℝ) := by
      rw [hvx]; push_cast; ring
    rw [e]
    apply nid_div_ge hpos
    apply far_of_not_dvd
    intro hd
    have h4 := Int.le_of_dvd (by exact_mod_cast hx1) hd
    have h3 : (x : ℤ) ≤ N := by exact_mod_cast hxN
    push_cast at h4
    omega
  · have e : ((v i : ℤ) : ℝ) * (((1 : ℤ) : ℝ) / ((N + 1 : ℕ) : ℝ)) =
        ((((w1 : ℕ) : ℤ) : ℤ) : ℝ) / ((N + 1 : ℕ) : ℝ) := by
      rw [hv]; push_cast; ring
    rw [e]
    apply nid_div_ge hpos
    apply far_of_not_dvd
    exact hd1
  · have e : ((v i : ℤ) : ℝ) * (((1 : ℤ) : ℝ) / ((N + 1 : ℕ) : ℝ)) =
        ((((w2 : ℕ) : ℤ) : ℤ) : ℝ) / ((N + 1 : ℕ) : ℝ) := by
      rw [hv]; push_cast; ring
    rw [e]
    apply nid_div_ge hpos
    apply far_of_not_dvd
    exact hd2

end Gap
end Sext6
end LRSpectrumFull
