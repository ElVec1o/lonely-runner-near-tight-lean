import LRSpectrumFull.Sext6.Gap.UpperTrap

/-!
# Multi-entry value theorem, upper-bound core  [2026-11-24]

Generalises `UpperCore` (steps U3-U6 of the accompanying notes on Theorem V section 3) from `[N] \ {r}` to `[N] \ R`,
where `R` is a finite set of removed entries, each `> N/2`, pairwise non-coprime (hypothesis `hG`).
Only two places change: the reduced multiple `r/g ≤ N/2` is retained because every element of `R` exceeds `N/2`;
the blocker is a unit mod `r`, hence never an element `r' ≠ r` of `R` (`hG`).
No `sorry`, no `axiom`.

Convention: `N` is the size of the ambient interval `[1,N]`; the speed vector `v : Fin (k+1) → ℤ` is a finite family (repetitions allowed) and `k`, `N` are independent parameters of the generic statements. Speeds are the moving runners; the runner at rest is not counted, so a vector of `N` speeds means `N + 1` runners and the Lonely Runner value is `1/(N+1)`.
Hypotheses: those of the individual statements (numerical bounds, structural conditions and, where named in the list above, window predicates such as `PrimeWin`, `CopWin`, `PrimeWindow7`, which later modules discharge for explicit ranges). The unproved predicates `DusartPi`, `LRCHyp`, `CopWinHyp` are not hypotheses of any statement in this module.
Axiom audit: covered by `MultiAxioms` (also reached through the imports of `Axioms8`) (`#print axioms`; declarations not printed there are bricks of printed ones, so their axioms are bounded by the printed lines).
-/

namespace LRSpectrumFull
namespace Sext6
namespace Gap

/-- U3 (multi): `c` is a unit modulo `r`. -/
theorem munit_of_trap {N r m β : ℕ} (R : Finset ℕ) (hRlt : ∀ r' ∈ R, N < 2 * r')
    (hS : Spec N r m β) (τ : ℝ)
    (hτ1 : 1 / ((N : ℝ) + 1) ≤ τ) (t : ℝ) (c : ℤ) (η : ℝ)
    (hrt : (r : ℝ) * t = c + η) (hη0 : 0 ≤ η) (hη1 : η ≤ 1 / ((N : ℝ) + 1))
    (hx : ∀ x : ℕ, 1 ≤ x → x ≤ N → x ∉ R → τ < nearestIntDist ((x : ℝ) * t)) :
    IsCoprime c (r : ℤ) := by
  have hr2 := hS.hr2
  have hrr := hS.two_le_r
  rw [Int.isCoprime_iff_gcd_eq_one]
  by_contra hg
  have hd1 : ((Int.gcd c (r : ℤ) : ℕ) : ℤ) ∣ (r : ℤ) := Int.gcd_dvd_right c r
  have hd2 : ((Int.gcd c (r : ℤ) : ℕ) : ℤ) ∣ c := Int.gcd_dvd_left c r
  generalize Int.gcd c (r : ℤ) = g at hg hd1 hd2
  obtain ⟨y, hy⟩ := hd1
  obtain ⟨c', hc'⟩ := hd2
  have hg0 : 0 < g := by
    rcases Nat.eq_zero_or_pos g with h0 | h0
    · rw [h0] at hy
      simp at hy
      omega
    · exact h0
  have hg2 : 2 ≤ g := by omega
  have hg2' : (2 : ℤ) ≤ g := by exact_mod_cast hg2
  have hrz : (2 : ℤ) ≤ r := by exact_mod_cast hrr
  have hy1 : 1 ≤ y := by
    by_contra hyc
    have h0 : y ≤ 0 := by omega
    have : (g : ℤ) * y ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (by positivity) h0
    linarith
  have h2y : 2 * y ≤ (r : ℤ) := by
    have : 2 * y ≤ (g : ℤ) * y := mul_le_mul_of_nonneg_right hg2' (by omega)
    linarith
  have hy2 : y < r := by omega
  have hyr : (y : ℤ) < r := hy2
  obtain ⟨xn, hxn⟩ : ∃ xn : ℕ, (xn : ℤ) = y := ⟨y.toNat, Int.toNat_of_nonneg (by omega)⟩
  have hxnR : (xn : ℝ) = (y : ℝ) := by exact_mod_cast hxn
  have hnotR : xn ∉ R := by
    intro hmem
    have h3 := hRlt xn hmem
    omega
  have hrR : (r : ℝ) = (g : ℝ) * (y : ℝ) := by
    have := congrArg (fun z : ℤ => (z : ℝ)) hy
    push_cast at this
    exact this
  have hcR : (c : ℝ) = (g : ℝ) * (c' : ℝ) := by
    have := congrArg (fun z : ℤ => (z : ℝ)) hc'
    push_cast at this
    exact this
  have hgR : (2 : ℝ) ≤ g := by exact_mod_cast hg2
  have hw : (g : ℝ) * ((y : ℝ) * t - c') = η := by
    have := hrt
    rw [hrR, hcR] at this
    linarith
  have hw0 : 0 ≤ (y : ℝ) * t - c' := by
    by_contra hcon
    have : (g : ℝ) * ((y : ℝ) * t - c') < 0 :=
      mul_neg_of_pos_of_neg (by linarith) (not_le.mp hcon)
    linarith
  have hw1 : (y : ℝ) * t - c' ≤ η := by
    have : 0 ≤ ((g : ℝ) - 1) * ((y : ℝ) * t - c') := mul_nonneg (by linarith) hw0
    nlinarith
  have h1 := hx xn (by omega) (by omega) hnotR
  rw [hxnR] at h1
  have h2 := nearestIntDist_le_dist ((y : ℝ) * t) c'
  rw [abs_of_nonneg hw0] at h2
  linarith

/-- Lemma 4 core (multi): U3-U6 for `[N] \ R` with new speeds `m r' r'`. -/
theorem mcore_false {N r m β : ℕ} (R : Finset ℕ) (hRlt : ∀ r' ∈ R, N < 2 * r')
    (hG : ∀ r' ∈ R, r' ≠ r → ¬ Nat.Coprime r' r)
    (hS : Spec N r m β) (τ : ℝ)
    (hτ1 : 1 / ((N : ℝ) + 1) ≤ τ) (hτ2 : (m : ℝ) / ((m * r + β : ℕ) : ℝ) ≤ τ)
    (t : ℝ) (c : ℤ) (η : ℝ) (hrt : (r : ℝ) * t = c + η) (hη0 : 0 ≤ η)
    (hη1 : η ≤ 1 / ((N : ℝ) + 1))
    (hx : ∀ x : ℕ, 1 ≤ x → x ≤ N → x ∉ R → τ < nearestIntDist ((x : ℝ) * t))
    (hm : τ < nearestIntDist (((m : ℝ) * r) * t)) : False := by
  have hN2 := hS.hN
  have hr2 := hS.hr2
  have hrr := hS.two_le_r
  have hr1 := hS.hr1
  have hb1 := hS.hb1
  have hbpos := hS.beta_pos
  have hNR : (0 : ℝ) < (N : ℝ) + 1 := by positivity
  have hη2 : η * ((N : ℝ) + 1) ≤ 1 := (le_div_iff₀ hNR).mp hη1
  have hcop := munit_of_trap R hRlt hS τ hτ1 t c η hrt hη0 hη1 hx
  obtain ⟨X, hX1, hX2, k, hk⟩ := exists_block r ((N : ℤ) + 1 - r) (by omega) c hcop
  have hXpos : (1 : ℤ) ≤ X := by
    have : (r : ℤ) ≤ N := by exact_mod_cast hr2
    omega
  obtain ⟨xn, hxn⟩ : ∃ xn : ℕ, (xn : ℤ) = X := ⟨X.toNat, Int.toNat_of_nonneg (by omega)⟩
  have hxnR : (xn : ℝ) = (X : ℝ) := by exact_mod_cast hxn
  have hxN : xn ≤ N := by omega
  have hxr : xn ≠ r := by
    intro hxr
    have hXr : X = r := by rw [← hxn, hxr]
    rw [hXr] at hk
    have hd : (r : ℤ) ∣ 1 := ⟨k - c, by linarith⟩
    have := Int.le_of_dvd (by norm_num) hd
    omega
  have hcopx : Nat.Coprime xn r := by
    have : IsCoprime X (r : ℤ) := ⟨-c, k, by linarith⟩
    rw [← hxn] at this
    exact Nat.isCoprime_iff_coprime.mp this
  have hxnRR : xn ∉ R := fun hmem => hG xn hmem hxr hcopx
  have hβx : β ≤ xn := hS.hb3 xn (by omega) hcopx
  have hβxR : (β : ℝ) ≤ (X : ℝ) := by rw [← hxnR]; exact_mod_cast hβx
  have hkR : (c : ℝ) * X + 1 = r * k := by exact_mod_cast hk
  have hw : (r : ℝ) * ((X : ℝ) * t - k) = X * η - 1 := by
    linear_combination (X : ℝ) * hrt + hkR
  have hXR : (X : ℝ) ≤ N := by rw [← hxnR]; exact_mod_cast hxN
  have hXη : (X : ℝ) * η ≤ 1 := by
    have h1 : (X : ℝ) * η ≤ N * η := mul_le_mul_of_nonneg_right hXR hη0
    nlinarith
  have hrpos : (0 : ℝ) < r := by exact_mod_cast (by omega : 0 < r)
  have hw0 : (X : ℝ) * t - k ≤ 0 := by
    by_contra hcon
    have := mul_pos hrpos (not_le.mp hcon)
    linarith
  have hxv := hx xn (by omega) hxN hxnRR
  rw [hxnR] at hxv
  have h1 : τ < -((X : ℝ) * t - k) := by
    have := lt_of_lt_of_le hxv (nearestIntDist_le_dist ((X : ℝ) * t) k)
    rwa [abs_of_nonpos hw0] at this
  have h2 : (r : ℝ) * τ < 1 - X * η := by
    have := mul_lt_mul_of_pos_left h1 hrpos
    linarith
  have hmR : (0 : ℝ) < m := by exact_mod_cast (by have := hS.hm; omega : 0 < m)
  have hDR : (0 : ℝ) < ((m * r + β : ℕ) : ℝ) := by
    have : 0 < m * r + β := by omega
    exact_mod_cast this
  have hstar : (m : ℝ) ≤ τ * ((m : ℝ) * r + β) := by
    have := (div_le_iff₀ hDR).mp hτ2
    push_cast at this
    exact this
  have hβη : (β : ℝ) * η ≤ X * η := mul_le_mul_of_nonneg_right hβxR hη0
  have h3 : (m : ℝ) * ((β : ℝ) * η) ≤ m * (X * η) := mul_le_mul_of_nonneg_left hβη hmR.le
  have h4 : (m : ℝ) * (X * η) < m * (1 - r * τ) := by
    apply mul_lt_mul_of_pos_left _ hmR
    linarith
  have hβR : (0 : ℝ) < β := by exact_mod_cast hbpos
  have h5 : (β : ℝ) * ((m : ℝ) * η) < (β : ℝ) * τ := by nlinarith
  have h6 : (m : ℝ) * η < τ := lt_of_mul_lt_mul_left h5 hβR.le
  have e : ((m : ℝ) * r) * t - ((m * c : ℤ) : ℝ) = m * η := by
    push_cast
    linear_combination (m : ℝ) * hrt
  have h7 := lt_of_lt_of_le hm (nearestIntDist_le_dist (((m : ℝ) * r) * t) (m * c))
  rw [e, abs_of_nonneg (by positivity)] at h7
  linarith

end Gap
end Sext6
end LRSpectrumFull
