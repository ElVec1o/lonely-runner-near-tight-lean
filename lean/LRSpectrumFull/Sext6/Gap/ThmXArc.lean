import LRSpectrumFull.Sext6.Gap.OneRArc
import LRSpectrumFull.Sext6.Gap.ThmXWit

/-!
# Theorem X, part 4: the upper bound `ML ≤ 2/(2N+1)` when `D0 > 2N - 2r`  [2026-11-25]

Source: the accompanying notes on Theorem X, Sections 1-2 (Lemma 1, Lemma 2, the forward direction), with the
review fix of the accompanying notes (Dirichlet with `1/(N+1)` and a strict uniform margin instead of compactness).

On an arc `r p = c + η`, `0 ≤ η ≤ 1/(N+1)`, where every retained speed is `≥ τ > 1/(N+1)` from an integer
(only the speeds `2r` and `X` of the tent are used: `τ ≤ 2η` and `τ ≤ (1 - Xη)/r`), the window element
`D = X + 2r` has `‖D p‖ ≤ |2η - (1 - Xη)/r|` (Lemma 2, the sum identity).  If moreover `‖D p‖ ≥ τ` then
`τ ≤ 2/(2N+1)` as soon as `2N < D0 + 2r`.  Hence `ML ≤ 2/(2N+1) < 1/N`, a margin that needs no compactness.
No `sorry`, no `axiom`.

Convention: `N` is the size of the ambient interval `[N]`.
Hypotheses: `DSpec N r D` (so `1 ≤ r`, `2 r ≤ N`, `3 ≤ N`, `D = D0`) and `2 N < D + 2 r`.
Axiom audit: covered by `Axioms24`.
-/

namespace LRSpectrumFull
namespace Sext6
namespace Gap

/-- **Lemma 1 + Lemma 2 on one arc** (`η ≥ 0`). -/
theorem arcV_pos {N r D : ℕ} (hS : DSpec N r D) (hDg : 2 * N < D + 2 * r) (τ p η : ℝ) (c : ℤ)
    (hτ : 1 / ((N : ℝ) + 1) < τ) (hrt : (r : ℝ) * p = c + η) (hη0 : 0 ≤ η)
    (hη1 : η ≤ 1 / ((N : ℝ) + 1))
    (hx : ∀ x : ℕ, 1 ≤ x → x ≤ N → x ≠ r → τ ≤ nearestIntDist ((x : ℝ) * p))
    (hw : ∀ w : ℕ, N + r + 1 ≤ w → w ≤ N + 2 * r → Nat.Coprime w r →
      τ ≤ nearestIntDist ((w : ℝ) * p)) :
    τ ≤ 2 / ((2 : ℝ) * N + 1) := by
  have hr := hS.hr
  have hN2 := hS.hN
  have hN3 := hS.hN3
  have hD1 := hS.hD1
  have hNR : (0 : ℝ) < (N : ℝ) + 1 := by positivity
  have hη2 : η * ((N : ℝ) + 1) ≤ 1 := (le_div_iff₀ hNR).mp hη1
  have hτpos : 0 < τ := lt_trans (by positivity) hτ
  have hcop := unit_of_arc hr (by omega) τ p η c hτ hrt hη0 hη1 hx
  obtain ⟨X, hX1, hX2, k, hk⟩ := exists_block r ((N : ℤ) + 1 - r) (by omega) c hcop
  obtain ⟨xn, hxn⟩ : ∃ xn : ℕ, (xn : ℤ) = X := ⟨X.toNat, Int.toNat_of_nonneg (by omega)⟩
  have hxN : xn ≤ N := by omega
  have hxr : xn ≠ r := by omega
  have hx1 : 1 ≤ xn := by omega
  have hcopx : Nat.Coprime xn r := by
    have : IsCoprime X (r : ℤ) := ⟨-c, k, by linarith⟩
    rw [← hxn] at this
    exact Nat.isCoprime_iff_coprime.mp this
  have hDle : D ≤ xn + 2 * r :=
    hS.hmin (xn + 2 * r) (by omega) ((Nat.coprime_add_mul_right_left xn r 2).mpr hcopx)
  have hxnR : (xn : ℝ) = (X : ℝ) := by exact_mod_cast hxn
  have hXR : (X : ℝ) ≤ N := by rw [← hxnR]; exact_mod_cast hxN
  -- the speed 2r
  have h2r := hx (2 * r) (by omega) hN2 (by omega)
  have h2r' := nearestIntDist_le_dist (((2 * r : ℕ) : ℝ) * p) (2 * c)
  have e2 : ((2 * r : ℕ) : ℝ) * p - ((2 * c : ℤ) : ℝ) = 2 * η := by
    push_cast
    linear_combination 2 * hrt
  rw [e2, abs_of_nonneg (by linarith)] at h2r'
  have hτη : τ ≤ 2 * η := le_trans h2r h2r'
  -- the speed X
  have hxv := hx xn hx1 hxN hxr
  rw [hxnR] at hxv
  have hkR : (c : ℝ) * X + 1 = r * k := by exact_mod_cast hk
  have hw' : (r : ℝ) * ((X : ℝ) * p - k) = X * η - 1 := by
    linear_combination (X : ℝ) * hrt + hkR
  have hXη : (X : ℝ) * η ≤ 1 := by
    have h1 : (X : ℝ) * η ≤ N * η := mul_le_mul_of_nonneg_right hXR hη0
    nlinarith
  have hrpos : (0 : ℝ) < r := by exact_mod_cast (by omega : 0 < r)
  have hw0 : (X : ℝ) * p - k ≤ 0 := by
    by_contra hcon
    have := mul_pos hrpos (not_le.mp hcon)
    linarith
  have h1 : τ ≤ -((X : ℝ) * p - k) := by
    have := le_trans hxv (nearestIntDist_le_dist ((X : ℝ) * p) k)
    rwa [abs_of_nonpos hw0] at this
  -- the window element D' = X + 2r (Lemma 2: the sum identity)
  have hDw := hw (xn + 2 * r) (by omega) (by omega)
    ((Nat.coprime_add_mul_right_left xn r 2).mpr hcopx)
  have hDw' := nearestIntDist_le_dist (((xn + 2 * r : ℕ) : ℝ) * p) (k + 2 * c)
  have eδ : ((xn + 2 * r : ℕ) : ℝ) * p - ((k + 2 * c : ℤ) : ℝ) = ((X : ℝ) * p - k) + 2 * η := by
    push_cast
    rw [hxnR]
    linear_combination 2 * hrt
  rw [eδ] at hDw'
  have hτδ : τ ≤ |((X : ℝ) * p - k) + 2 * η| := le_trans hDw hDw'
  rcases le_or_gt 0 (((X : ℝ) * p - k) + 2 * η) with hδ | hδ
  · rw [abs_of_nonneg hδ] at hτδ
    exfalso
    linarith
  · rw [abs_of_neg hδ] at hτδ
    -- τ + 2η ≤ b = -(X p - k), and r b = 1 - X η
    have hneg : τ ≤ -(((X : ℝ) * p - k) + 2 * η) := hτδ
    have hm := mul_le_mul_of_nonneg_left hneg hrpos.le
    have hkey : (r : ℝ) * τ + ((2 : ℝ) * r + X) * η ≤ 1 := by nlinarith
    have hDR : (2 : ℝ) * N + 1 ≤ 4 * r + X := by
      have : 2 * N + 1 ≤ xn + 4 * r := by omega
      have h' : ((2 * N + 1 : ℕ) : ℝ) ≤ ((xn + 4 * r : ℕ) : ℝ) := by exact_mod_cast this
      push_cast at h'
      rw [hxnR] at h'
      linarith
    have hXnn : (0 : ℝ) ≤ X := by
      rw [← hxnR]; positivity
    have hη' : τ / 2 ≤ η := by linarith
    have hprod : ((2 : ℝ) * r + X) * (τ / 2) ≤ ((2 : ℝ) * r + X) * η :=
      mul_le_mul_of_nonneg_left hη' (by positivity)
    have hfin : τ * ((2 : ℝ) * N + 1) ≤ 2 := by
      have h5 : τ * ((2 : ℝ) * N + 1) ≤ τ * (4 * r + X) :=
        mul_le_mul_of_nonneg_left hDR hτpos.le
      nlinarith
    rw [le_div_iff₀ (by positivity)]
    exact hfin

/-- **Core for the family** (Dirichlet + arc, both signs of `η`). -/
theorem coreV {N r D : ℕ} (hS : DSpec N r D) (hDg : 2 * N < D + 2 * r) (τ p : ℝ)
    (hτ : 1 / ((N : ℝ) + 1) < τ)
    (hx : ∀ x : ℕ, 1 ≤ x → x ≤ N → x ≠ r → τ ≤ nearestIntDist ((x : ℝ) * p))
    (hw : ∀ w : ℕ, N + r + 1 ≤ w → w ≤ N + 2 * r → Nat.Coprime w r →
      τ ≤ nearestIntDist ((w : ℝ) * p)) :
    τ ≤ 2 / ((2 : ℝ) * N + 1) := by
  have hr := hS.hr
  have hN2 := hS.hN
  have hN3 := hS.hN3
  obtain ⟨j, q, hq0, hqN, hqd⟩ := Real.exists_int_int_abs_mul_sub_le p (n := N) (by omega)
  obtain ⟨qn, hqn⟩ : ∃ qn : ℕ, (qn : ℤ) = q := ⟨q.toNat, Int.toNat_of_nonneg (by omega)⟩
  have hqnR : (qn : ℝ) = (q : ℝ) := by exact_mod_cast hqn
  have hqnN : qn ≤ N := by
    have : (qn : ℤ) ≤ N := by rw [hqn]; exact_mod_cast hqN
    exact_mod_cast this
  have hqr : qn = r := by
    by_contra hne
    have h3 := hx qn (by omega) hqnN hne
    rw [hqnR] at h3
    have h4 := nearestIntDist_le_dist ((q : ℝ) * p) j
    linarith
  have hqr' : (q : ℝ) = r := by rw [← hqnR]; exact_mod_cast hqr
  rw [hqr'] at hqd
  obtain ⟨hl, hu⟩ := abs_le.mp hqd
  rcases le_or_gt 0 ((r : ℝ) * p - j) with hη | hη
  · exact arcV_pos hS hDg τ p ((r : ℝ) * p - j) j hτ (by ring) hη hu hx hw
  · have hx' : ∀ x : ℕ, 1 ≤ x → x ≤ N → x ≠ r → τ ≤ nearestIntDist ((x : ℝ) * (-p)) := by
      intro x hx1 hxN hxr
      rw [show (x : ℝ) * (-p) = -((x : ℝ) * p) by ring, nearestIntDist_neg]
      exact hx x hx1 hxN hxr
    have hw' : ∀ w : ℕ, N + r + 1 ≤ w → w ≤ N + 2 * r → Nat.Coprime w r →
        τ ≤ nearestIntDist ((w : ℝ) * (-p)) := by
      intro w hw1 hw2 hw3
      rw [show (w : ℝ) * (-p) = -((w : ℝ) * p) by ring, nearestIntDist_neg]
      exact hw w hw1 hw2 hw3
    exact arcV_pos hS hDg τ (-p) (-((r : ℝ) * p - j)) (-j) hτ
      (by push_cast; ring) (by linarith) (by linarith) hx' hw'

/-- `gap v p ≤ 2/(2N+1)` for every `p`, when `v` carries the family `([N] \ {r}) ∪ W`. -/
theorem gapV_le {k N r D : ℕ} (hS : DSpec N r D) (hDg : 2 * N < D + 2 * r)
    (v : Fin (k + 1) → ℤ) (hV : IsV N r v) (p : ℝ) : gap v p ≤ 2 / ((2 : ℝ) * N + 1) := by
  by_contra hcon
  have hcon' := not_le.mp hcon
  have hNR : (0 : ℝ) < (N : ℝ) + 1 := by positivity
  have h12 : 1 / ((N : ℝ) + 1) < 2 / ((2 : ℝ) * N + 1) := by
    rw [div_lt_div_iff₀ hNR (by positivity)]
    linarith
  have hτ := lt_trans h12 hcon'
  have hx : ∀ x : ℕ, 1 ≤ x → x ≤ N → x ≠ r → gap v p ≤ nearestIntDist ((x : ℝ) * p) := by
    intro x hx1 hxN hxr
    obtain ⟨i, hi⟩ := hV.cov x (Or.inl ⟨hx1, hxN, hxr⟩)
    have h1 := gap_le v p i
    have h2 : ((v i : ℤ) : ℝ) = (x : ℝ) := by exact_mod_cast hi
    rw [h2] at h1
    exact h1
  have hw : ∀ w : ℕ, N + r + 1 ≤ w → w ≤ N + 2 * r → Nat.Coprime w r →
      gap v p ≤ nearestIntDist ((w : ℝ) * p) := by
    intro w hw1 hw2 hw3
    obtain ⟨i, hi⟩ := hV.cov w (Or.inr ⟨hw1, hw2, hw3⟩)
    have h1 := gap_le v p i
    have h2 : ((v i : ℤ) : ℝ) = (w : ℝ) := by exact_mod_cast hi
    rw [h2] at h1
    exact h1
  have := coreV hS hDg (gap v p) p hτ hx hw
  linarith

/-- `ML v ≤ 2/(2N+1)` when `D0 > 2N - 2r`. -/
theorem ML_le_two_div_2N1 {k N r D : ℕ} (hS : DSpec N r D) (hDg : 2 * N < D + 2 * r)
    (v : Fin (k + 1) → ℤ) (hV : IsV N r v) : ML v ≤ 2 / ((2 : ℝ) * N + 1) := by
  unfold ML
  apply csSup_le (Set.range_nonempty _)
  rintro y ⟨t, rfl⟩
  exact gapV_le hS hDg v hV t

end Gap
end Sext6
end LRSpectrumFull
