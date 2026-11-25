import LRSpectrumFull.Sext6.Gap.Witness
import LRSpectrumFull.Sext6.Gap.Value

/-!
# The `1/r` case: `ML (([1,N] \ {r}) ∪ {w}) = 1/r` iff `r ∤ w`  [2026-11-24]

Setting: `N = k + 1` speeds, `2 ≤ N`, `N < 2 r`, `r ≤ N`, `w > N`; `V = wFam k r w`.
COMPUTED first (an accompanying exact search tool, exact, N = 4..40, r in (N/2, N], w in (N, 400], 200,000+ sets):
`r ∤ w` gives `ML = 1/r` exactly in every case; `r ∣ w` gives `ML < 1/r` in every case.

* `ML_ge_inv`        : `r ∤ w`  ⟹  `1/r ≤ ML`  (time `t = 1/r`; the only multiple of `r` in `[1,N]` is `r`).
* `ML_le_inv`        : `ML ≤ 1/r` for EVERY `w` (Dirichlet trapping as in `ML_le_tau`, but the blocker
  `X` with `c X ≡ -1 (mod r)` is at distance `(1 - X η)/r ≤ 1/r`; the inserted speed is not used).
* `ML_wFam_lt_inv`   : `w = m r`, `m ≥ 2`  ⟹  `ML < 1/r` (Theorem V: `max (1/(N+1)) (m/(m r + β)) < 1/r`).
* `ML_wFam_eq_inv_iff`: `ML = 1/r  ↔  ¬ r ∣ w`  (for `w > N`).
No `sorry`, no `axiom`.

Convention: `N = k + 1` is the number of speeds of the vector `v : Fin (k+1) → ℤ`. Speeds are the moving runners; the runner at rest is not counted, so a vector of `N` speeds means `N + 1` runners and the Lonely Runner value is `1/(N+1)`.
Hypotheses: those of the individual statements (numerical bounds, structural conditions and, where named in the list above, window predicates such as `PrimeWin`, `CopWin`, `PrimeWindow7`, which later modules discharge for explicit ranges). The unproved predicates `DusartPi`, `LRCHyp`, `CopWinHyp` are not hypotheses of any statement in this module.
Axiom audit: covered by `Axioms4` (first); every later audit module imports this module (`#print axioms`; declarations not printed there are bricks of printed ones, so their axioms are bounded by the printed lines).
-/

namespace LRSpectrumFull
namespace Sext6
namespace Gap

/-- `r ∤ z` gives `‖z/r‖ ≥ 1/r`. -/
theorem nid_div_ge_inv {r : ℕ} (hr : 0 < r) (z : ℤ) (hz : ¬ ((r : ℤ) ∣ z)) :
    1 / (r : ℝ) ≤ nearestIntDist ((z : ℝ) / r) := by
  have key : ((1 : ℕ) : ℝ) / (r : ℝ) ≤ nearestIntDist ((z : ℝ) / r) := by
    apply nid_div_ge hr z 1
    intro n
    have hne : z - n * (r : ℤ) ≠ 0 := by
      intro h
      apply hz
      exact ⟨n, by linarith⟩
    have := Int.one_le_abs hne
    exact_mod_cast this
  have h1 : ((1 : ℕ) : ℝ) = 1 := by norm_num
  rw [h1] at key
  exact key

/-- A retained speed `x ∈ [1,N] \ {r}` is not a multiple of `r` when `N < 2 r`. -/
theorem not_dvd_retained {N r x : ℕ} (hr1 : N < 2 * r) (hx1 : 1 ≤ x) (hxN : x ≤ N)
    (hxr : x ≠ r) : ¬ (r ∣ x) := by
  rintro ⟨c, hc⟩
  have hc3 : c = 0 ∨ c = 1 ∨ 2 ≤ c := by
    rcases Nat.lt_or_ge c 2 with h | h
    · omega
    · exact Or.inr (Or.inr h)
  rcases hc3 with h | h | h
  · rw [h] at hc
    simp at hc
    omega
  · rw [h] at hc
    simp at hc
    omega
  · have h2 : r * 2 ≤ r * c := Nat.mul_le_mul_left r h
    rw [← hc] at h2
    omega

/-- Lower bound: `r ∤ w` gives `1/r ≤ ML`. -/
theorem ML_ge_inv {k N r w : ℕ} (hk : k + 1 = N) (hr1 : N < 2 * r) (hr2 : r ≤ N)
    (hrw : ¬ (r ∣ w)) : 1 / (r : ℝ) ≤ ML (wFam k r w) := by
  have hr0 : 0 < r := by omega
  refine ML_ge_of_far (wFam k r w) (1 / (r : ℝ)) (1 / (r : ℝ)) ?_
  intro i
  have e : ((wFam k r w i : ℤ) : ℝ) * (1 / (r : ℝ)) = ((wFam k r w i : ℤ) : ℝ) / r := by
    rw [mul_one_div]
  rw [e]
  apply nid_div_ge_inv hr0
  by_cases hi : (i : ℕ) + 1 = r
  · rw [wFam_at_r i hi]
    intro hd
    exact hrw (Int.natCast_dvd_natCast.mp hd)
  · rw [wFam_ne_r i hi]
    intro hd
    have hiN : (i : ℕ) < k + 1 := i.isLt
    exact not_dvd_retained (x := (i : ℕ) + 1) hr1 (by omega) (by omega) hi
      (Int.natCast_dvd_natCast.mp hd)

/-- Core of the upper bound: no time `t` at which `r t = c + η`, `0 ≤ η ≤ 1/(N+1)` and all retained speeds
are farther than `1/r` from an integer. -/
theorem inv_core_false {N r : ℕ} (hN : 2 ≤ N) (hr1 : N < 2 * r) (hr2 : r ≤ N)
    (t : ℝ) (c : ℤ) (η : ℝ) (hrt : (r : ℝ) * t = c + η) (hη0 : 0 ≤ η)
    (hη1 : η ≤ 1 / ((N : ℝ) + 1))
    (hx : ∀ x : ℕ, 1 ≤ x → x ≤ N → x ≠ r → 1 / (r : ℝ) < nearestIntDist ((x : ℝ) * t)) :
    False := by
  have hS := spec_betaFam (m := 2) hN hr1 hr2 le_rfl
  have hrr := hS.two_le_r
  have hNR : (0 : ℝ) < (N : ℝ) + 1 := by positivity
  have hrpos : (0 : ℝ) < r := by exact_mod_cast (by omega : 0 < r)
  have hη2 : η * ((N : ℝ) + 1) ≤ 1 := (le_div_iff₀ hNR).mp hη1
  have hτ1 : 1 / ((N : ℝ) + 1) ≤ 1 / (r : ℝ) := by
    apply one_div_le_one_div_of_le hrpos
    have : (r : ℝ) ≤ N := by exact_mod_cast hr2
    linarith
  have hcop := unit_of_trap hS (1 / (r : ℝ)) hτ1 t c η hrt hη0 hη1 hx
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
  have hkR : (c : ℝ) * X + 1 = r * k := by exact_mod_cast hk
  have hw : (r : ℝ) * ((X : ℝ) * t - k) = X * η - 1 := by
    linear_combination (X : ℝ) * hrt + hkR
  have hXR : (X : ℝ) ≤ N := by rw [← hxnR]; exact_mod_cast hxN
  have hX1R : (1 : ℝ) ≤ X := by exact_mod_cast hXpos
  have hXη : (X : ℝ) * η ≤ 1 := by
    have h1 : (X : ℝ) * η ≤ N * η := mul_le_mul_of_nonneg_right hXR hη0
    nlinarith
  have hw0 : (X : ℝ) * t - k ≤ 0 := by
    by_contra hcon
    have := mul_pos hrpos (not_le.mp hcon)
    linarith
  have hxv := hx xn (by omega) hxN hxr
  rw [hxnR] at hxv
  have h1 : 1 / (r : ℝ) < -((X : ℝ) * t - k) := by
    have := lt_of_lt_of_le hxv (nearestIntDist_le_dist ((X : ℝ) * t) k)
    rwa [abs_of_nonpos hw0] at this
  have h2 : (r : ℝ) * (1 / (r : ℝ)) < 1 - X * η := by
    have := mul_lt_mul_of_pos_left h1 hrpos
    linarith
  have h3 : (r : ℝ) * (1 / (r : ℝ)) = 1 := mul_one_div_cancel hrpos.ne'
  have h4 : 0 ≤ (X : ℝ) * η := mul_nonneg (by linarith) hη0
  linarith

/-- Upper bound: `ML ≤ 1/r` for every `w`. -/
theorem ML_le_inv {k N r w : ℕ} (hk : k + 1 = N) (hN : 2 ≤ N) (hr1 : N < 2 * r)
    (hr2 : r ≤ N) : ML (wFam k r w) ≤ 1 / (r : ℝ) := by
  have hrr : 2 ≤ r := by omega
  have hrpos : (0 : ℝ) < r := by exact_mod_cast (by omega : 0 < r)
  have hτ1 : 1 / ((N : ℝ) + 1) ≤ 1 / (r : ℝ) := by
    apply one_div_le_one_div_of_le hrpos
    have : (r : ℝ) ≤ N := by exact_mod_cast hr2
    linarith
  unfold ML
  apply csSup_le (Set.range_nonempty _)
  rintro y ⟨t, rfl⟩
  by_contra hcon
  push Not at hcon
  have hx : ∀ x : ℕ, 1 ≤ x → x ≤ N → x ≠ r → 1 / (r : ℝ) < nearestIntDist ((x : ℝ) * t) := by
    intro x hx1 hxN hxr
    obtain ⟨i, hi⟩ := wFam_retained (w := w) hk hx1 hxN hxr
    have hv : ((wFam k r w i : ℤ) : ℝ) = (x : ℝ) := by rw [hi]; simp
    have h5 := gap_le (wFam k r w) t i
    rw [hv] at h5
    exact lt_of_lt_of_le hcon h5
  obtain ⟨j, q, hq0, hqN, hqd⟩ := Real.exists_int_int_abs_mul_sub_le t (n := N) (by omega)
  obtain ⟨qn, hqn⟩ : ∃ qn : ℕ, (qn : ℤ) = q := ⟨q.toNat, Int.toNat_of_nonneg (by omega)⟩
  have hqnR : (qn : ℝ) = (q : ℝ) := by exact_mod_cast hqn
  have hqnN : qn ≤ N := by
    have : (qn : ℤ) ≤ N := by rw [hqn]; exact_mod_cast hqN
    exact_mod_cast this
  have hqr : qn = r := by
    by_contra hne
    have h3 := hx qn (by omega) hqnN hne
    rw [hqnR] at h3
    have h4 := nearestIntDist_le_dist ((q : ℝ) * t) j
    linarith
  have hqr' : (q : ℝ) = r := by rw [← hqnR]; exact_mod_cast hqr
  rw [hqr'] at hqd
  obtain ⟨hl, hu⟩ := abs_le.mp hqd
  rcases le_or_gt 0 ((r : ℝ) * t - j) with hη | hη
  · exact inv_core_false hN hr1 hr2 t j ((r : ℝ) * t - j) (by ring) hη hu hx
  · refine inv_core_false hN hr1 hr2 (-t) (-j) (-((r : ℝ) * t - j)) (by push_cast; ring)
      (by linarith) (by linarith) ?_
    intro x hx1 hxN hxr
    have := hx x hx1 hxN hxr
    rwa [show (x : ℝ) * (-t) = -((x : ℝ) * t) by ring, nearestIntDist_neg]

/-- `w = m r` with `m ≥ 2` gives `ML < 1/r` (from Theorem V). -/
theorem ML_wFam_lt_inv {k N r m : ℕ} (hk : k + 1 = N) (hN : 2 ≤ N) (hr1 : N < 2 * r)
    (hr2 : r ≤ N) (hm : 2 ≤ m) : ML (wFam k r (m * r)) < 1 / (r : ℝ) := by
  have hS := spec_betaFam (m := m) hN hr1 hr2 hm
  have hbpos := hS.beta_pos
  have hrr := hS.two_le_r
  have hrpos : (0 : ℝ) < r := by exact_mod_cast (by omega : 0 < r)
  have hDR : (0 : ℝ) < ((m * r + betaFam N r : ℕ) : ℝ) := by
    have : 0 < m * r + betaFam N r := by omega
    exact_mod_cast this
  rw [← vFam_eq_wFam, theoremV hk hN hr1 hr2 hm]
  apply max_lt
  · apply one_div_lt_one_div_of_lt hrpos
    have : (r : ℝ) ≤ N := by exact_mod_cast hr2
    linarith
  · rw [div_lt_div_iff₀ hDR hrpos]
    have hbR : (0 : ℝ) < (betaFam N r : ℝ) := by exact_mod_cast hbpos
    push_cast
    nlinarith

/-- **The `1/r` case.**  For `N ≥ 2`, `N/2 < r ≤ N` and `w > N`:
`ML (([1,N] \ {r}) ∪ {w}) = 1/r` exactly when `r ∤ w`. -/
theorem ML_wFam_eq_inv_iff {k N r w : ℕ} (hk : k + 1 = N) (hN : 2 ≤ N) (hr1 : N < 2 * r)
    (hr2 : r ≤ N) (hw : N < w) :
    ML (wFam k r w) = 1 / (r : ℝ) ↔ ¬ (r ∣ w) := by
  constructor
  · intro heq hdvd
    obtain ⟨m, hm⟩ := hdvd
    have hm2 : 2 ≤ m := by
      rcases (show m = 0 ∨ m = 1 ∨ 2 ≤ m by omega) with h | h | h
      · rw [h] at hm
        simp at hm
        omega
      · rw [h] at hm
        simp at hm
        omega
      · exact h
    have hw' : w = m * r := by rw [hm]; ring
    rw [hw'] at heq
    have hlt := ML_wFam_lt_inv hk hN hr1 hr2 hm2
    linarith
  · intro hnd
    exact le_antisymm (ML_le_inv hk hN hr1 hr2) (ML_ge_inv hk hr1 hr2 hnd)

end Gap
end Sext6
end LRSpectrumFull
