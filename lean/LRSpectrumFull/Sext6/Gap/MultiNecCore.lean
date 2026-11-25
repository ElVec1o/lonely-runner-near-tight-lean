import LRSpectrumFull.Sext6.Gap.MultiLower

/-!
# Multi-entry value theorem: necessity, the equality case of the trap  [2026-11-25]

`mnec_core` is `mcore_false` with every `<` replaced by `≤` at the level of the speeds and with
`1/(N+1) < τ` strict.  Where `mcore_false` derives a contradiction from `τ < ‖·‖`, the equality case
derives `τ = m/(m r + β)`, `η = 1/(m r + β)` and `X = β` (so `r ∣ c β + 1`): the time is pinned to
`(c m + k)/(m r + β)`.

* `int_far_of_nid` : `m/D ≤ ‖z/D‖` gives `m ≤ |z - n D|` for every integer `n` (converse of `nid_div_ge`).
* `mnec_core`      : the equality case.
No `sorry`, no `axiom`.

Convention: `N` is the size of the ambient interval `[1,N]`; the speed vector `v : Fin (k+1) → ℤ` is a finite family (repetitions allowed) and `k`, `N` are independent parameters of the generic statements. Speeds are the moving runners; the runner at rest is not counted, so a vector of `N` speeds means `N + 1` runners and the Lonely Runner value is `1/(N+1)`.
Axiom audit: covered by `Axioms23`.
-/

namespace LRSpectrumFull
namespace Sext6
namespace Gap

theorem int_far_of_nid {D : ℕ} (hD : 0 < D) (z : ℤ) (m : ℕ)
    (h : (m : ℝ) / D ≤ nearestIntDist ((z : ℝ) / D)) (n : ℤ) :
    (m : ℤ) ≤ |z - n * D| := by
  have hDR : (0 : ℝ) < D := by exact_mod_cast hD
  have hDne : (D : ℝ) ≠ 0 := hDR.ne'
  have h1 := nearestIntDist_le_dist ((z : ℝ) / D) n
  have e : (z : ℝ) / D - n = ((z - n * D : ℤ) : ℝ) / D := by
    push_cast; field_simp
  rw [e, abs_div, abs_of_pos hDR] at h1
  have h2 : (m : ℝ) / D ≤ |((z - n * D : ℤ) : ℝ)| / D := h.trans h1
  have h3 : (m : ℝ) ≤ |((z - n * D : ℤ) : ℝ)| := (div_le_div_iff_of_pos_right hDR).mp h2
  have h4 : (m : ℝ) ≤ ((|z - n * D| : ℤ) : ℝ) := by rw [Int.cast_abs]; exact h3
  exact_mod_cast h4

theorem mnec_core {N r m β : ℕ} (R : Finset ℕ) (hRlt : ∀ r' ∈ R, N < 2 * r')
    (hG : ∀ r' ∈ R, r' ≠ r → ¬ Nat.Coprime r' r)
    (hS : Spec N r m β) (τ : ℝ)
    (hτ1 : 1 / ((N : ℝ) + 1) < τ) (hτ2 : (m : ℝ) / ((m * r + β : ℕ) : ℝ) ≤ τ)
    (t : ℝ) (c : ℤ) (η : ℝ) (hrt : (r : ℝ) * t = c + η) (hη0 : 0 ≤ η)
    (hη1 : η ≤ 1 / ((N : ℝ) + 1))
    (hx : ∀ x : ℕ, 1 ≤ x → x ≤ N → x ∉ R → τ ≤ nearestIntDist ((x : ℝ) * t))
    (hm : τ ≤ nearestIntDist (((m : ℝ) * r) * t)) :
    τ = (m : ℝ) / ((m * r + β : ℕ) : ℝ) ∧ η = 1 / ((m * r + β : ℕ) : ℝ) ∧
      ∃ k : ℤ, c * (β : ℤ) + 1 = r * k := by
  have hN2 := hS.hN
  have hr2 := hS.hr2
  have hrr := hS.two_le_r
  have hr1 := hS.hr1
  have hb1 := hS.hb1
  have hbpos := hS.beta_pos
  have hNR : (0 : ℝ) < (N : ℝ) + 1 := by positivity
  have hη2 : η * ((N : ℝ) + 1) ≤ 1 := (le_div_iff₀ hNR).mp hη1
  have hτpos : 0 < τ := lt_of_le_of_lt (by positivity) hτ1
  have hτ' : (1 : ℝ) / ((N : ℝ) + 1) ≤ (1 / ((N : ℝ) + 1) + τ) / 2 := by linarith
  have hcop := munit_of_trap R hRlt hS ((1 / ((N : ℝ) + 1) + τ) / 2) hτ' t c η hrt hη0 hη1
    (fun x hx1 hxN hxR => lt_of_lt_of_le (by linarith) (hx x hx1 hxN hxR))
  obtain ⟨X, hX1, hX2, hXd⟩ := exists_block r ((N : ℤ) + 1 - r) (by omega) c hcop
  obtain ⟨k, hk⟩ := hXd
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
  have h1 : τ ≤ -((X : ℝ) * t - k) := by
    have := le_trans hxv (nearestIntDist_le_dist ((X : ℝ) * t) k)
    rwa [abs_of_nonpos hw0] at this
  have h2 : (r : ℝ) * τ ≤ 1 - X * η := by
    have := mul_le_mul_of_nonneg_left h1 hrpos.le
    linarith
  have hmη : τ ≤ (m : ℝ) * η := by
    have e : ((m : ℝ) * r) * t - ((m * c : ℤ) : ℝ) = m * η := by
      push_cast
      linear_combination (m : ℝ) * hrt
    have h7 := le_trans hm (nearestIntDist_le_dist (((m : ℝ) * r) * t) (m * c))
    rwa [e, abs_of_nonneg (by positivity)] at h7
  have hmR : (0 : ℝ) < m := by exact_mod_cast (by have := hS.hm; omega : 0 < m)
  have hDR : (0 : ℝ) < ((m * r + β : ℕ) : ℝ) := by
    have : 0 < m * r + β := by omega
    exact_mod_cast this
  have hstar : (m : ℝ) ≤ τ * ((m : ℝ) * r + β) := by
    have := (div_le_iff₀ hDR).mp hτ2
    push_cast at this
    exact this
  have hβR : (0 : ℝ) < β := by exact_mod_cast hbpos
  have hA : (β : ℝ) * ((m : ℝ) * η) ≤ (m : ℝ) * ((X : ℝ) * η) := by
    have h5 := mul_le_mul_of_nonneg_right hβxR hη0
    have h6 := mul_le_mul_of_nonneg_left h5 hmR.le
    linarith
  have hB : (m : ℝ) * ((X : ℝ) * η) ≤ (m : ℝ) * (1 - r * τ) := by
    refine mul_le_mul_of_nonneg_left ?_ hmR.le
    linarith
  have hC : (m : ℝ) * (1 - r * τ) ≤ τ * β := by linarith
  have hD : τ * β ≤ (β : ℝ) * ((m : ℝ) * η) := by
    have := mul_le_mul_of_nonneg_left hmη hβR.le
    linarith
  have e1 : (m : ℝ) * ((X : ℝ) * η) = β * (m * η) := by linarith
  have e3 : (m : ℝ) * (1 - r * τ) = τ * β := by linarith
  have e4 : τ * β = (β : ℝ) * ((m : ℝ) * η) := by linarith
  have hpos : 0 < (m : ℝ) * η := lt_of_lt_of_le hτpos hmη
  have hXβ : (X : ℝ) = β := by
    have h0 : ((m : ℝ) * η) * ((X : ℝ) - β) = 0 := by linarith
    rcases mul_eq_zero.mp h0 with h | h
    · exact absurd h hpos.ne'
    · linarith
  have hτD : τ * ((m * r + β : ℕ) : ℝ) = m := by
    push_cast
    linarith
  have hτeq : τ = (m : ℝ) / ((m * r + β : ℕ) : ℝ) := (eq_div_iff hDR.ne').mpr hτD
  have hmητ : (m : ℝ) * η = τ := by
    have h0 : (β : ℝ) * ((m : ℝ) * η - τ) = 0 := by linarith
    rcases mul_eq_zero.mp h0 with h | h
    · exact absurd h hβR.ne'
    · linarith
  have hηeq : η = 1 / ((m * r + β : ℕ) : ℝ) := by
    rw [eq_div_iff hDR.ne']
    have h8 : (m : ℝ) * (η * ((m * r + β : ℕ) : ℝ)) = (m : ℝ) * 1 := by
      linear_combination ((m * r + β : ℕ) : ℝ) * hmητ + hτD
    exact mul_left_cancel₀ hmR.ne' h8
  have hXβZ : X = (β : ℤ) := by exact_mod_cast hXβ
  refine ⟨hτeq, hηeq, k, ?_⟩
  rw [← hXβZ]
  exact hk

end Gap
end Sext6
end LRSpectrumFull
