/-
# L3 (piece 2): ratio-closed primitive sextuples are exactly `(1..6)` and `(10,12,15,20,30,60)`.

Central idea: normalise by the smallest entry `m`; then `60 v_j = w_j m` with `w_j` in a 12-element set,
and the finite list of `w`-sets with all pairwise ratios of the form `a/b`, `a ≠ b ∈ {1..6}` is
found by kernel `decide` over the 924 six-subsets.  Primitivity then pins `m`.
-/
import LRSpectrumFull.Sext6.L1prime
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.LinearCombination
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Max

namespace LRSpectrumFull
namespace Sext6

/-- `y / x`-ratio condition: `y/x = b/a`-type relation `b x = a y` with `a ≠ b ∈ {1..6}`. -/
abbrev ratioOK (x y : ℤ) : Prop :=
  ∃ a ∈ Finset.Icc (1 : ℤ) 6, ∃ b ∈ Finset.Icc (1 : ℤ) 6, a ≠ b ∧ b * x = a * y

def U' : Finset ℤ := {60, 72, 75, 80, 90, 100, 120, 150, 180, 240, 300, 360}
def WA : Finset ℤ := {60, 120, 180, 240, 300, 360}
def WB : Finset ℤ := {60, 72, 90, 120, 180, 360}

/-- The only 6-subsets of `U'` whose elements are pairwise ratio-related. -/
theorem finite_sols : ∀ T ∈ U'.powersetCard 6,
    (∀ x ∈ T, ∀ y ∈ T, x ≠ y → ratioOK x y) → T = WA ∨ T = WB := by
  decide +kernel

theorem coef_mem : ∀ a ∈ Finset.Icc (1 : ℤ) 6, ∀ b ∈ Finset.Icc (1 : ℤ) 6, b < a →
    b ∣ 60 * a ∧ 60 * a / b ∈ U' := by
  decide +kernel

theorem perm_of_mem {n : ℕ} (u v : Fin n → ℤ) (hv : Function.Injective v)
    (h : ∀ j, ∃ k, u k = v j) : ∃ σ : Equiv.Perm (Fin n), ∀ j, v j = u (σ j) := by
  choose f hf using h
  have hfi : Function.Injective f := fun a b hab => hv (by rw [← hf a, ← hf b, hab])
  exact ⟨Equiv.ofBijective f (Finite.injective_iff_bijective.mp hfi), fun j => (hf j).symm⟩

theorem prim_unit (v : Fin 6 → ℤ) (hprim : Primitive v) (m : ℤ) (hm : 0 < m)
    (h : ∀ i, m ∣ v i) : m = 1 := by
  have e : (m.toNat : ℤ) = m := Int.toNat_of_nonneg hm.le
  have h1 := hprim m.toNat (fun i => by rw [e]; exact h i)
  omega

theorem v2_vals : v2 0 = 10 ∧ v2 1 = 12 ∧ v2 2 = 15 ∧ v2 3 = 20 ∧ v2 4 = 30 ∧ v2 5 = 60 := by
  decide

/-- **L3.** -/
theorem L3 (v : Fin 6 → ℤ) (hinj : Function.Injective v) (hpos : ∀ i, 0 < v i)
    (hprim : Primitive v)
    (hpair : ∀ i j, i ≠ j → ∃ a b : ℤ, a ∈ Finset.Icc (1 : ℤ) 6 ∧ b ∈ Finset.Icc (1 : ℤ) 6 ∧
      a ≠ b ∧ b * v i = a * v j) :
    (∃ σ : Equiv.Perm (Fin 6), ∀ i, v i = (σ i : ℕ) + 1) ∨
    (∃ σ : Equiv.Perm (Fin 6), ∀ i, v i = v2 (σ i)) := by
  obtain ⟨i0, -, hi0'⟩ := Finset.exists_min_image Finset.univ v Finset.univ_nonempty
  have hi0 : ∀ j, v i0 ≤ v j := fun j => hi0' j (Finset.mem_univ j)
  have hm : 0 < v i0 := hpos i0
  have hw : ∀ j, ∃ w : ℤ, w ∈ U' ∧ 60 * v j = w * v i0 := by
    intro j
    by_cases hj : j = i0
    · subst hj
      exact ⟨60, by decide, rfl⟩
    · obtain ⟨a, b, ha, hb, hab, h⟩ := hpair j i0 hj
      have hjm : v i0 < v j := lt_of_le_of_ne (hi0 j) (fun e => hj (hinj e.symm))
      have ha' := Finset.mem_Icc.mp ha
      have hb' := Finset.mem_Icc.mp hb
      have hb0 : 0 < b := by omega
      have hba : b < a := by
        by_contra hcon
        push Not at hcon
        have h1 : a * v i0 ≤ b * v i0 := mul_le_mul_of_nonneg_right hcon hm.le
        have h2 : b * v i0 < b * v j := mul_lt_mul_of_pos_left hjm hb0
        linarith
      obtain ⟨hdvd, hmem⟩ := coef_mem a ha b hb hba
      refine ⟨60 * a / b, hmem, ?_⟩
      have e1 : 60 * a / b * b = 60 * a := Int.ediv_mul_cancel hdvd
      apply mul_left_cancel₀ hb0.ne'
      calc b * (60 * v j) = 60 * (b * v j) := by ring
        _ = 60 * (a * v i0) := by rw [h]
        _ = (60 * a / b * b) * v i0 := by rw [e1]; ring
        _ = b * (60 * a / b * v i0) := by ring
  choose w hwU hw60 using hw
  have hwinj : Function.Injective w := by
    intro j k hjk
    apply hinj
    have : 60 * v j = 60 * v k := by rw [hw60 j, hw60 k, hjk]
    linarith
  have hwpair : ∀ j k, j ≠ k → ratioOK (w j) (w k) := by
    intro j k hjk
    obtain ⟨a, b, ha, hb, hab, h⟩ := hpair j k hjk
    refine ⟨a, ha, b, hb, hab, ?_⟩
    have : (b * w j) * v i0 = (a * w k) * v i0 := by
      linear_combination (-b) * hw60 j + a * hw60 k + 60 * h
    exact mul_right_cancel₀ hm.ne' this
  have hWcard : (Finset.univ.image w).card = 6 := by
    rw [Finset.card_image_of_injective _ hwinj]; simp
  have hWsub : Finset.univ.image w ⊆ U' := by
    intro x hx
    obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hx
    exact hwU j
  have hWmem : Finset.univ.image w ∈ U'.powersetCard 6 :=
    Finset.mem_powersetCard.mpr ⟨hWsub, hWcard⟩
  have hWpair : ∀ x ∈ Finset.univ.image w, ∀ y ∈ Finset.univ.image w, x ≠ y → ratioOK x y := by
    intro x hx y hy hxy
    obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨k, _, rfl⟩ := Finset.mem_image.mp hy
    exact hwpair j k (fun e => hxy (by rw [e]))
  rcases finite_sols _ hWmem hWpair with hA | hB
  · left
    have hc : ∀ j, ∃ c : ℤ, 1 ≤ c ∧ c ≤ 6 ∧ v j = c * v i0 := by
      intro j
      have hj : w j ∈ WA := hA ▸ Finset.mem_image_of_mem w (Finset.mem_univ j)
      simp only [WA, Finset.mem_insert, Finset.mem_singleton] at hj
      have h60 := hw60 j
      rcases hj with h | h | h | h | h | h <;> rw [h] at h60
      · exact ⟨1, by norm_num, by norm_num, by linarith⟩
      · exact ⟨2, by norm_num, by norm_num, by linarith⟩
      · exact ⟨3, by norm_num, by norm_num, by linarith⟩
      · exact ⟨4, by norm_num, by norm_num, by linarith⟩
      · exact ⟨5, by norm_num, by norm_num, by linarith⟩
      · exact ⟨6, by norm_num, by norm_num, by linarith⟩
    have hm1 : v i0 = 1 := by
      apply prim_unit v hprim (v i0) hm
      intro j
      obtain ⟨c, _, _, hc'⟩ := hc j
      exact ⟨c, by linarith⟩
    obtain ⟨σ, hσ⟩ := perm_of_mem (fun k : Fin 6 => ((k : ℕ) : ℤ) + 1) v hinj (by
      intro j
      obtain ⟨c, h1, h6, hc'⟩ := hc j
      rw [hm1] at hc'
      exact ⟨⟨(c - 1).toNat, by omega⟩, by simp only; omega⟩)
    exact ⟨σ, fun i => hσ i⟩
  · right
    have h72 : (72 : ℤ) ∈ Finset.univ.image w := by rw [hB]; simp [WB]
    have h90 : (90 : ℤ) ∈ Finset.univ.image w := by rw [hB]; simp [WB]
    obtain ⟨j1, _, hj1⟩ := Finset.mem_image.mp h72
    obtain ⟨j2, _, hj2⟩ := Finset.mem_image.mp h90
    have e1 := hw60 j1
    have e2 := hw60 j2
    rw [hj1] at e1
    rw [hj2] at e2
    obtain ⟨d, hd⟩ : (10 : ℤ) ∣ v i0 := by omega
    have hd0 : 0 < d := by omega
    obtain ⟨hv0, hv1, hv2, hv3, hv4, hv5⟩ := v2_vals
    have hc : ∀ j, ∃ k : Fin 6, v j = v2 k * d := by
      intro j
      have hj : w j ∈ WB := hB ▸ Finset.mem_image_of_mem w (Finset.mem_univ j)
      simp only [WB, Finset.mem_insert, Finset.mem_singleton] at hj
      have h60 := hw60 j
      rcases hj with h | h | h | h | h | h <;> rw [h, hd] at h60
      · exact ⟨0, by rw [hv0]; linarith⟩
      · exact ⟨1, by rw [hv1]; linarith⟩
      · exact ⟨2, by rw [hv2]; linarith⟩
      · exact ⟨3, by rw [hv3]; linarith⟩
      · exact ⟨4, by rw [hv4]; linarith⟩
      · exact ⟨5, by rw [hv5]; linarith⟩
    have hd1 : d = 1 := by
      apply prim_unit v hprim d hd0
      intro j
      obtain ⟨k, hk⟩ := hc j
      exact ⟨v2 k, by rw [hk]; ring⟩
    subst hd1
    obtain ⟨σ, hσ⟩ := perm_of_mem v2 v hinj (by
      intro j
      obtain ⟨k, hk⟩ := hc j
      exact ⟨k, by rw [hk]; ring⟩)
    exact ⟨σ, hσ⟩

end Sext6
end LRSpectrumFull

#print axioms LRSpectrumFull.Sext6.L3
