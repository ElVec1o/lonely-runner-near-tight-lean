import LRSpectrumFull.Sext6.Gap.Q81S3

/-!
# Q8.1, Theorem C at `N = 4`: `2/9 ≤ ML`  [2026-11-25]

Source: the accompanying notes (part 2) section 3: `N = 4`, `(r1, r2) = (3, 4)`, `V = {1, 2, 3 m1, 4 m2}` (`v2Fam 3 3 4 m1 m2`).
At level `τ = 2/9` (`= 2/(2N+1)`, the value `G(4)`) the counting argument of Lemma 3 still works
(`1 - 4 τ = 1/9 > 0`), in the class `t = (1 + η)/4`, `0 < η ≤ 5/9` (retained `1, 2`), or `t = (2 + η)/3`, `0 < η ≤ 1/3`.
The same four finite checks as for `N = 5..9` (corner, two tails, box with explicit `η = p/q`) cover all `m1 ≥ 4`, `m2 ≥ 3`;
`m1 ≤ 3` or `m2 ≤ 2` is Case I (`caseI_ML`, `caseI'_ML`: `1/4 ≤ ML`).
* `theoremC_four` : `2/9 ≤ ML (v2Fam 3 3 4 m1 m2)` for all `m1, m2 ≥ 2`.
No `sorry`, no `axiom`.

Convention: `N = k + 1` is the number of speeds of the vector `v : Fin (k+1) → ℤ`. Speeds are the moving runners; the runner at rest is not counted, so a vector of `N` speeds means `N + 1` runners and the Lonely Runner value is `1/(N+1)`.
Hypotheses: those of the individual statements (numerical bounds, structural conditions and, where named in the list above, window predicates such as `PrimeWin`, `CopWin`, `PrimeWindow7`, which later modules discharge for explicit ranges). The unproved predicates `DusartPi`, `LRCHyp`, `CopWinHyp` are not hypotheses of any statement in this module.
Axiom audit: covered by `Axioms22` (`#print axioms`; declarations not printed there are bricks of printed ones, so their axioms are bounded by the printed lines).
-/

namespace LRSpectrumFull
namespace Sext6
namespace Gap

open MeasureTheory

/-- Integer certificate: `2/9 ≤ ‖n/D‖` from `2 D ≤ 9 (n mod D)` and `2 D ≤ 9 (D - n mod D)`. -/
theorem nid9_nat_div (n D : ℕ) (hD : 0 < D)
    (h1 : 2 * D ≤ 9 * (n % D)) (h2 : 2 * D ≤ 9 * (D - n % D)) :
    2 / 9 ≤ nearestIntDist ((n : ℝ) / D) := by
  have hDpos : (0 : ℝ) < D := by exact_mod_cast hD
  have hmod : n % D < D := Nat.mod_lt n hD
  obtain ⟨r, q, hr, hn⟩ : ∃ r q : ℕ, r = n % D ∧ n = r + D * q :=
    ⟨n % D, n / D, rfl, (Nat.mod_add_div n D).symm⟩
  rw [← hr] at h1 h2 hmod
  have e : (n : ℝ) / D = (r : ℝ) / D + ((q : ℤ) : ℝ) := by
    rw [hn]
    push_cast
    field_simp
  rw [e, nearestIntDist_add_int]
  have hr0 : (0 : ℝ) ≤ r := Nat.cast_nonneg _
  have hrD : (r : ℝ) < D := by exact_mod_cast hmod
  have h1c : 2 * (D : ℝ) ≤ 9 * r := by exact_mod_cast h1
  have h2c : 2 * (D : ℝ) ≤ 9 * ((D : ℝ) - r) := by
    have hs := (Nat.cast_sub hmod.le : ((D - r : ℕ) : ℝ) = (D : ℝ) - r)
    have : 2 * (D : ℝ) ≤ 9 * ((D - r : ℕ) : ℝ) := by exact_mod_cast h2
    rw [hs] at this
    exact this
  apply nearestIntDist_ge
  · positivity
  · rw [div_lt_one hDpos]; exact hrD
  · rw [le_div_iff₀ hDpos]; linarith
  · have : (r : ℝ) / D ≤ 7 / 9 := by
      rw [div_le_iff₀ hDpos]; linarith
    linarith

/-- Class `t = (1 + η)/4`. -/
theorem n4_core {m1 m2 : ℕ} (η : ℝ) (hη0 : 0 ≤ η) (hη1 : η ≤ 5 / 9)
    (hA : 2 / 9 ≤ nearestIntDist ((m2 : ℝ) * η))
    (hB : 2 / 9 ≤ nearestIntDist ((m1 : ℝ) / 4 - ((m1 : ℝ) * 3 / 4) * η)) :
    2 / 9 ≤ ML (v2Fam 3 3 4 m1 m2) := by
  have ht : ((((1 : ℤ) : ℝ) + η) / ((4 : ℕ) : ℝ)) = (1 + η) / 4 := by push_cast; ring
  refine ML_v2Fam_ge (N := 4) (k := 3) (r1 := 3) (r2 := 4) rfl (2 / 9)
    (((((1 : ℤ) : ℝ) + η) / ((4 : ℕ) : ℝ))) ?_ ?_ ?_
  · intro x hx1 hxN hxr1 hxr2
    have hx : x = 1 ∨ x = 2 := by omega
    rw [ht]
    rcases hx with rfl | rfl
    · simp only [Nat.cast_one, one_mul]
      apply nearestIntDist_ge <;> linarith
    · have e : ((2 : ℕ) : ℝ) * ((1 + η) / 4) = (1 + η) / 2 := by push_cast; ring
      rw [e]
      apply nearestIntDist_ge <;> linarith
  · have h := nid_mul_blocker m1 3 4 (1 : ℤ) 1 η (by norm_num) (by norm_num)
    rw [h]
    simpa using hB
  · rw [nid_mul_mod m2 4 (1 : ℤ) η (by norm_num)]
    exact hA

/-- Class `t = (2 + η)/3`. -/
theorem n3_core {m1 m2 : ℕ} (η : ℝ) (hη0 : 0 ≤ η) (hη1 : η ≤ 1 / 3)
    (hA : 2 / 9 ≤ nearestIntDist ((m1 : ℝ) * η))
    (hB : 2 / 9 ≤ nearestIntDist ((m2 : ℝ) / 3 - ((m2 : ℝ) * 4 / 3) * η)) :
    2 / 9 ≤ ML (v2Fam 3 3 4 m1 m2) := by
  have ht : ((((2 : ℤ) : ℝ) + η) / ((3 : ℕ) : ℝ)) = (2 + η) / 3 := by push_cast; ring
  refine ML_v2Fam_ge (N := 4) (k := 3) (r1 := 3) (r2 := 4) rfl (2 / 9)
    (((((2 : ℤ) : ℝ) + η) / ((3 : ℕ) : ℝ))) ?_ ?_ ?_
  · intro x hx1 hxN hxr1 hxr2
    have hx : x = 1 ∨ x = 2 := by omega
    rw [ht]
    rcases hx with rfl | rfl
    · simp only [Nat.cast_one, one_mul]
      apply nearestIntDist_ge <;> linarith
    · have e : ((2 : ℕ) : ℝ) * ((2 + η) / 3) = (1 + 2 * η) / 3 + (((1 : ℤ)) : ℝ) := by
        push_cast; ring
      rw [e, nearestIntDist_add_int]
      apply nearestIntDist_ge <;> linarith
  · rw [nid_mul_mod m1 3 (2 : ℤ) η (by norm_num)]
    exact hA
  · have h := nid_mul_blocker m2 4 3 (2 : ℤ) 3 η (by norm_num) (by norm_num)
    rw [h]
    simpa using hB

/-! ### The four regimes at `N = 4` (`τ = 2/9`) -/

def R14 (m1 m2 : ℕ) : Prop := 78 * m1 + 208 * m2 < 15 * m1 * m2
def S24P (m1 m2 cn cd : ℕ) : Prop :=
  0 < cd ∧ 9 * cn ≤ 5 * cd ∧ 9 * m2 * cn ≤ 7 * cd ∧ 2 * cd < 9 * m2 * cn ∧
    208 * m2 * cd < 15 * m1 * (9 * m2 * cn - 2 * cd)
def S14P (m1 m2 cn cd : ℕ) : Prop :=
  0 < cd ∧ 3 * cn ≤ cd ∧ 9 * m1 * cn ≤ 7 * cd ∧ 2 * cd < 9 * m1 * cn ∧
    39 * m1 * cd < 5 * m2 * (9 * m1 * cn - 2 * cd)
def chk24P (m1 m2 p q : ℕ) : Prop :=
  9 * p ≤ 5 * q ∧ 3 * p ≤ q ∧ 0 < q ∧ 2 * q ≤ 9 * ((m2 * p) % q) ∧ 2 * q ≤ 9 * (q - (m2 * p) % q) ∧
    8 * q ≤ 9 * ((m1 * (q - 3 * p)) % (4 * q)) ∧ 8 * q ≤ 9 * (4 * q - (m1 * (q - 3 * p)) % (4 * q))
def chk14P (m1 m2 p q : ℕ) : Prop :=
  3 * p ≤ q ∧ 4 * p ≤ q ∧ 0 < q ∧ 2 * q ≤ 9 * ((m1 * p) % q) ∧ 2 * q ≤ 9 * (q - (m1 * p) % q) ∧
    6 * q ≤ 9 * ((m2 * (q - 4 * p)) % (3 * q)) ∧ 6 * q ≤ 9 * (3 * q - (m2 * (q - 4 * p)) % (3 * q))

instance (m1 m2 : ℕ) : Decidable (R14 m1 m2) := by unfold R14; infer_instance
instance (m1 m2 cn cd : ℕ) : Decidable (S24P m1 m2 cn cd) := by unfold S24P; infer_instance
instance (m1 m2 cn cd : ℕ) : Decidable (S14P m1 m2 cn cd) := by unfold S14P; infer_instance
instance (m1 m2 p q : ℕ) : Decidable (chk24P m1 m2 p q) := by unfold chk24P; infer_instance
instance (m1 m2 p q : ℕ) : Decidable (chk14P m1 m2 p q) := by unfold chk14P; infer_instance

theorem chk24_sound {m1 m2 p q : ℕ} (h : chk24P m1 m2 p q) : 2 / 9 ≤ ML (v2Fam 3 3 4 m1 m2) := by
  obtain ⟨hE, hpq, hq, hA1, hA2, hB1, hB2⟩ := h
  have hqpos : (0 : ℝ) < q := by exact_mod_cast hq
  refine n4_core ((p : ℝ) / q) (by positivity) ?_ ?_ ?_
  · rw [div_le_div_iff₀ hqpos (by norm_num)]
    have : (9 : ℝ) * p ≤ 5 * q := by exact_mod_cast hE
    linarith
  · have e : (m2 : ℝ) * ((p : ℝ) / q) = ((m2 * p : ℕ) : ℝ) / q := by push_cast; ring
    rw [e]
    exact nid9_nat_div (m2 * p) q hq hA1 hA2
  · have hs : ((q - 3 * p : ℕ) : ℝ) = (q : ℝ) - 3 * p := by
      rw [Nat.cast_sub hpq]; push_cast; ring
    have e : (m1 : ℝ) / 4 - ((m1 : ℝ) * 3 / 4) * ((p : ℝ) / q) =
        ((m1 * (q - 3 * p) : ℕ) : ℝ) / ((4 * q : ℕ) : ℝ) := by
      simp only [Nat.cast_mul, hs]
      push_cast
      field_simp
      try ring
    rw [e]
    exact nid9_nat_div (m1 * (q - 3 * p)) (4 * q) (by omega) (by rw [show (2 : ℕ) * (4 * q) = 8 * q by ring]; exact hB1)
      (by rw [show (2 : ℕ) * (4 * q) = 8 * q by ring]; exact hB2)

theorem chk14_sound {m1 m2 p q : ℕ} (h : chk14P m1 m2 p q) : 2 / 9 ≤ ML (v2Fam 3 3 4 m1 m2) := by
  obtain ⟨hE, hpq, hq, hA1, hA2, hB1, hB2⟩ := h
  have hqpos : (0 : ℝ) < q := by exact_mod_cast hq
  refine n3_core ((p : ℝ) / q) (by positivity) ?_ ?_ ?_
  · rw [div_le_div_iff₀ hqpos (by norm_num)]
    have : (3 : ℝ) * p ≤ q := by exact_mod_cast hE
    linarith
  · have e : (m1 : ℝ) * ((p : ℝ) / q) = ((m1 * p : ℕ) : ℝ) / q := by push_cast; ring
    rw [e]
    exact nid9_nat_div (m1 * p) q hq hA1 hA2
  · have hs : ((q - 4 * p : ℕ) : ℝ) = (q : ℝ) - 4 * p := by
      rw [Nat.cast_sub hpq]; push_cast; ring
    have e : (m2 : ℝ) / 3 - ((m2 : ℝ) * 4 / 3) * ((p : ℝ) / q) =
        ((m2 * (q - 4 * p) : ℕ) : ℝ) / ((3 * q : ℕ) : ℝ) := by
      simp only [Nat.cast_mul, hs]
      push_cast
      field_simp
      try ring
    rw [e]
    exact nid9_nat_div (m2 * (q - 4 * p)) (3 * q) (by omega) (by rw [show (2 : ℕ) * (3 * q) = 6 * q by ring]; exact hB1)
      (by rw [show (2 : ℕ) * (3 * q) = 6 * q by ring]; exact hB2)

theorem R14_sound {m1 m2 : ℕ} (hm1 : 1 ≤ m1) (hm2 : 1 ≤ m2) (h : R14 m1 m2) :
    2 / 9 ≤ ML (v2Fam 3 3 4 m1 m2) := by
  have hm1pos : (0 : ℝ) < m1 := by exact_mod_cast hm1
  have hm2pos : (0 : ℝ) < m2 := by exact_mod_cast hm2
  have hI : (78 : ℝ) * m1 + 208 * m2 < 15 * m1 * m2 := by exact_mod_cast h
  have hαpos : (0 : ℝ) < (m1 : ℝ) * 3 / 4 := by positivity
  have hfin : 2 / 9 / (m2 : ℝ) + ((m2 : ℝ) * (5 / 9) + 2 / 9) * (2 * (2 / 9) / (m2 : ℝ)) +
      (((m1 : ℝ) * 3 / 4) * (5 / 9) + 2 * (2 / 9) + 1) * (2 * (2 / 9) / ((m1 : ℝ) * 3 / 4)) < 5 / 9 := by
    have key : 5 / 9 - (2 / 9 / (m2 : ℝ) + ((m2 : ℝ) * (5 / 9) + 2 / 9) * (2 * (2 / 9) / (m2 : ℝ)) +
      (((m1 : ℝ) * 3 / 4) * (5 / 9) + 2 * (2 / 9) + 1) * (2 * (2 / 9) / ((m1 : ℝ) * 3 / 4))) =
        (15 * m1 * m2 - 78 * m1 - 208 * m2) / (81 * m1 * m2 * 3) := by
      field_simp
      ring
    have : 0 < 5 / 9 - (2 / 9 / (m2 : ℝ) + ((m2 : ℝ) * (5 / 9) + 2 / 9) * (2 * (2 / 9) / (m2 : ℝ)) +
      (((m1 : ℝ) * 3 / 4) * (5 / 9) + 2 * (2 / 9) + 1) * (2 * (2 / 9) / ((m1 : ℝ) * 3 / 4))) := by
      rw [key]
      exact div_pos (by linarith) (by positivity)
    linarith
  obtain ⟨η, hη0, hηE, hA, hB⟩ := good_eta_exists (τ := 2 / 9) (E := 5 / 9) (a := (m2 : ℝ))
    (α := (m1 : ℝ) * 3 / 4) (x0 := (m1 : ℝ) / 4) (by norm_num) (by norm_num) (by norm_num)
    hm2pos hαpos hfin
  exact n4_core η hη0.le hηE hA hB

theorem S24_sound {m1 m2 cn cd : ℕ} (hm1 : 1 ≤ m1) (hm2 : 1 ≤ m2) (h : S24P m1 m2 cn cd) :
    2 / 9 ≤ ML (v2Fam 3 3 4 m1 m2) := by
  obtain ⟨hcd, hE, hA, hpos, hI⟩ := h
  have hm1pos : (0 : ℝ) < m1 := by exact_mod_cast hm1
  have hm2pos : (0 : ℝ) < m2 := by exact_mod_cast hm2
  have hcdpos : (0 : ℝ) < cd := by exact_mod_cast hcd
  have hposR : 2 * (cd : ℝ) < 9 * m2 * cn := by exact_mod_cast hpos
  have hcnpos : (0 : ℝ) < cn := by
    by_contra hc
    have h0 : (cn : ℝ) = 0 := le_antisymm (not_lt.mp hc) (Nat.cast_nonneg _)
    rw [h0] at hposR
    linarith
  have hy1 : 2 / (9 * (m2 : ℝ)) < (cn : ℝ) / cd := by
    rw [div_lt_div_iff₀ (by positivity) hcdpos]
    nlinarith
  obtain ⟨ℓ, hℓ⟩ : ∃ ℓ : ℝ, ℓ = (cn : ℝ) / cd - 2 / (9 * (m2 : ℝ)) := ⟨_, rfl⟩
  have hℓpos : 0 < ℓ := by rw [hℓ]; linarith
  obtain ⟨α, hα⟩ : ∃ α : ℝ, α = (m1 : ℝ) * 3 / 4 := ⟨_, rfl⟩
  have hαpos : 0 < α := by rw [hα]; positivity
  have hXI : 2 * (2 / 9 : ℝ) * (1 + 2 * (2 / 9)) < α * ℓ * (1 - 2 * (2 / 9)) := by
    have hI' : (208 : ℝ) * m2 * cd < 15 * m1 * (9 * m2 * cn - 2 * cd) := by
      have h1 : ((208 * m2 * cd : ℕ) : ℝ) < ((15 * m1 * (9 * m2 * cn - 2 * cd) : ℕ) : ℝ) := by
        exact_mod_cast hI
      have hs : ((9 * m2 * cn - 2 * cd : ℕ) : ℝ) = 9 * (m2 : ℝ) * cn - 2 * cd := by
        rw [Nat.cast_sub hpos.le]; push_cast; ring
      push_cast [hs] at h1
      linarith
    have hdiff : α * ℓ * (1 - 2 * (2 / 9)) - 2 * (2 / 9) * (1 + 2 * (2 / 9)) =
        (15 * (m1 : ℝ) * (9 * m2 * cn - 2 * cd) - 208 * m2 * cd) / (324 * m2 * cd) := by
      rw [hα, hℓ]
      field_simp
      try ring
    have : 0 < α * ℓ * (1 - 2 * (2 / 9)) - 2 * (2 / 9) * (1 + 2 * (2 / 9)) := by
      rw [hdiff]
      exact div_pos (by linarith) (by positivity)
    linarith
  have hfin : (α * ℓ + 2 * (2 / 9 : ℝ) + 1) * (2 * (2 / 9) / α) < ℓ := by
    have e : (α * ℓ + 2 * (2 / 9 : ℝ) + 1) * (2 * (2 / 9) / α) =
        ((α * ℓ + 2 * (2 / 9 : ℝ) + 1) * (2 * (2 / 9))) / α := by ring
    rw [e, div_lt_iff₀ hαpos]
    nlinarith
  obtain ⟨η, hη1, hη2, hB⟩ := good_eta_piece (τ := 2 / 9) (y1 := 2 / (9 * (m2 : ℝ))) (ℓ := ℓ)
    (α := α) (x0 := (m1 : ℝ) / 4) (by norm_num) hℓpos hαpos hfin
  have hη2' : η ≤ (cn : ℝ) / cd := by rw [hℓ] at hη2; linarith
  have hη0 : 0 < η := lt_of_le_of_lt (by positivity) hη1
  have hEc : (9 : ℝ) * cn ≤ 5 * cd := by exact_mod_cast hE
  have hAc : (9 : ℝ) * m2 * cn ≤ 7 * cd := by exact_mod_cast hA
  refine n4_core η hη0.le ?_ ?_ (by rw [← hα]; exact hB)
  · have h4 : (cn : ℝ) / cd ≤ 5 / 9 := by
      rw [div_le_div_iff₀ hcdpos (by norm_num)]; linarith
    linarith
  · apply nearestIntDist_ge
    · positivity
    · have h3 : (m2 : ℝ) * η ≤ (m2 : ℝ) * ((cn : ℝ) / cd) := mul_le_mul_of_nonneg_left hη2' hm2pos.le
      have h4 : (m2 : ℝ) * ((cn : ℝ) / cd) ≤ 7 / 9 := by
        have e : (m2 : ℝ) * ((cn : ℝ) / cd) = ((m2 : ℝ) * cn) / cd := by ring
        rw [e, div_le_div_iff₀ hcdpos (by norm_num)]; linarith
      linarith
    · have : 2 / (9 * (m2 : ℝ)) < η := hη1
      have h5 : (2 : ℝ) / 9 = (m2 : ℝ) * (2 / (9 * (m2 : ℝ))) := by field_simp
      rw [h5]
      exact mul_le_mul_of_nonneg_left this.le hm2pos.le
    · have h3 : (m2 : ℝ) * η ≤ (m2 : ℝ) * ((cn : ℝ) / cd) := mul_le_mul_of_nonneg_left hη2' hm2pos.le
      have h4 : (m2 : ℝ) * ((cn : ℝ) / cd) ≤ 7 / 9 := by
        have e : (m2 : ℝ) * ((cn : ℝ) / cd) = ((m2 : ℝ) * cn) / cd := by ring
        rw [e, div_le_div_iff₀ hcdpos (by norm_num)]; linarith
      linarith

theorem S14_sound {m1 m2 cn cd : ℕ} (hm1 : 1 ≤ m1) (hm2 : 1 ≤ m2) (h : S14P m1 m2 cn cd) :
    2 / 9 ≤ ML (v2Fam 3 3 4 m1 m2) := by
  obtain ⟨hcd, hE, hA, hpos, hI⟩ := h
  have hm1pos : (0 : ℝ) < m1 := by exact_mod_cast hm1
  have hm2pos : (0 : ℝ) < m2 := by exact_mod_cast hm2
  have hcdpos : (0 : ℝ) < cd := by exact_mod_cast hcd
  have hposR : 2 * (cd : ℝ) < 9 * m1 * cn := by exact_mod_cast hpos
  have hy1 : 2 / (9 * (m1 : ℝ)) < (cn : ℝ) / cd := by
    rw [div_lt_div_iff₀ (by positivity) hcdpos]
    nlinarith
  obtain ⟨ℓ, hℓ⟩ : ∃ ℓ : ℝ, ℓ = (cn : ℝ) / cd - 2 / (9 * (m1 : ℝ)) := ⟨_, rfl⟩
  have hℓpos : 0 < ℓ := by rw [hℓ]; linarith
  obtain ⟨α, hα⟩ : ∃ α : ℝ, α = (m2 : ℝ) * 4 / 3 := ⟨_, rfl⟩
  have hαpos : 0 < α := by rw [hα]; positivity
  have hXI : 2 * (2 / 9 : ℝ) * (1 + 2 * (2 / 9)) < α * ℓ * (1 - 2 * (2 / 9)) := by
    have hI' : (39 : ℝ) * m1 * cd < 5 * m2 * (9 * m1 * cn - 2 * cd) := by
      have h1 : ((39 * m1 * cd : ℕ) : ℝ) < ((5 * m2 * (9 * m1 * cn - 2 * cd) : ℕ) : ℝ) := by
        exact_mod_cast hI
      have hs : ((9 * m1 * cn - 2 * cd : ℕ) : ℝ) = 9 * (m1 : ℝ) * cn - 2 * cd := by
        rw [Nat.cast_sub hpos.le]; push_cast; ring
      push_cast [hs] at h1
      linarith
    have hdiff : α * ℓ * (1 - 2 * (2 / 9)) - 2 * (2 / 9) * (1 + 2 * (2 / 9)) =
        (20 * (m2 : ℝ) * (9 * m1 * cn - 2 * cd) - 156 * m1 * cd) / (243 * m1 * cd) := by
      rw [hα, hℓ]
      field_simp
      try ring
    have : 0 < α * ℓ * (1 - 2 * (2 / 9)) - 2 * (2 / 9) * (1 + 2 * (2 / 9)) := by
      rw [hdiff]
      exact div_pos (by linarith) (by positivity)
    linarith
  have hfin : (α * ℓ + 2 * (2 / 9 : ℝ) + 1) * (2 * (2 / 9) / α) < ℓ := by
    have e : (α * ℓ + 2 * (2 / 9 : ℝ) + 1) * (2 * (2 / 9) / α) =
        ((α * ℓ + 2 * (2 / 9 : ℝ) + 1) * (2 * (2 / 9))) / α := by ring
    rw [e, div_lt_iff₀ hαpos]
    nlinarith
  obtain ⟨η, hη1, hη2, hB⟩ := good_eta_piece (τ := 2 / 9) (y1 := 2 / (9 * (m1 : ℝ))) (ℓ := ℓ)
    (α := α) (x0 := (m2 : ℝ) / 3) (by norm_num) hℓpos hαpos hfin
  have hη2' : η ≤ (cn : ℝ) / cd := by rw [hℓ] at hη2; linarith
  have hη0 : 0 < η := lt_of_le_of_lt (by positivity) hη1
  have hEc : (3 : ℝ) * cn ≤ cd := by exact_mod_cast hE
  have hAc : (9 : ℝ) * m1 * cn ≤ 7 * cd := by exact_mod_cast hA
  refine n3_core η hη0.le ?_ ?_ (by rw [← hα]; exact hB)
  · have h4 : (cn : ℝ) / cd ≤ 1 / 3 := by
      rw [div_le_div_iff₀ hcdpos (by norm_num)]; linarith
    linarith
  · have h3 : (m1 : ℝ) * η ≤ (m1 : ℝ) * ((cn : ℝ) / cd) := mul_le_mul_of_nonneg_left hη2' hm1pos.le
    have h4 : (m1 : ℝ) * ((cn : ℝ) / cd) ≤ 7 / 9 := by
      have e : (m1 : ℝ) * ((cn : ℝ) / cd) = ((m1 : ℝ) * cn) / cd := by ring
      rw [e, div_le_div_iff₀ hcdpos (by norm_num)]; linarith
    have : 2 / (9 * (m1 : ℝ)) < η := hη1
    have h5 : (2 : ℝ) / 9 = (m1 : ℝ) * (2 / (9 * (m1 : ℝ))) := by field_simp
    apply nearestIntDist_ge
    · positivity
    · linarith
    · rw [h5]; exact mul_le_mul_of_nonneg_left this.le hm1pos.le
    · linarith

def S24ok (m1 m2 : ℕ) : Prop := S24P m1 m2 7 (9 * m2) ∨ S24P m1 m2 5 9
def S14ok (m1 m2 : ℕ) : Prop := S14P m1 m2 7 (9 * m1) ∨ S14P m1 m2 1 3
def expl4 (m1 m2 : ℕ) (L : List (ℕ × ℕ × ℕ)) : Prop :=
  ∃ c ∈ L, (c.1 = 2 ∧ chk24P m1 m2 c.2.1 c.2.2) ∨ (c.1 = 1 ∧ chk14P m1 m2 c.2.1 c.2.2)
def cov4P (L : List (ℕ × ℕ × ℕ)) (m1 m2 : ℕ) : Prop :=
  R14 m1 m2 ∨ S24ok m1 m2 ∨ S14ok m1 m2 ∨ expl4 m1 m2 L

instance (m1 m2 : ℕ) : Decidable (S24ok m1 m2) := by unfold S24ok; infer_instance
instance (m1 m2 : ℕ) : Decidable (S14ok m1 m2) := by unfold S14ok; infer_instance
instance (m1 m2 : ℕ) (L : List (ℕ × ℕ × ℕ)) : Decidable (expl4 m1 m2 L) := by
  unfold expl4; infer_instance
instance (L : List (ℕ × ℕ × ℕ)) (m1 m2 : ℕ) : Decidable (cov4P L m1 m2) := by
  unfold cov4P; infer_instance

theorem cov4_sound {m1 m2 : ℕ} (L : List (ℕ × ℕ × ℕ)) (hm1 : 1 ≤ m1) (hm2 : 1 ≤ m2)
    (h : cov4P L m1 m2) : 2 / 9 ≤ ML (v2Fam 3 3 4 m1 m2) := by
  rcases h with h | h | h | h
  · exact R14_sound hm1 hm2 h
  · rcases h with h | h
    · exact S24_sound hm1 hm2 h
    · exact S24_sound hm1 hm2 h
  · rcases h with h | h
    · exact S14_sound hm1 hm2 h
    · exact S14_sound hm1 hm2 h
  · obtain ⟨c, _, h | h⟩ := h
    · exact chk24_sound h.2
    · exact chk14_sound h.2

theorem R14_mono_m1 {m1 m1' m2 : ℕ} (h : R14 m1 m2) (hm : m1 ≤ m1') : R14 m1' m2 := by
  unfold R14 at *
  have := lin_mono (a := 78) (b := 208) (c := 15) (x := m1) (x' := m1') (y := m2) (by nlinarith [h]) hm
  nlinarith [this]

theorem R14_mono_m2 {m1 m2 m2' : ℕ} (h : R14 m1 m2) (hm : m2 ≤ m2') : R14 m1 m2' := by
  unfold R14 at *
  have := lin_mono (a := 208) (b := 78) (c := 15) (x := m2) (x' := m2') (y := m1) (by nlinarith [h]) hm
  nlinarith [this]

theorem S24P_mono {m1 m1' m2 cn cd : ℕ} (h : S24P m1 m2 cn cd) (hm : m1 ≤ m1') :
    S24P m1' m2 cn cd := by
  obtain ⟨a, b, c, d, e⟩ := h
  refine ⟨a, b, c, d, lt_of_lt_of_le e ?_⟩
  exact Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ hm)

theorem S14P_mono {m1 m2 m2' cn cd : ℕ} (h : S14P m1 m2 cn cd) (hm : m2 ≤ m2') :
    S14P m1 m2' cn cd := by
  obtain ⟨a, b, c, d, e⟩ := h
  refine ⟨a, b, c, d, lt_of_lt_of_le e ?_⟩
  exact Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ hm)

theorem S24ok_mono {m1 m1' m2 : ℕ} (h : S24ok m1 m2) (hm : m1 ≤ m1') : S24ok m1' m2 := by
  rcases h with h | h
  · exact Or.inl (S24P_mono h hm)
  · exact Or.inr (S24P_mono h hm)

theorem S14ok_mono {m1 m2 m2' : ℕ} (h : S14ok m1 m2) (hm : m2 ≤ m2') : S14ok m1 m2' := by
  rcases h with h | h
  · exact Or.inl (S14P_mono h hm)
  · exact Or.inr (S14P_mono h hm)

theorem cover4_all {P Q : ℕ} (L : List (ℕ × ℕ × ℕ))
    (hT1 : R14 P Q)
    (hT2 : ∀ m2, m2 < Q → 3 ≤ m2 → R14 P m2 ∨ S24ok P m2)
    (hT3 : ∀ m1, m1 < P → 4 ≤ m1 → R14 m1 Q ∨ S14ok m1 Q)
    (hbox : ∀ m1, m1 < P → 4 ≤ m1 → ∀ m2, m2 < Q → 3 ≤ m2 → cov4P L m1 m2) :
    ∀ m1 m2, 4 ≤ m1 → 3 ≤ m2 → cov4P L m1 m2 := by
  intro m1 m2 hm1 hm2
  by_cases h1 : m1 < P
  · by_cases h2 : m2 < Q
    · exact hbox m1 h1 hm1 m2 h2 hm2
    · have hQ : Q ≤ m2 := by omega
      rcases hT3 m1 h1 hm1 with h | h
      · exact Or.inl (R14_mono_m2 h hQ)
      · exact Or.inr (Or.inr (Or.inl (S14ok_mono h hQ)))
  · have hP : P ≤ m1 := by omega
    by_cases h2 : m2 < Q
    · rcases hT2 m2 h2 hm2 with h | h
      · exact Or.inl (R14_mono_m1 h hP)
      · exact Or.inr (Or.inl (S24ok_mono h hP))
    · have hQ : Q ≤ m2 := by omega
      exact Or.inl (R14_mono_m2 (R14_mono_m1 hT1 hP) hQ)

theorem theoremC_four_II {m1 m2 : ℕ} (hm1 : 4 ≤ m1) (hm2 : 3 ≤ m2) :
    2 / 9 ≤ ML (v2Fam 3 3 4 m1 m2) := by
  have h := cover4_all (P := 28) (Q := 27) ([(1, 2, 9), (2, 1, 13), (1, 5, 31), (2, 1, 18), (2, 1, 4), (2, 1, 6)] : List (ℕ × ℕ × ℕ))
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) m1 m2 hm1 hm2
  exact cov4_sound ([(1, 2, 9), (2, 1, 13), (1, 5, 31), (2, 1, 18), (2, 1, 4), (2, 1, 6)] : List (ℕ × ℕ × ℕ)) (by omega) (by omega) h

/-- **Theorem C at `N = 4`**: `2/9 ≤ ML (({1,2}) ∪ {3 m1, 4 m2})` for all `m1, m2 ≥ 2`. -/
theorem theoremC_four {m1 m2 : ℕ} (hm1 : 2 ≤ m1) (hm2 : 2 ≤ m2) :
    2 / 9 ≤ ML (v2Fam 3 3 4 m1 m2) := by
  by_cases h1 : m1 + 1 ≤ 4
  · have h := caseI_ML (k := 3) (N := 4) (r1 := 3) (r2 := 4) (m1 := m1) (m2 := m2) rfl
      (by norm_num) (by norm_num) (by norm_num) (by decide) hm1 hm2 h1
    have h' : (2 : ℝ) / 9 ≤ 1 / ((4 : ℕ) : ℝ) := by norm_num
    exact h'.trans h
  · by_cases h2 : m2 + 1 ≤ 3
    · have h := caseI'_ML (k := 3) (N := 4) (r1 := 3) (r2 := 4) (m1 := m1) (m2 := m2) rfl
        (by norm_num) (by norm_num) (by norm_num) (by decide) hm1 hm2 h2
      have h' : (2 : ℝ) / 9 ≤ 1 / ((4 : ℕ) : ℝ) := by norm_num
      exact h'.trans h
    · exact theoremC_four_II (by omega) (by omega)

end Gap
end Sext6
end LRSpectrumFull
