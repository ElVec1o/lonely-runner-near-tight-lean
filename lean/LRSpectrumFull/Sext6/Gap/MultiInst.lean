import LRSpectrumFull.Sext6.Gap.MultiLower

/-!
# Multi-entry value theorem: two instances  [2026-11-24]

* `N = 73`, `R = {70, 72}`, `m = 2`: `ML = 1/74` (a tight two-entry set, `gcd(70,72) = 2`).
* `N = 13`, `R = {12, 10}`, `m 12 = 3`, `m 10 = 2`: `ML = 2/27`, the value of the witness at the entry `10`.
No `sorry`, no `axiom`.

Convention: `N` is the size of the ambient interval `[1,N]`; the speed vector `v : Fin (k+1) → ℤ` is a finite family (repetitions allowed) and `k`, `N` are independent parameters of the generic statements. Speeds are the moving runners; the runner at rest is not counted, so a vector of `N` speeds means `N + 1` runners and the Lonely Runner value is `1/(N+1)`.
Hypotheses: those of the individual statements (numerical bounds, structural conditions and, where named in the list above, window predicates such as `PrimeWin`, `CopWin`, `PrimeWindow7`, which later modules discharge for explicit ranges). The unproved predicates `DusartPi`, `LRCHyp`, `CopWinHyp` are not hypotheses of any statement in this module.
Axiom audit: covered by `MultiAxioms` (also reached through the imports of `Axioms8`) (`#print axioms`; declarations not printed there are bricks of printed ones, so their axioms are bounded by the printed lines).
-/

namespace LRSpectrumFull
namespace Sext6
namespace Gap

/-- The speed vector `([1,N] \ {r1, r2}) ∪ {m1 r1, m2 r2}` on `k + 1` slots (`N = k + 1`). -/
def v2Fam (k r1 r2 m1 m2 : ℕ) : Fin (k + 1) → ℤ := fun i =>
  if (i : ℕ) + 1 = r1 then ((m1 * r1 : ℕ) : ℤ)
  else if (i : ℕ) + 1 = r2 then ((m2 * r2 : ℕ) : ℤ) else (((i : ℕ) + 1 : ℕ) : ℤ)

theorem v2Fam_ret {k r1 r2 m1 m2 : ℕ} (x : ℕ) (hx1 : 1 ≤ x) (hxN : x ≤ k + 1)
    (hx : x ≠ r1 ∧ x ≠ r2) : ∃ i, v2Fam k r1 r2 m1 m2 i = (x : ℤ) := by
  refine ⟨⟨x - 1, by omega⟩, ?_⟩
  have h : x - 1 + 1 = x := by omega
  simp only [v2Fam, h]
  rw [if_neg hx.1, if_neg hx.2]

theorem v2Fam_within {k r1 r2 m1 m2 : ℕ} (R : Finset ℕ) (hR1 : r1 ∈ R) (hR2 : r2 ∈ R)
    (hR : ∀ x, x ∈ R → x = r1 ∨ x = r2) (m : ℕ → ℕ) (hm1 : m r1 = m1) (hm2 : m r2 = m2) :
    WithinMulti (k + 1) R m (v2Fam k r1 r2 m1 m2) := by
  intro i
  unfold v2Fam
  by_cases h1 : (i : ℕ) + 1 = r1
  · right
    refine ⟨r1, hR1, ?_⟩
    rw [if_pos h1, hm1]
  · by_cases h2 : (i : ℕ) + 1 = r2
    · right
      refine ⟨r2, hR2, ?_⟩
      rw [if_neg h1, if_pos h2, hm2]
    · left
      refine ⟨(i : ℕ) + 1, by omega, by have := i.isLt; omega, ?_, ?_⟩
      · intro hmem
        rcases hR _ hmem with h | h
        · exact h1 h
        · exact h2 h
      · rw [if_neg h1, if_neg h2]

theorem spec_73_70 : Spec 73 70 2 9 := by
  refine ⟨by norm_num, by norm_num, by norm_num, le_rfl, by norm_num, by decide, ?_⟩
  intro b hb hcop
  by_contra hlt
  have hb4 : 4 ≤ b := by omega
  have hb9 : b < 9 := by omega
  interval_cases b <;> exact absurd hcop (by decide)

theorem spec_73_72 : Spec 73 72 2 5 := by
  refine ⟨by norm_num, by norm_num, by norm_num, le_rfl, by norm_num, by decide, ?_⟩
  intro b hb hcop
  by_contra hlt
  have hb2 : 2 ≤ b := by omega
  have hb5 : b < 5 := by omega
  interval_cases b <;> exact absurd hcop (by decide)

/-- `N = 73`, `R = {70, 72}`, `m = 2`: `ML = 1/74`. -/
theorem inst_73_70_72 : ML (v2Fam 72 70 72 2 2) = 1 / 74 := by
  have h := multi_value_tight (k := 72) (N := 73) (by norm_num) ({70, 72} : Finset ℕ)
    (fun _ => 2) (fun r => if r = 70 then 9 else 5)
    (by
      intro r hr
      simp only [Finset.mem_insert, Finset.mem_singleton] at hr
      rcases hr with rfl | rfl
      · simpa using spec_73_70
      · simpa using spec_73_72)
    (by
      intro r hr r' hr' hne
      simp only [Finset.mem_insert, Finset.mem_singleton] at hr hr'
      rcases hr with rfl | rfl <;> rcases hr' with rfl | rfl <;> first | exact absurd rfl hne | decide)
    (v2Fam 72 70 72 2 2)
    (by
      intro x hx1 hxN hxR
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hxR
      exact v2Fam_ret x hx1 hxN hxR)
    (by
      intro r hr
      simp only [Finset.mem_insert, Finset.mem_singleton] at hr
      rcases hr with rfl | rfl
      · refine ⟨⟨69, by norm_num⟩, ?_⟩
        simp [v2Fam]
      · refine ⟨⟨71, by norm_num⟩, ?_⟩
        simp [v2Fam])
    (v2Fam_within (k := 72) _ (by simp) (by simp)
      (by intro x hx; simpa using hx) (fun _ => 2) rfl rfl)
    (by
      intro r hr
      simp only [Finset.mem_insert, Finset.mem_singleton] at hr
      rcases hr with rfl | rfl <;> norm_num)
    (by
      intro r hr
      simp only [Finset.mem_insert, Finset.mem_singleton] at hr
      rcases hr with rfl | rfl <;> decide)
  rw [h]
  norm_num

theorem spec_13_12 : Spec 13 12 3 5 := by
  refine ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by decide, ?_⟩
  intro b hb hcop
  by_contra hlt
  have hb2 : 2 ≤ b := by omega
  have hb5 : b < 5 := by omega
  interval_cases b <;> exact absurd hcop (by decide)

theorem spec_13_10 : Spec 13 10 2 7 := by
  refine ⟨by norm_num, by norm_num, by norm_num, le_rfl, by norm_num, by decide, ?_⟩
  intro b hb hcop
  by_contra hlt
  have hb4 : 4 ≤ b := by omega
  have hb7 : b < 7 := by omega
  interval_cases b <;> exact absurd hcop (by decide)

/-- `N = 13`, `R = {12, 10}`, `m 12 = 3`, `m 10 = 2`: `ML = 2/27` (witness at the entry `10`, `a = 8`). -/
theorem inst_13_12_10 : ML (v2Fam 12 12 10 3 2) = 2 / 27 := by
  have h := multi_value_wit (k := 12) (N := 13) (by norm_num) ({12, 10} : Finset ℕ)
    (fun r => if r = 12 then 3 else 2) (fun r => if r = 12 then 5 else 7)
    (by
      intro r hr
      simp only [Finset.mem_insert, Finset.mem_singleton] at hr
      rcases hr with rfl | rfl
      · simpa using spec_13_12
      · simpa using spec_13_10)
    (by
      intro r hr r' hr' hne
      simp only [Finset.mem_insert, Finset.mem_singleton] at hr hr'
      rcases hr with rfl | rfl <;> rcases hr' with rfl | rfl <;> first | exact absurd rfl hne | decide)
    (v2Fam 12 12 10 3 2)
    (by
      intro x hx1 hxN hxR
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hxR
      exact v2Fam_ret x hx1 hxN hxR)
    (by
      intro r hr
      simp only [Finset.mem_insert, Finset.mem_singleton] at hr
      rcases hr with rfl | rfl
      · refine ⟨⟨11, by norm_num⟩, ?_⟩
        simp [v2Fam]
      · refine ⟨⟨9, by norm_num⟩, ?_⟩
        simp [v2Fam])
    (v2Fam_within (k := 12) _ (by simp) (by simp)
      (by intro x hx; simpa using hx) (fun r => if r = 12 then 3 else 2) (by simp) (by simp))
    10 (by simp)
    (by norm_num)
    (by
      intro r hr
      simp only [Finset.mem_insert, Finset.mem_singleton] at hr
      rcases hr with rfl | rfl <;> norm_num)
    8 3 (by norm_num)
    (by
      intro r' hr' hne n
      simp only [Finset.mem_insert, Finset.mem_singleton] at hr'
      rcases hr' with rfl | rfl
      · by_contra hcon
        push Not at hcon
        norm_num at hcon
        rw [abs_lt] at hcon
        omega
      · exact absurd rfl hne)
  rw [h]
  norm_num

end Gap
end Sext6
end LRSpectrumFull
