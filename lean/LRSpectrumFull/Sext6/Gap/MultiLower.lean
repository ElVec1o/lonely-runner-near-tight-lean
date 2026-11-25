import LRSpectrumFull.Sext6.Gap.MultiUpper

/-!
# Multi-entry value theorem: lower bounds (witness times) and the value  [2026-11-24]

* `multi_ML_ge_B` : witness time `a/D`, `D = m r + β`, `a r ≡ -1 (mod D)`, for one entry `r ∈ R`:
   every retained speed is at distance `≥ m r / D`, the speed `m r * r` at distance `m r / D`, and every other new
   speed `m r' * r'` at distance `≥ m r / D` iff the residue hypothesis `hW` holds.
* `multi_ML_ge_A` : witness time `1/(N+1)`: needs `(N+1) ∤ m r' * r'` for all `r' ∈ R`.
* `multi_value_tight`, `multi_value_wit` : the value `ML v` (sufficient criterion of the accompanying notes Theorem M2).
No `sorry`, no `axiom`.

Convention: `N` is the size of the ambient interval `[1,N]`; the speed vector `v : Fin (k+1) → ℤ` is a finite family (repetitions allowed) and `k`, `N` are independent parameters of the generic statements. Speeds are the moving runners; the runner at rest is not counted, so a vector of `N` speeds means `N + 1` runners and the Lonely Runner value is `1/(N+1)`.
Hypotheses: those of the individual statements (numerical bounds, structural conditions and, where named in the list above, window predicates such as `PrimeWin`, `CopWin`, `PrimeWindow7`, which later modules discharge for explicit ranges). The unproved predicates `DusartPi`, `LRCHyp`, `CopWinHyp` are not hypotheses of any statement in this module.
Axiom audit: covered by `MultiAxioms` (also reached through the imports of `Axioms8`) (`#print axioms`; declarations not printed there are bricks of printed ones, so their axioms are bounded by the printed lines).
-/

namespace LRSpectrumFull
namespace Sext6
namespace Gap

/-- A speed vector all of whose entries are retained speeds (`[1,N] \ R`) or new speeds `m r' * r'`. -/
def WithinMulti {k : ℕ} (N : ℕ) (R : Finset ℕ) (m : ℕ → ℕ) (v : Fin (k + 1) → ℤ) : Prop :=
  ∀ i, (∃ x : ℕ, 1 ≤ x ∧ x ≤ N ∧ x ∉ R ∧ v i = (x : ℤ)) ∨ ∃ r' ∈ R, v i = ((m r' * r' : ℕ) : ℤ)

theorem multi_ML_ge_B {k N : ℕ} (R : Finset ℕ) (m β : ℕ → ℕ) (r : ℕ) (hr : r ∈ R)
    (hS : Spec N r (m r) (β r)) (v : Fin (k + 1) → ℤ) (hwith : WithinMulti N R m v)
    (a c : ℤ) (hD : a * r + 1 = c * ((m r * r + β r : ℕ) : ℤ))
    (hW : ∀ r' ∈ R, r' ≠ r → ∀ n : ℤ,
      (m r : ℤ) ≤ |a * ((m r' * r' : ℕ) : ℤ) - n * ((m r * r + β r : ℕ) : ℤ)|) :
    (m r : ℝ) / ((m r * r + β r : ℕ) : ℝ) ≤ ML v := by
  have hbpos := hS.beta_pos
  have hrr := hS.two_le_r
  have hDpos : 0 < m r * r + β r := by omega
  apply ML_ge_of_far v _ ((a : ℝ) / ((m r * r + β r : ℕ) : ℝ))
  intro i
  rcases hwith i with ⟨x, hx1, hxN, hxR, hvx⟩ | ⟨r', hr', hvr⟩
  · have hxr : x ≠ r := by
      intro h
      apply hxR
      rw [h]
      exact hr
    have e : ((v i : ℤ) : ℝ) * ((a : ℝ) / ((m r * r + β r : ℕ) : ℝ)) =
        ((a * (x : ℤ) : ℤ) : ℝ) / ((m r * r + β r : ℕ) : ℝ) := by
      rw [hvx]; push_cast; ring
    rw [e]
    exact nid_div_ge hDpos _ (m r) (fun n => lowerA_int hS a c hD x hx1 hxN hxr n)
  · have e : ((v i : ℤ) : ℝ) * ((a : ℝ) / ((m r * r + β r : ℕ) : ℝ)) =
        ((a * ((m r' * r' : ℕ) : ℤ) : ℤ) : ℝ) / ((m r * r + β r : ℕ) : ℝ) := by
      rw [hvr]; push_cast; ring
    rw [e]
    by_cases hrr' : r' = r
    · subst hrr'
      exact nid_div_ge hDpos _ (m r') (fun n => lowerA_speed hS a c hD n)
    · exact nid_div_ge hDpos _ (m r) (fun n => hW r' hr' hrr' n)

theorem multi_ML_ge_A {k N : ℕ} (R : Finset ℕ) (m : ℕ → ℕ) (hN : 1 ≤ N)
    (v : Fin (k + 1) → ℤ) (hwith : WithinMulti N R m v)
    (hndv : ∀ r' ∈ R, ¬ (((N + 1 : ℕ) : ℤ) ∣ ((m r' * r' : ℕ) : ℤ))) :
    1 / ((N : ℝ) + 1) ≤ ML v := by
  have hpos : 0 < N + 1 := by omega
  have hc : 1 / ((N : ℝ) + 1) = ((1 : ℕ) : ℝ) / ((N + 1 : ℕ) : ℝ) := by push_cast; ring
  rw [hc]
  apply ML_ge_of_far v _ (((1 : ℤ) : ℝ) / ((N + 1 : ℕ) : ℝ))
  intro i
  rcases hwith i with ⟨x, hx1, hxN, hxR, hvx⟩ | ⟨r', hr', hvr⟩
  · have e : ((v i : ℤ) : ℝ) * (((1 : ℤ) : ℝ) / ((N + 1 : ℕ) : ℝ)) =
        ((((x : ℤ)) : ℤ) : ℝ) / ((N + 1 : ℕ) : ℝ) := by
      rw [hvx]; push_cast; ring
    rw [e]
    apply nid_div_ge hpos
    apply far_of_not_dvd
    intro hd
    have := Int.le_of_dvd (by exact_mod_cast hx1) hd
    have h3 : (x : ℤ) ≤ N := by exact_mod_cast hxN
    push_cast at this
    omega
  · have e : ((v i : ℤ) : ℝ) * (((1 : ℤ) : ℝ) / ((N + 1 : ℕ) : ℝ)) =
        ((((m r' * r' : ℕ) : ℤ)) : ℝ) / ((N + 1 : ℕ) : ℝ) := by
      rw [hvr]; push_cast; ring
    rw [e]
    apply nid_div_ge hpos
    apply far_of_not_dvd
    exact hndv r' hr'

/-- Value: tight case.  If every `m r / (m r * r + β r) ≤ 1/(N+1)` and `(N+1) ∤ m r * r` for all `r ∈ R`
then `ML v = 1/(N+1)`. -/
theorem multi_value_tight {k N : ℕ} (hN : 2 ≤ N) (R : Finset ℕ) (m β : ℕ → ℕ)
    (hS : ∀ r ∈ R, Spec N r (m r) (β r))
    (hG : ∀ r ∈ R, ∀ r' ∈ R, r' ≠ r → ¬ Nat.Coprime r' r)
    (v : Fin (k + 1) → ℤ)
    (hret : ∀ x : ℕ, 1 ≤ x → x ≤ N → x ∉ R → ∃ i, v i = (x : ℤ))
    (hnew : ∀ r ∈ R, ∃ i, v i = ((m r * r : ℕ) : ℤ))
    (hwith : WithinMulti N R m v)
    (htight : ∀ r ∈ R, (m r : ℝ) / ((m r * r + β r : ℕ) : ℝ) ≤ 1 / ((N : ℝ) + 1))
    (hndv : ∀ r' ∈ R, ¬ (((N + 1 : ℕ) : ℤ) ∣ ((m r' * r' : ℕ) : ℤ))) :
    ML v = 1 / ((N : ℝ) + 1) :=
  le_antisymm (multi_ML_le hN R m β hS hG v hret hnew _ le_rfl htight)
    (multi_ML_ge_A R m (by omega) v hwith hndv)

/-- Value: non-tight witness case.  Let `r0 ∈ R` with `τ := m r0 / (m r0 * r0 + β r0)` the maximum of
`1/(N+1)` and all `m r / (m r * r + β r)`, and suppose the witness residue condition `hW` holds for `r0`.
Then `ML v = τ`. -/
theorem multi_value_wit {k N : ℕ} (hN : 2 ≤ N) (R : Finset ℕ) (m β : ℕ → ℕ)
    (hS : ∀ r ∈ R, Spec N r (m r) (β r))
    (hG : ∀ r ∈ R, ∀ r' ∈ R, r' ≠ r → ¬ Nat.Coprime r' r)
    (v : Fin (k + 1) → ℤ)
    (hret : ∀ x : ℕ, 1 ≤ x → x ≤ N → x ∉ R → ∃ i, v i = (x : ℤ))
    (hnew : ∀ r ∈ R, ∃ i, v i = ((m r * r : ℕ) : ℤ))
    (hwith : WithinMulti N R m v)
    (r0 : ℕ) (hr0 : r0 ∈ R)
    (h1 : 1 / ((N : ℝ) + 1) ≤ (m r0 : ℝ) / ((m r0 * r0 + β r0 : ℕ) : ℝ))
    (h2 : ∀ r ∈ R, (m r : ℝ) / ((m r * r + β r : ℕ) : ℝ) ≤ (m r0 : ℝ) / ((m r0 * r0 + β r0 : ℕ) : ℝ))
    (a c : ℤ) (hD : a * r0 + 1 = c * ((m r0 * r0 + β r0 : ℕ) : ℤ))
    (hW : ∀ r' ∈ R, r' ≠ r0 → ∀ n : ℤ,
      (m r0 : ℤ) ≤ |a * ((m r' * r' : ℕ) : ℤ) - n * ((m r0 * r0 + β r0 : ℕ) : ℤ)|) :
    ML v = (m r0 : ℝ) / ((m r0 * r0 + β r0 : ℕ) : ℝ) :=
  le_antisymm (multi_ML_le hN R m β hS hG v hret hnew _ h1 h2)
    (multi_ML_ge_B R m β r0 hr0 (hS r0 hr0) v hwith a c hD hW)

end Gap
end Sext6
end LRSpectrumFull
