import LRSpectrumFull.Sext6.Gap.OELow

/-!
# Theorem OE-low, the four exceptional sets at `N = 14`  [2026-11-24]

`V = [14]_{6 → w}` for `w ∈ {69, 75, 144, 431}` is settled by neither the witness lemma nor Lemma L.
An explicit rational time `t = p/q` with every `‖v t‖ ≥ c/q ≥ 1/14` settles it, by exact integer residues:

| w   | t = p/q  | c  | c/q     |
|-----|----------|----|---------|
| 69  | 7/40     | 3  | 3/40    |
| 75  | 15/86    | 7  | 7/86    |
| 144 | 27/155   | 12 | 12/155  |
| 431 | 77/443   | 32 | 32/443  |

* `nid_rat_ge`  : `c ≤ z mod q`, `c ≤ q - z mod q` ⟹ `c/q ≤ ‖z/q‖`.
* `ML_ge_rat`   : the same for `ML v` at `t = p/q`.
* `ML_ge_inv_exc14` : `1/14 ≤ ML (wFam 13 6 w)` for the four values of `w`.
No `sorry`, no `axiom`.

Convention: `N = k + 1` is the number of entries (speeds) of the one-entry vector `wFam k r w = ([1,N] \ {r}) ∪ {w}`. Speeds are the moving runners; the runner at rest is not counted, so a vector of `N` speeds means `N + 1` runners and the Lonely Runner value is `1/(N+1)`.
Hypotheses: those of the individual statements (numerical bounds, structural conditions and, where named in the list above, window predicates such as `PrimeWin`, `CopWin`, `PrimeWindow7`, which later modules discharge for explicit ranges). The unproved predicates `DusartPi`, `LRCHyp`, `CopWinHyp` are not hypotheses of any statement in this module.
Axiom audit: covered by `Axioms6` (first); every later audit module imports this module (`#print axioms`; declarations not printed there are bricks of printed ones, so their axioms are bounded by the printed lines).
-/

namespace LRSpectrumFull
namespace Sext6
namespace Gap

theorem nid_rat_ge {q c : ℕ} (hq : 0 < q) (z : ℤ) (h1 : (c : ℤ) ≤ z % (q : ℤ))
    (h2 : (c : ℤ) ≤ (q : ℤ) - z % (q : ℤ)) : (c : ℝ) / q ≤ nearestIntDist ((z : ℝ) / q) := by
  apply nid_div_ge hq z c
  intro n
  have hqz : (0 : ℤ) < q := by exact_mod_cast hq
  have hz := Int.ediv_add_emod z (q : ℤ)
  obtain ⟨ρ, hρ⟩ : ∃ ρ, ρ = z % (q : ℤ) := ⟨_, rfl⟩
  obtain ⟨u, hu⟩ : ∃ u, u = z / (q : ℤ) := ⟨_, rfl⟩
  rw [← hρ] at h1 h2 hz
  rw [← hu] at hz
  have e : z - n * (q : ℤ) = ρ + (q : ℤ) * (u - n) := by linarith
  rw [e]
  rcases le_or_gt 0 (u - n) with hj | hj
  · have hp : 0 ≤ (q : ℤ) * (u - n) := mul_nonneg hqz.le hj
    have hc0 : (0 : ℤ) ≤ c := by positivity
    rw [abs_of_nonneg (by linarith)]
    linarith
  · have hqj : (q : ℤ) * (u - n) ≤ (q : ℤ) * (-1) :=
      mul_le_mul_of_nonneg_left (by omega) hqz.le
    have hc0 : (0 : ℤ) ≤ c := by positivity
    rw [abs_of_nonpos (by linarith)]
    linarith

theorem ML_ge_rat {k : ℕ} (v : Fin (k + 1) → ℤ) (p q c N : ℕ) (hq : 0 < q)
    (hcq : 1 / (N : ℝ) ≤ (c : ℝ) / q)
    (h : ∀ i, (c : ℤ) ≤ ((p : ℤ) * v i) % (q : ℤ) ∧ (c : ℤ) ≤ (q : ℤ) - ((p : ℤ) * v i) % (q : ℤ)) :
    1 / (N : ℝ) ≤ ML v := by
  refine ML_ge_of_far v (1 / (N : ℝ)) ((p : ℝ) / q) ?_
  intro i
  have e : (v i : ℝ) * ((p : ℝ) / q) = ((((p : ℤ) * v i : ℤ)) : ℝ) / q := by
    push_cast; ring
  rw [e]
  exact hcq.trans (nid_rat_ge hq _ (h i).1 (h i).2)

theorem ML_ge_inv_exc14 {w : ℕ} (hw : w = 69 ∨ w = 75 ∨ w = 144 ∨ w = 431) :
    1 / ((14 : ℕ) : ℝ) ≤ ML (wFam 13 6 w) := by
  rcases hw with rfl | rfl | rfl | rfl
  · exact ML_ge_rat (wFam 13 6 69) 7 40 3 14 (by norm_num) (by norm_num) (by decide +kernel)
  · exact ML_ge_rat (wFam 13 6 75) 15 86 7 14 (by norm_num) (by norm_num) (by decide +kernel)
  · exact ML_ge_rat (wFam 13 6 144) 27 155 12 14 (by norm_num) (by norm_num) (by decide +kernel)
  · exact ML_ge_rat (wFam 13 6 431) 77 443 32 14 (by norm_num) (by norm_num) (by decide +kernel)

end Gap
end Sext6
end LRSpectrumFull
