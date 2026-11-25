import LRSpectrumFull.Sext6.Gap.MultiBridge

/-!
# Witness lemma (R1): a rational time `a/D` with `a r ≡ 1 (mod D)`  [2026-11-24]

Source: an accompanying exact search tool (mode `one`: witness test
"`D ∈ [N+1+r, 2N+1]`, `gcd(D,r)=1`, `w r⁻¹ mod D ∉ {0,±1}`") and Zhang's Thm 2.9 shape.

* `ML_ge_witness`      : for ANY speed vector `v : Fin (k+1) → ℤ`, any `D > 0` and any `r` coprime to `D`:
  if no entry of `v` is `≡ 0, +r, -r (mod D)` then `2/D ≤ ML v`.  (At `t = a/D`, `a r ≡ 1`, the entry `x`
  sits at `a x mod D`, which lies in `{0, ±1}` exactly when `x ≡ 0, ±r`.)
* `ML_ge_inv_of_witness`: if moreover `D ≤ 2 N` (`N = k + 1` entries) then `1/N ≤ ML v`.
* `wFam k r w`         : the one-entry family `([1,N] \ {r}) ∪ {w}` (index `i` carries `i+1`, except index
  `r-1`, which carries `w`).  `vFam k r m = wFam k r (m*r)`.
* `ML_ge_two_div_fam`  : for `wFam k r w`, the retained speeds satisfy the congruence hypotheses
  automatically as soon as `D ≥ N + 1 + r`; only the inserted speed `w` needs `w ≢ 0, ±r (mod D)`.
* `ML_ge_inv_fam`      : and `D ≤ 2N` gives `ML ≥ 1/N`.
No `sorry`, no `axiom`.

Convention: `N = k + 1` is the number of speeds of the vector `v : Fin (k+1) → ℤ`. Speeds are the moving runners; the runner at rest is not counted, so a vector of `N` speeds means `N + 1` runners and the Lonely Runner value is `1/(N+1)`.
Hypotheses: For `ML_ge_witness`: any speed vector, `0 < D`, `r` coprime to `D`, and no entry `≡ 0, ±r (mod D)`; the family statements add `k + 1 = N` and `D ≥ N + 1 + r`. The unproved predicates `DusartPi`, `LRCHyp`, `CopWinHyp` do not occur.
Axiom audit: covered by `Axioms4` (first); every later audit module imports this module (`#print axioms`; declarations not printed there are bricks of printed ones, so their axioms are bounded by the printed lines).
-/

namespace LRSpectrumFull
namespace Sext6
namespace Gap

/-- **Witness lemma** (general form).  `v` any speed vector, `D > 0`, `r` coprime to `D`.  If no entry `x`
of `v` satisfies `D ∣ x`, `D ∣ x - r` or `D ∣ x + r`, then `2 / D ≤ ML v`. -/
theorem ML_ge_witness {k : ℕ} (v : Fin (k + 1) → ℤ) (D : ℕ) (r : ℤ) (hD : 0 < D)
    (hcop : IsCoprime r (D : ℤ))
    (h : ∀ i, ¬ ((D : ℤ) ∣ v i) ∧ ¬ ((D : ℤ) ∣ v i - r) ∧ ¬ ((D : ℤ) ∣ v i + r)) :
    2 / (D : ℝ) ≤ ML v := by
  obtain ⟨a, b, hab⟩ := hcop
  refine ML_ge_of_far v (2 / (D : ℝ)) ((a : ℝ) / D) ?_
  intro i
  obtain ⟨h0, h1, h2⟩ := h i
  have e : ((v i : ℤ) : ℝ) * ((a : ℝ) / D) = ((a * v i : ℤ) : ℝ) / D := by
    push_cast; ring
  have key : ((2 : ℕ) : ℝ) / (D : ℝ) ≤ nearestIntDist (((a * v i : ℤ) : ℝ) / D) := by
    apply nid_div_ge hD (a * v i) 2
    intro n
    by_contra hcon
    push Not at hcon
    have hc2 : |a * v i - n * (D : ℤ)| < 2 := by exact_mod_cast hcon
    obtain ⟨hlo, hhi⟩ := abs_lt.mp hc2
    obtain ⟨y, hy⟩ : ∃ y : ℤ, y = a * v i - n * (D : ℤ) := ⟨_, rfl⟩
    rw [← hy] at hlo hhi
    have hkey : v i - y * r = (D : ℤ) * (b * v i + n * r) := by
      rw [hy]
      linear_combination (-(v i)) * hab
    have hy3 : y = -1 ∨ y = 0 ∨ y = 1 := by omega
    rcases hy3 with hy' | hy' | hy'
    · rw [hy'] at hkey
      exact h2 ⟨b * v i + n * r, by linear_combination hkey⟩
    · rw [hy'] at hkey
      exact h0 ⟨b * v i + n * r, by linear_combination hkey⟩
    · rw [hy'] at hkey
      exact h1 ⟨b * v i + n * r, by linear_combination hkey⟩
  have h2c : ((2 : ℕ) : ℝ) = 2 := by norm_num
  rw [h2c] at key
  rw [e]
  exact key

/-- Corollary: with `N = k + 1` entries and `D ≤ 2 N`, a witness gives `1/N ≤ ML v`. -/
theorem ML_ge_inv_of_witness {k N : ℕ} (hk : k + 1 = N) (v : Fin (k + 1) → ℤ) (D : ℕ) (r : ℤ)
    (hD : 0 < D) (hcop : IsCoprime r (D : ℤ))
    (h : ∀ i, ¬ ((D : ℤ) ∣ v i) ∧ ¬ ((D : ℤ) ∣ v i - r) ∧ ¬ ((D : ℤ) ∣ v i + r))
    (hDN : D ≤ 2 * N) : 1 / (N : ℝ) ≤ ML v := by
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hDR : (0 : ℝ) < D := by exact_mod_cast hD
  have h1 : 1 / (N : ℝ) ≤ 2 / (D : ℝ) := by
    rw [div_le_div_iff₀ hNpos hDR]
    have : (D : ℝ) ≤ 2 * N := by exact_mod_cast hDN
    linarith
  exact h1.trans (ML_ge_witness v D r hD hcop h)

/-- The one-entry family `([1,N] \ {r}) ∪ {w}` on `N = k + 1` speeds: index `i` carries `i + 1`,
except index `r - 1`, which carries `w`. -/
def wFam (k r w : ℕ) : Fin (k + 1) → ℤ :=
  fun i => if (i : ℕ) + 1 = r then (w : ℤ) else (((i : ℕ) + 1 : ℕ) : ℤ)

theorem vFam_eq_wFam (k r m : ℕ) : vFam k r m = wFam k r (m * r) := by
  funext i
  rfl

theorem wFam_at_r {k r w : ℕ} (i : Fin (k + 1)) (hi : (i : ℕ) + 1 = r) :
    wFam k r w i = (w : ℤ) := by
  simp [wFam, hi]

theorem wFam_ne_r {k r w : ℕ} (i : Fin (k + 1)) (hi : ¬ ((i : ℕ) + 1 = r)) :
    wFam k r w i = (((i : ℕ) + 1 : ℕ) : ℤ) := by
  simp [wFam, hi]

/-- Every retained speed `x ∈ [1,N] \ {r}` is an entry of `wFam k r w`. -/
theorem wFam_retained {k N r w x : ℕ} (hk : k + 1 = N) (hx1 : 1 ≤ x) (hxN : x ≤ N)
    (hxr : x ≠ r) : ∃ i : Fin (k + 1), wFam k r w i = (x : ℤ) := by
  obtain ⟨i, hi'⟩ : ∃ i : Fin (k + 1), (i : ℕ) + 1 = x :=
    ⟨⟨x - 1, by omega⟩, by show x - 1 + 1 = x; omega⟩
  have hir : ¬ ((i : ℕ) + 1 = r) := by omega
  refine ⟨i, ?_⟩
  rw [wFam_ne_r i hir, hi']

/-- The retained speeds of `wFam` satisfy the witness congruence hypotheses as soon as `D ≥ N + 1 + r`;
the inserted speed `w` needs them as hypotheses. -/
theorem wFam_cond {k N r w D : ℕ} (hk : k + 1 = N) (hr1 : 1 ≤ r) (hr2 : r ≤ N)
    (hD : N + 1 + r ≤ D)
    (hw0 : ¬ ((D : ℤ) ∣ (w : ℤ))) (hw1 : ¬ ((D : ℤ) ∣ (w : ℤ) - (r : ℤ)))
    (hw2 : ¬ ((D : ℤ) ∣ (w : ℤ) + (r : ℤ))) (i : Fin (k + 1)) :
    ¬ ((D : ℤ) ∣ wFam k r w i) ∧ ¬ ((D : ℤ) ∣ wFam k r w i - (r : ℤ)) ∧
      ¬ ((D : ℤ) ∣ wFam k r w i + (r : ℤ)) := by
  by_cases hi : (i : ℕ) + 1 = r
  · rw [wFam_at_r i hi]
    exact ⟨hw0, hw1, hw2⟩
  · rw [wFam_ne_r i hi]
    have hiN : (i : ℕ) < k + 1 := i.isLt
    generalize hx : (i : ℕ) + 1 = x at hi ⊢
    have hx1 : 1 ≤ x := by omega
    have hxN : x ≤ N := by omega
    refine ⟨?_, ?_, ?_⟩
    · intro hd
      have := Int.eq_zero_of_abs_lt_dvd hd (abs_lt.mpr ⟨by omega, by omega⟩)
      omega
    · intro hd
      have := Int.eq_zero_of_abs_lt_dvd hd (abs_lt.mpr ⟨by omega, by omega⟩)
      omega
    · intro hd
      have := Int.eq_zero_of_abs_lt_dvd hd (abs_lt.mpr ⟨by omega, by omega⟩)
      omega

/-- **Witness lemma for `([1,N] \ {r}) ∪ {w}`.**  `D ≥ N + 1 + r`, `gcd(D, r) = 1`, and
`w ≢ 0, +r, -r (mod D)`; then `2/D ≤ ML`. -/
theorem ML_ge_two_div_fam {k N r w D : ℕ} (hk : k + 1 = N) (hr1 : 1 ≤ r) (hr2 : r ≤ N)
    (hD : N + 1 + r ≤ D) (hcop : Nat.Coprime D r)
    (hw0 : ¬ ((D : ℤ) ∣ (w : ℤ))) (hw1 : ¬ ((D : ℤ) ∣ (w : ℤ) - (r : ℤ)))
    (hw2 : ¬ ((D : ℤ) ∣ (w : ℤ) + (r : ℤ))) :
    2 / (D : ℝ) ≤ ML (wFam k r w) := by
  have hDpos : 0 < D := by omega
  have hc : IsCoprime (r : ℤ) (D : ℤ) := Nat.isCoprime_iff_coprime.mpr hcop.symm
  exact ML_ge_witness (wFam k r w) D (r : ℤ) hDpos hc
    (fun i => wFam_cond hk hr1 hr2 hD hw0 hw1 hw2 i)

/-- Corollary (2): if moreover `D ≤ 2 N` then `1/N ≤ ML`. -/
theorem ML_ge_inv_fam {k N r w D : ℕ} (hk : k + 1 = N) (hr1 : 1 ≤ r) (hr2 : r ≤ N)
    (hD : N + 1 + r ≤ D) (hDN : D ≤ 2 * N) (hcop : Nat.Coprime D r)
    (hw0 : ¬ ((D : ℤ) ∣ (w : ℤ))) (hw1 : ¬ ((D : ℤ) ∣ (w : ℤ) - (r : ℤ)))
    (hw2 : ¬ ((D : ℤ) ∣ (w : ℤ) + (r : ℤ))) :
    1 / (N : ℝ) ≤ ML (wFam k r w) := by
  have hDpos : 0 < D := by omega
  have hc : IsCoprime (r : ℤ) (D : ℤ) := Nat.isCoprime_iff_coprime.mpr hcop.symm
  exact ML_ge_inv_of_witness hk (wFam k r w) D (r : ℤ) hDpos hc
    (fun i => wFam_cond hk hr1 hr2 hD hw0 hw1 hw2 i) hDN

end Gap
end Sext6
end LRSpectrumFull
