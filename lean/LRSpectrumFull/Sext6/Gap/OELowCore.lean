import LRSpectrumFull.Sext6.Gap.Witness
import LRSpectrumFull.NearestIntLipschitz

/-!
# Theorem OE-low, Lemma L (large inserted speed)  [2026-11-24]

Source: the accompanying notes on Theorem OE section 3 (Lemma L) and section 7 (LR-5).

For `D` with `N + 1 + r ≤ D`, `gcd(D, r) = 1`, `D + E = 2N`, `E ≥ 1`, and `D N² ≤ 2 E w`:
at the time `t = (k + 1/2)/w` closest to `t₀ = a/D` (`a r ≡ 1 mod D`) the retained speeds keep
`‖x t‖ ≥ 2/D - N δ = 1/N` (`δ = E/(D N²)`), and the inserted speed sits at `‖w t‖ = 1/2`.

* `far_of_cond`       : the integer residue test at `t₀ = a/D` (the retained-speed half of the witness lemma,
                        exposed as a statement about one integer `z`).
* `retained_cond`     : retained speeds `x ∈ [1,N] \ {r}` satisfy the three non-divisibility conditions.
* `ML_ge_inv_large`   : Lemma L, for the one-entry family `wFam k r w`.
No `sorry`, no `axiom`.

Convention: `N = k + 1` is the number of entries (speeds) of the one-entry vector `wFam k r w = ([1,N] \ {r}) ∪ {w}`. Speeds are the moving runners; the runner at rest is not counted, so a vector of `N` speeds means `N + 1` runners and the Lonely Runner value is `1/(N+1)`.
Hypotheses: those of the individual statements (numerical bounds, structural conditions and, where named in the list above, window predicates such as `PrimeWin`, `CopWin`, `PrimeWindow7`, which later modules discharge for explicit ranges). The unproved predicates `DusartPi`, `LRCHyp`, `CopWinHyp` are not hypotheses of any statement in this module.
Axiom audit: covered by `Axioms5` (first); every later audit module imports this module (`#print axioms`; declarations not printed there are bricks of printed ones, so their axioms are bounded by the printed lines).
-/

namespace LRSpectrumFull
namespace Sext6
namespace Gap

/-- Residue test at `t₀ = a/D`: if `a r + b D = 1` and `D ∤ z, z - r, z + r`, then `2/D ≤ ‖z · (a/D)‖`. -/
theorem far_of_cond {D : ℕ} (hD : 0 < D) (r a b z : ℤ) (hab : a * r + b * (D : ℤ) = 1)
    (h0 : ¬ ((D : ℤ) ∣ z)) (h1 : ¬ ((D : ℤ) ∣ z - r)) (h2 : ¬ ((D : ℤ) ∣ z + r)) :
    2 / (D : ℝ) ≤ nearestIntDist ((z : ℝ) * ((a : ℝ) / D)) := by
  have e : (z : ℝ) * ((a : ℝ) / D) = ((a * z : ℤ) : ℝ) / D := by
    push_cast; ring
  have key : ((2 : ℕ) : ℝ) / (D : ℝ) ≤ nearestIntDist (((a * z : ℤ) : ℝ) / D) := by
    apply nid_div_ge hD (a * z) 2
    intro n
    by_contra hcon
    push Not at hcon
    have hc2 : |a * z - n * (D : ℤ)| < 2 := by exact_mod_cast hcon
    obtain ⟨hlo, hhi⟩ := abs_lt.mp hc2
    obtain ⟨y, hy⟩ : ∃ y : ℤ, y = a * z - n * (D : ℤ) := ⟨_, rfl⟩
    rw [← hy] at hlo hhi
    have hkey : z - y * r = (D : ℤ) * (b * z + n * r) := by
      rw [hy]
      linear_combination (-z) * hab
    have hy3 : y = -1 ∨ y = 0 ∨ y = 1 := by omega
    rcases hy3 with hy' | hy' | hy'
    · rw [hy'] at hkey
      exact h2 ⟨b * z + n * r, by linear_combination hkey⟩
    · rw [hy'] at hkey
      exact h0 ⟨b * z + n * r, by linear_combination hkey⟩
    · rw [hy'] at hkey
      exact h1 ⟨b * z + n * r, by linear_combination hkey⟩
  have h2c : ((2 : ℕ) : ℝ) = 2 := by norm_num
  rw [h2c] at key
  rw [e]
  exact key

/-- A retained speed `x ∈ [1,N] \ {r}` is `≢ 0, r, -r (mod D)` as soon as `D ≥ N + 1 + r`. -/
theorem retained_cond {N r x D : ℕ} (hD : N + 1 + r ≤ D) (hx1 : 1 ≤ x) (hxN : x ≤ N)
    (hxr : x ≠ r) :
    ¬ ((D : ℤ) ∣ (x : ℤ)) ∧ ¬ ((D : ℤ) ∣ (x : ℤ) - (r : ℤ)) ∧
      ¬ ((D : ℤ) ∣ (x : ℤ) + (r : ℤ)) := by
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

/-- **Lemma L (large inserted speed).**  `N = k + 1`, `1 ≤ r`, `N + 1 + r ≤ D`, `D + E = 2N`, `1 ≤ E`,
`gcd(D, r) = 1`, `D N² ≤ 2 E w`  ⟹  `1/N ≤ ML ([N] \ {r} ∪ {w})`. -/
theorem ML_ge_inv_large {k N r w D E : ℕ} (hk : k + 1 = N) (hN : 2 ≤ N)
    (hD : N + 1 + r ≤ D) (hDE : D + E = 2 * N) (hE : 1 ≤ E) (hcop : Nat.Coprime D r)
    (hw : D * N ^ 2 ≤ 2 * E * w) : 1 / (N : ℝ) ≤ ML (wFam k r w) := by
  have hDpos : 0 < D := by omega
  have hNpos : 0 < N := by omega
  have hwpos : 0 < w := by
    rcases Nat.eq_zero_or_pos w with h | h
    · exfalso
      subst h
      have : 0 < D * N ^ 2 := Nat.mul_pos hDpos (pow_pos hNpos 2)
      omega
    · exact h
  obtain ⟨a, b, hab⟩ : IsCoprime (r : ℤ) (D : ℤ) := Nat.isCoprime_iff_coprime.mpr hcop.symm
  have hDR : (0 : ℝ) < D := by exact_mod_cast hDpos
  have hNR : (0 : ℝ) < N := by exact_mod_cast hNpos
  have hwR : (0 : ℝ) < w := by exact_mod_cast hwpos
  have hN2 : (2 : ℝ) ≤ N := by exact_mod_cast hN
  have hDne : (D : ℝ) ≠ 0 := hDR.ne'
  have hNne : (N : ℝ) ≠ 0 := hNR.ne'
  have hwne : (w : ℝ) ≠ 0 := hwR.ne'
  have hER : (E : ℝ) = 2 * N - D := by
    have h : ((D + E : ℕ) : ℝ) = ((2 * N : ℕ) : ℝ) := by rw [hDE]
    push_cast at h
    linarith
  have hE0 : (0 : ℝ) ≤ E := by positivity
  have hwineq : (D : ℝ) * (N : ℝ) ^ 2 ≤ 2 * (E : ℝ) * (w : ℝ) := by exact_mod_cast hw
  obtain ⟨t0, ht0⟩ : ∃ t0 : ℝ, t0 = (a : ℝ) / D := ⟨_, rfl⟩
  obtain ⟨δ, hδdef⟩ : ∃ δ : ℝ, δ = (E : ℝ) / ((D : ℝ) * (N : ℝ) ^ 2) := ⟨_, rfl⟩
  have hδ0 : 0 ≤ δ := by rw [hδdef]; positivity
  have hδ : 1 / (2 * (w : ℝ)) ≤ δ := by
    rw [hδdef, div_le_div_iff₀ (by linarith) (mul_pos hDR (pow_pos hNR 2))]
    linarith
  obtain ⟨k0, hk0a, hk0b⟩ : ∃ k0 : ℤ, (k0 : ℝ) ≤ (w : ℝ) * t0 ∧ (w : ℝ) * t0 < k0 + 1 :=
    ⟨⌊(w : ℝ) * t0⌋, Int.floor_le _, Int.lt_floor_add_one _⟩
  obtain ⟨t, ht⟩ : ∃ t : ℝ, t = ((k0 : ℝ) + 1 / 2) / w := ⟨_, rfl⟩
  have hwt : (w : ℝ) * t = (k0 : ℝ) + 1 / 2 := by
    rw [ht]
    first
      | (field_simp; done)
      | (field_simp; ring)
  have hdist : |t - t0| ≤ δ := by
    have h1 : t - t0 = ((k0 : ℝ) + 1 / 2 - (w : ℝ) * t0) / w := by
      rw [ht]
      first
        | (field_simp; done)
        | (field_simp; ring)
    have h2 : |(k0 : ℝ) + 1 / 2 - (w : ℝ) * t0| ≤ 1 / 2 := by
      rw [abs_le]
      constructor <;> linarith
    rw [h1, abs_div, abs_of_pos hwR]
    have h3 : |(k0 : ℝ) + 1 / 2 - (w : ℝ) * t0| / w ≤ (1 / 2) / w := by gcongr
    have h4 : (1 / 2 : ℝ) / w = 1 / (2 * (w : ℝ)) := by rw [div_div]
    linarith
  have hkey : (2 : ℝ) / D - (N : ℝ) * δ = 1 / N := by
    rw [hδdef, hER]
    first
      | (field_simp; done)
      | (field_simp; ring)
  have hhalf : 1 / (N : ℝ) ≤ nearestIntDist (1 / 2) := by
    have hle : 1 / (N : ℝ) ≤ 1 / 2 := one_div_le_one_div_of_le (by norm_num) hN2
    exact nearestIntDist_ge (by norm_num) (by norm_num) hle (by linarith)
  have hhalf' : nearestIntDist ((k0 : ℝ) + 1 / 2) = nearestIntDist (1 / 2) := by
    rw [add_comm]
    exact nearestIntDist_add_int _ _
  refine ML_ge_of_far (wFam k r w) (1 / (N : ℝ)) t ?_
  intro i
  by_cases hi : (i : ℕ) + 1 = r
  · rw [wFam_at_r i hi]
    have hc : (((w : ℕ) : ℤ) : ℝ) = (w : ℝ) := by norm_cast
    rw [hc, hwt, hhalf']
    exact hhalf
  · rw [wFam_ne_r i hi]
    have hiN : (i : ℕ) < k + 1 := i.isLt
    generalize hx : (i : ℕ) + 1 = x at hi ⊢
    have hx1 : 1 ≤ x := by omega
    have hxN : x ≤ N := by omega
    have hxr : x ≠ r := by omega
    obtain ⟨c0, c1, c2⟩ := retained_cond (r := r) hD hx1 hxN hxr
    have hfar := far_of_cond hDpos (r : ℤ) a b (x : ℤ) hab c0 c1 c2
    rw [← ht0] at hfar
    have hxR : ((x : ℕ) : ℝ) ≤ N := by exact_mod_cast hxN
    have hx0 : (0 : ℝ) ≤ ((x : ℕ) : ℝ) := by positivity
    have hcc : ((((x : ℕ) : ℤ)) : ℝ) = ((x : ℕ) : ℝ) := by norm_cast
    rw [hcc] at hfar ⊢
    have hlip := nearestIntDist_lipschitz (((x : ℕ) : ℝ) * t0) (((x : ℕ) : ℝ) * t)
    have habs : |((x : ℕ) : ℝ) * t0 - ((x : ℕ) : ℝ) * t| ≤ (N : ℝ) * δ := by
      have e1 : ((x : ℕ) : ℝ) * t0 - ((x : ℕ) : ℝ) * t = ((x : ℕ) : ℝ) * (t0 - t) := by ring
      rw [e1, abs_mul, abs_of_nonneg hx0, abs_sub_comm]
      calc ((x : ℕ) : ℝ) * |t - t0| ≤ ((x : ℕ) : ℝ) * δ := by gcongr
        _ ≤ (N : ℝ) * δ := by gcongr
    have hl := (abs_sub_le_iff.mp hlip).1
    linarith

end Gap
end Sext6
end LRSpectrumFull
