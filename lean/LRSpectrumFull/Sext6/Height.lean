/-
# Height hypothesis, stated as in Yi-Gill-Bu.

Source: Yi, Gill, Bu, "Four runners that are barely lonely", arXiv 2610.40694v1, Thm 11.1(i), p.34:
"Let n >= 3, assume LRC(n-1) and LRC(n-2), and put kappa_n = (n(n-1))^(n-2).  Every primitive v in Z^n
with all v_i != 0 satisfies ML(T_v) > 1/n - kappa_n / (2|v|)", |v| the Euclidean length,
LRC(m) = every set of m positive integers has ML >= 1/(m+1).  (UNREFEREED, arXiv v1.)
Here `n` counts speeds and `Fin (k+1) → ℤ` is the vector, `n = k+1`.

Specialisation to n = 6 (kappa_6 = 30^4 = 810,000).  Proved here: it implies the entry-wise bound
`HeightBound` of `Statement.lean`: ML v ≤ 1/7 forces |v| < 21 * 810000 = 17,010,000, and the
Euclidean length is at least every entry.  `LRC 5` and `LRC 4` stay explicit hypotheses.
-/
import LRSpectrumFull.Sext6.Statement
import Mathlib.Analysis.SpecialFunctions.Pow.Real

namespace LRSpectrumFull
namespace Sext6

/-- `LRC m` (YGB p.34): every set of `m` positive integers has `ML ≥ 1/(m+1)`. -/
def LRC (m : ℕ) : Prop :=
  ∀ k : ℕ, k + 1 = m → ∀ v : Fin (k + 1) → ℤ, Function.Injective v → (∀ i, 0 < v i) →
    (1 : ℝ) / ((m : ℝ) + 1) ≤ ML v

/-- Euclidean length of an integer vector. -/
noncomputable def euclNorm {n : ℕ} (v : Fin n → ℤ) : ℝ := Real.sqrt (∑ i, ((v i : ℤ) : ℝ) ^ 2)

/-- `κ_n = (n (n-1))^(n-2)`. -/
def ygbKappa (n : ℕ) : ℕ := (n * (n - 1)) ^ (n - 2)

/-- YGB Theorem 11.1(i), general `n` (cited, unrefereed). -/
def YGB11_1i (n : ℕ) : Prop :=
  3 ≤ n → LRC (n - 1) → LRC (n - 2) → ∀ k : ℕ, k + 1 = n → ∀ v : Fin (k + 1) → ℤ,
    Primitive v → (∀ i, v i ≠ 0) →
      (1 : ℝ) / n - (ygbKappa n : ℝ) / (2 * euclNorm v) < ML v

/-- The `n = 6`, `κ = 810000` specialisation, with `LRC 5` and `LRC 4` explicit. -/
def HeightBoundYGB6 : Prop :=
  LRC 5 → LRC 4 → ∀ v : Fin 6 → ℤ, Primitive v → (∀ i, v i ≠ 0) →
    (1 : ℝ) / 6 - 810000 / (2 * euclNorm v) < ML v

theorem ygbKappa_six : ygbKappa 6 = 810000 := by decide

theorem HeightBoundYGB6_of_general (h : YGB11_1i 6) : HeightBoundYGB6 := by
  intro h5 h4 v hprim hne
  have := h (by norm_num) h5 h4 5 rfl v hprim hne
  rw [ygbKappa_six] at this
  simpa using this

/-- every entry is at most the Euclidean length. -/
theorem entry_le_euclNorm {n : ℕ} (v : Fin n → ℤ) (i : Fin n) : (v i : ℝ) ≤ euclNorm v := by
  unfold euclNorm
  refine le_trans (le_abs_self _) (Real.abs_le_sqrt ?_)
  exact Finset.single_le_sum (f := fun j => ((v j : ℤ) : ℝ) ^ 2) (fun j _ => sq_nonneg _)
    (Finset.mem_univ i)

/-- **Height bound from YGB.** `HeightBoundYGB6` (with `LRC 5`, `LRC 4`) implies the entry-wise
bound used by `Statement.HeightBound`. -/
theorem heightBound_of_ygb (h : HeightBoundYGB6) (h5 : LRC 5) (h4 : LRC 4) : HeightBound := by
  intro v hpos hprim hML i
  have hne : ∀ j, v j ≠ 0 := fun j => (hpos j).ne'
  have hlt := h h5 h4 v hprim hne
  have hE : 0 < euclNorm v := by
    have h0 : (0 : ℝ) < (v 0 : ℝ) := by exact_mod_cast hpos 0
    exact lt_of_lt_of_le h0 (entry_le_euclNorm v 0)
  have h2 : (1 : ℝ) / 6 - 810000 / (2 * euclNorm v) < 1 / 7 := lt_of_lt_of_le hlt hML
  have h3 : (1 : ℝ) / 42 < 810000 / (2 * euclNorm v) := by linarith
  rw [lt_div_iff₀ (by positivity)] at h3
  have h4' : euclNorm v < 17010000 := by linarith
  have h5' : (v i : ℝ) < 17010000 := lt_of_le_of_lt (entry_le_euclNorm v i) h4'
  exact_mod_cast h5'

end Sext6
end LRSpectrumFull

#print axioms LRSpectrumFull.Sext6.HeightBoundYGB6_of_general
#print axioms LRSpectrumFull.Sext6.heightBound_of_ygb
