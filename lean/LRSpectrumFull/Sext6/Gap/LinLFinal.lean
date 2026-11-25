import LRSpectrumFull.Sext6.Gap.LinLCore
import LRSpectrumFull.Sext6.Gap.RobustK13Cheb

/-!
# Theorem L (linear robustness), module 4: hypothesis-free corollaries (Chebyshev window)  [2026-11-25]

`ChebCond T N : 6 l (T + 3 l + 60) + 1200 ≤ N`, `l = Nat.log 2 N + 2` (from `RobustK13Cheb`) gives a coprime
window of size `T` for every `1 ≤ r`, `2 r ≤ N` (`copWinT_of_cheb`).  With `T = C k + 1`:

* `theoremS_linC`   : generic constant `C ≥ 7` with the per-speed bound `SmallTot C N r`.
* `theoremS_lin18`  : Stage A, `T = 18k+1`.
* `cor_a_linC`, `cor_a_lin18` : Corollary S'(a).
* `theoremS_lin18_big` : the same for `N ≥ max 10^5 (67 T²)`, no `ChebCond`.
No `sorry`, no `axiom`.

Convention: `N` is a natural number; `v : Fin (n+1) → ℤ` is an arbitrary finite family of speeds; `k` counts the entries `> N`.
Hypotheses: `ChebCond` is a decidable numerical condition on `(T, N)`, not an unproved predicate.
Axiom audit: `Axioms26`.
-/

namespace LRSpectrumFull
namespace Sext6
namespace Gap

/-- **Theorem S, linear form, generic constant.** -/
theorem theoremS_linC {C n k N r : ℕ} (hC : 7 ≤ C) (hS : LinL.SmallTot C N r) (hk : 1 ≤ k)
    (hN : ChebCond (C * k + 1) N) (hr1 : 1 ≤ r) (hr : 2 * r ≤ N) (v : Fin (n + 1) → ℤ)
    (hv : ∀ i, (1 ≤ v i ∧ v i ≤ (N : ℤ) ∧ v i ≠ (r : ℤ)) ∨ (N : ℤ) < v i)
    (hcard : (Finset.univ.filter (fun i : Fin (n + 1) => (N : ℤ) < v i)).card ≤ k) :
    1 / (N : ℝ) ≤ ML v := by
  have hP : CopWinT (C * k + 1) N r := copWinT_of_cheb _ N hN hr1 hr
  exact ML_ge_robust_linC hC hS hk hr1 (copWinT_le (by omega) hP) hP v hv hcard

/-- **Corollary S'(a), linear form, generic constant.** -/
theorem cor_a_linC {C n k N : ℕ} (hC : 7 ≤ C) (hS : ∀ r, LinL.SmallTot C N r) (hk : 1 ≤ k)
    (hN : ChebCond (C * k + 1) N)
    (v : Fin (n + 1) → ℤ) (hpos : ∀ i, 1 ≤ v i)
    (hcard : (Finset.univ.filter (fun i : Fin (n + 1) => (N : ℤ) < v i)).card ≤ k)
    (hML : ML v < 1 / (N : ℝ)) :
    ∀ r : ℕ, 1 ≤ r → 2 * r ≤ N → ∃ i, v i = (r : ℤ) := by
  intro r hr1 hr2
  by_contra hne
  push Not at hne
  have := theoremS_linC hC (hS r) hk hN hr1 hr2 v
    (by
      intro i
      by_cases hbig : (N : ℤ) < v i
      · exact Or.inr hbig
      · exact Or.inl ⟨hpos i, not_lt.mp hbig, hne i⟩) hcard
  exact absurd hML (not_lt.mpr this)

/-- **Theorem S, linear form, Stage A (`|F| ≥ 18k+1`).** -/
theorem theoremS_lin18 {n k N r : ℕ} (hk : 1 ≤ k) (hN : ChebCond (18 * k + 1) N) (hr1 : 1 ≤ r)
    (hr : 2 * r ≤ N) (v : Fin (n + 1) → ℤ)
    (hv : ∀ i, (1 ≤ v i ∧ v i ≤ (N : ℤ) ∧ v i ≠ (r : ℤ)) ∨ (N : ℤ) < v i)
    (hcard : (Finset.univ.filter (fun i : Fin (n + 1) => (N : ℤ) < v i)).card ≤ k) :
    1 / (N : ℝ) ≤ ML v :=
  theoremS_linC (by norm_num) (LinL.smallTot_18 N r) hk hN hr1 hr v hv hcard

/-- **Corollary S'(a), linear form, Stage A.** -/
theorem cor_a_lin18 {n k N : ℕ} (hk : 1 ≤ k) (hN : ChebCond (18 * k + 1) N)
    (v : Fin (n + 1) → ℤ) (hpos : ∀ i, 1 ≤ v i)
    (hcard : (Finset.univ.filter (fun i : Fin (n + 1) => (N : ℤ) < v i)).card ≤ k)
    (hML : ML v < 1 / (N : ℝ)) :
    ∀ r : ℕ, 1 ≤ r → 2 * r ≤ N → ∃ i, v i = (r : ℤ) :=
  cor_a_linC (by norm_num) (fun r => LinL.smallTot_18 N r) hk hN v hpos hcard hML

/-- Stage A without `ChebCond`: `N ≥ 10^5` and `67 (18k+1)^2 ≤ N`. -/
theorem theoremS_lin18_big {n k N r : ℕ} (hk : 1 ≤ k) (hN1 : 100000 ≤ N)
    (hN2 : 67 * (18 * k + 1) ^ 2 ≤ N) (hr1 : 1 ≤ r)
    (hr : 2 * r ≤ N) (v : Fin (n + 1) → ℤ)
    (hv : ∀ i, (1 ≤ v i ∧ v i ≤ (N : ℤ) ∧ v i ≠ (r : ℤ)) ∨ (N : ℤ) < v i)
    (hcard : (Finset.univ.filter (fun i : Fin (n + 1) => (N : ℤ) < v i)).card ≤ k) :
    1 / (N : ℝ) ≤ ML v := by
  have hP : CopWinT (18 * k + 1) N r := copWinT_of_cheb_N _ N hN1 hN2 hr1 hr
  exact ML_ge_robust_lin hk hr1 (copWinT_le (by omega) hP) hP v hv hcard

end Gap
end Sext6
end LRSpectrumFull
