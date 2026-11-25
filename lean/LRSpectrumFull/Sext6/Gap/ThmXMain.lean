import LRSpectrumFull.Sext6.Gap.ThmXArc
import LRSpectrumFull.Sext6.Gap.ThmXTab

/-!
# Theorem X: the exact criterion for the window family `([N] \ {r}) ∪ W`  [2026-11-25]

Source: the accompanying notes on Theorem X, (statement (ii), (iii), (iv) for the listed `r`, (v)) and the review of those notes.

Let `r ≥ 2`, `2 r ≤ N`, `W = {D ∈ [N+r+1, N+2r] : gcd(D,r) = 1}` (`|W| = φ(r)`), `v` any speed vector whose
entry set is exactly `([1,N] \ {r}) ∪ W` (`IsV N r v`), `D0 = dFam N r` the least integer `≥ N+1+r` coprime to `r`.

* `thmX_iff`      : `ML v < 1/N ↔ 2 N < D0 + 2 r` (i.e. `D0 > 2N - 2r`), both directions.
* `thmX_xholds`   : `ML v < 1/N ↔` no integer of `[N+r+1, 2N-2r]` is coprime to `r`.
* `thmX_le_three` : `ML v < 1/N` for every `2 r ≤ N ≤ 3 r`.
* `thmX_run`      : for `N = 3 r + l`, `ML v < 1/N ↔` every `m ∈ [l+1, 2 l]` shares a factor with `r`.
* `thmX_last`     : if `LastExc r L` (table of `ThmXTab`) then `ML < 1/L` at `L`, and `1/N ≤ ML` for every `N > L`.
* `thmX_minimal`  : (v) dropping any one element of `W` gives `1/N ≤ ML`.
* `ML_le_two_div_2N1` (module `ThmXArc`): in the exceptional case `ML v ≤ 2/(2N+1)`.
No `sorry`, no `axiom`.

Convention: `N` is the size of the ambient interval `[N]`; `k` is not linked to `N` (`v` may repeat entries); speeds are the
moving runners, the runner at rest is not counted.
Hypotheses: `2 ≤ r`, `2 r ≤ N` (so `N ≥ 4`); `IsV N r v`.
Axiom audit: covered by `Axioms24`.
-/

namespace LRSpectrumFull
namespace Sext6
namespace Gap

/-- **Theorem X** (`D0` given by `DSpec`). -/
theorem thmX_iff {k N r D : ℕ} (hS : DSpec N r D) (hr2 : 2 ≤ r) (v : Fin (k + 1) → ℤ)
    (hV : IsV N r v) : ML v < 1 / (N : ℝ) ↔ 2 * N < D + 2 * r := by
  constructor
  · intro hlt
    by_contra h
    have hle : D + 2 * r ≤ 2 * N := not_lt.mp h
    have := ML_ge_of_le hS hr2 hle v hV
    linarith
  · intro hDg
    have h1 := ML_le_two_div_2N1 hS hDg v hV
    have hN3 := hS.hN3
    have hNR : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
    have h2 : 2 / ((2 : ℝ) * N + 1) < 1 / (N : ℝ) := by
      rw [div_lt_div_iff₀ (by positivity) hNR]
      linarith
    linarith

/-- Theorem X with `D0 = dFam N r`. -/
theorem thmX_dFam {k N r : ℕ} (hr2 : 2 ≤ r) (hN : 2 * r ≤ N) (v : Fin (k + 1) → ℤ)
    (hV : IsV N r v) : ML v < 1 / (N : ℝ) ↔ 2 * N < dFam N r + 2 * r :=
  thmX_iff (spec_dFam (by omega) hN (by omega)) hr2 v hV

/-- Theorem X, arithmetic form: `ML v < 1/N` iff `[N+r+1, 2N-2r]` has no integer coprime to `r`. -/
theorem thmX_xholds {k N r : ℕ} (hr2 : 2 ≤ r) (hN : 2 * r ≤ N) (v : Fin (k + 1) → ℤ)
    (hV : IsV N r v) : ML v < 1 / (N : ℝ) ↔ XHolds r N := by
  have hS := spec_dFam (N := N) (r := r) (by omega) hN (by omega)
  rw [thmX_iff hS hr2 v hV, xholds_iff_dspec hS]

/-- (iii), first part: for `2 r ≤ N ≤ 3 r` the criterion always holds. -/
theorem thmX_le_three {k N r : ℕ} (hr2 : 2 ≤ r) (hN : 2 * r ≤ N) (h3 : N ≤ 3 * r)
    (v : Fin (k + 1) → ℤ) (hV : IsV N r v) : ML v < 1 / (N : ℝ) :=
  (thmX_xholds hr2 hN v hV).mpr (xholds_of_le_three h3)

/-- (iii), run form: for `N = 3 r + l`, `ML v < 1/N` iff every `m ∈ [l+1, 2l]` shares a factor with `r`. -/
theorem thmX_run {k N r l : ℕ} (hr2 : 2 ≤ r) (hN : 2 * r ≤ N) (hNl : N = 3 * r + l)
    (v : Fin (k + 1) → ℤ) (hV : IsV N r v) :
    ML v < 1 / (N : ℝ) ↔ ∀ m : ℕ, l + 1 ≤ m → m ≤ 2 * l → ¬ Nat.Coprime m r := by
  rw [thmX_xholds hr2 hN v hV, xholds_run hNl]

/-- (iv) for a tabulated last exceptional `N = L`: `ML < 1/L` at `L`, and `1/N ≤ ML` for every `N > L`. -/
theorem thmX_last {r L : ℕ} (hr2 : 2 ≤ r) (hL : 2 * r ≤ L) (hLE : LastExc r L) :
    (∀ (k : ℕ) (v : Fin (k + 1) → ℤ), IsV L r v → ML v < 1 / (L : ℝ)) ∧
    (∀ N : ℕ, L < N → ∀ (k : ℕ) (v : Fin (k + 1) → ℤ), IsV N r v → 1 / (N : ℝ) ≤ ML v) := by
  refine ⟨fun k v hV => (thmX_xholds hr2 hL v hV).mpr hLE.1, ?_⟩
  intro N hN k v hV
  have hN' : 2 * r ≤ N := by omega
  by_contra h
  exact hLE.2 N hN ((thmX_xholds hr2 hN' v hV).mp (not_le.mp h))

/-- **Minimality (v).**  For every `N ≥ 2 r` and every `D'` in the window coprime to `r`, any vector whose
entries are admissible and avoid `D'` has `1/N ≤ ML`; no hypothesis on `D0`. -/
theorem thmX_minimal {k N r D' : ℕ} (hr2 : 2 ≤ r) (hN : 2 * r ≤ N) (hD1 : N + r + 1 ≤ D')
    (hD2 : D' ≤ N + 2 * r) (hcop : Nat.Coprime D' r) (v : Fin (k + 1) → ℤ)
    (hv : ∀ i, XMem N r (v i)) (hne : ∀ i, v i ≠ (D' : ℤ)) : 1 / (N : ℝ) ≤ ML v :=
  ML_ge_of_drop hr2 hN hD1 hD2 hcop v hv hne

/-- The tabulated cases, e.g. `r = 6`: `ML < 1/20` at `N = 20` and `1/N ≤ ML` for every `N ≥ 21`. -/
theorem thmX_last_r6 :
    (∀ (k : ℕ) (v : Fin (k + 1) → ℤ), IsV 20 6 v → ML v < 1 / ((20 : ℕ) : ℝ)) ∧
    (∀ N : ℕ, 20 < N → ∀ (k : ℕ) (v : Fin (k + 1) → ℤ), IsV N 6 v → 1 / (N : ℝ) ≤ ML v) :=
  thmX_last (by norm_num) (by norm_num) lastExc_r6

end Gap
end Sext6
end LRSpectrumFull
