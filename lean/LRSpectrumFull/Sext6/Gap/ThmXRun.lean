import LRSpectrumFull.Sext6.Gap.OneRBase

/-!
# Theorem X, part 1: the arithmetic criterion and its run form  [2026-11-25]

Source: the accompanying notes on Theorem X, Section 0 (iii), Section 3 (iii), Section 4 (iv).

* `XHolds r N`        : no integer of `[N+r+1, 2N-2r]` is coprime to `r` (the criterion `D0 > 2N-2r`).
* `xholds_iff_dspec`  : for `DSpec N r D`, `XHolds r N ↔ 2 N < D + 2 r` (i.e. `D > 2N - 2r`).
* `xholds_of_le_three`: `XHolds r N` for every `N ≤ 3 r`.
* `xholds_run`        : for `N = 3 r + l`, `XHolds r N` iff every `m ∈ [l+1, 2l]` shares a factor with `r`.
* `not_xholds_of_ge`  : `¬ XHolds r N` for `N ≥ 4 r`, `r ≥ 1`.
* `LastExc r L`       : `L` is the last `N` with `XHolds r N`; `lastExc_of_finite` reduces it to a finite check.
No `sorry`, no `axiom`.

Convention: `N` is the size of the ambient interval `[N]`; `r ≥ 1`; all quantities here are natural numbers (the window `[N+r+1, N+2r]` has `r` consecutive integers).
Hypotheses: those of the individual statements.
Axiom audit: covered by `Axioms24`.
-/

namespace LRSpectrumFull
namespace Sext6
namespace Gap

/-- The arithmetic criterion `D0 > 2N - 2r`, stated without `D0`: the interval `[N+r+1, 2N-2r]`
contains no integer coprime to `r`. -/
def XHolds (r N : ℕ) : Prop :=
  ∀ b ∈ Finset.Icc (N + r + 1) (2 * N - 2 * r), ¬ Nat.Coprime b r

instance (r N : ℕ) : Decidable (XHolds r N) := by
  unfold XHolds; infer_instance

/-- `D0 > 2N - 2r` (in the form `2 N < D0 + 2 r`) iff `XHolds r N`. -/
theorem xholds_iff_dspec {N r D : ℕ} (hS : DSpec N r D) : XHolds r N ↔ 2 * N < D + 2 * r := by
  have hD1 := hS.hD1
  have hcop := hS.hcop
  have hN := hS.hN
  constructor
  · intro h
    by_contra hcon
    have hle : D ≤ 2 * N - 2 * r := by omega
    exact h D (Finset.mem_Icc.mpr ⟨by omega, hle⟩) hcop
  · intro h b hb hcb
    rw [Finset.mem_Icc] at hb
    have := hS.hmin b (by omega) hcb
    omega

/-- (iii), first part: for `N ≤ 3 r` the interval `[N+r+1, 2N-2r]` is empty. -/
theorem xholds_of_le_three {r N : ℕ} (hN : N ≤ 3 * r) : XHolds r N := by
  intro b hb
  rw [Finset.mem_Icc] at hb
  exfalso
  omega

/-- (iii), run form: for `N = 3 r + l`, `XHolds r N` iff every `m ∈ [l+1, 2 l]` has a common
factor with `r`. -/
theorem xholds_run {r N l : ℕ} (hN : N = 3 * r + l) :
    XHolds r N ↔ ∀ m : ℕ, l + 1 ≤ m → m ≤ 2 * l → ¬ Nat.Coprime m r := by
  subst hN
  constructor
  · intro h m h1 h2 hm
    exact h (r * 4 + m) (Finset.mem_Icc.mpr ⟨by omega, by omega⟩)
      ((Nat.coprime_mul_left_add_left m r 4).mpr hm)
  · intro h b hb hcb
    rw [Finset.mem_Icc] at hb
    obtain ⟨hb1, hb2⟩ := hb
    obtain ⟨m, hm⟩ : ∃ m, b = r * 4 + m := ⟨b - 4 * r, by omega⟩
    subst hm
    exact h m (by omega) (by omega) ((Nat.coprime_mul_left_add_left m r 4).mp hcb)

/-- For `N ≥ 4 r` the criterion always fails (the window contains a unit). -/
theorem not_xholds_of_ge {r N : ℕ} (hr : 1 ≤ r) (hN : 4 * r ≤ N) : ¬ XHolds r N := by
  intro h
  obtain ⟨b, hb1, hb2, hb3⟩ := exists_window_r (N := N) hr
  exact h b (Finset.mem_Icc.mpr ⟨by omega, by omega⟩) hb3

/-- `L` is the last `N` for which the criterion holds. -/
def LastExc (r L : ℕ) : Prop := XHolds r L ∧ ∀ N, L < N → ¬ XHolds r N

/-- Reduction of `LastExc` to a finite check on `(L, 4 r]`. -/
theorem lastExc_of_finite {r L : ℕ} (hr : 1 ≤ r) (h1 : XHolds r L)
    (h2 : ∀ N ∈ Finset.Icc (L + 1) (4 * r), ¬ XHolds r N) : LastExc r L := by
  refine ⟨h1, fun N hN => ?_⟩
  by_cases h : N ≤ 4 * r
  · exact h2 N (Finset.mem_Icc.mpr ⟨hN, h⟩)
  · exact not_xholds_of_ge hr (by omega)

end Gap
end Sext6
end LRSpectrumFull
