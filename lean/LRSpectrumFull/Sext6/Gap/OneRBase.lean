import LRSpectrumFull.Sext6.Gap.KStarMain
import LRSpectrumFull.Sext6.Gap.Witness
import LRSpectrumFull.Sext6.Gap.LowerA

/-!
# One-entry deletion `B = [N] \ {r}`, part 1: definitions and the lower bound  [2026-11-25]

Source: the accompanying notes on the one-entry deletion (Plan 3, Lemma B1, Lemma B0).

* `DSpec N r D`   : `D` is the least integer `≥ N + 1 + r` coprime to `r`, with `1 ≤ r`, `2 r ≤ N`, `3 ≤ N`.
* `dFam N r`      : that least integer, with `spec_dFam` and `DSpec.le_window : D ≤ N + 2 r`.
* `IsB N r v`     : the speeds of `v` are exactly `[1,N] \ {r}` (as a set; repetitions allowed).
* `ML_congr_range`: `ML` depends only on the set of entries.
* `far_at_inv`    : at `t = K/D` with `D ∣ r K - 1`, every speed `x ∈ [1,N] \ {r}` has `‖x t‖ ≥ 2/D`.
* `ML_ge_delB`       : `2/D ≤ ML v` for every `v` with all entries in `[1,N] \ {r}`.
No `sorry`, no `axiom`.

Convention: `N` is the size of the ambient interval `[N]` (`DSpec N r D`, `IsB N r v`): the deletion of `r` leaves `N - 1` distinct speeds, and `k` is not linked to `N` in the `IsB` statements (repetitions and any order are allowed). `bFam k r` lists `[N] \ {r}` and has `k + 1 = N - 1` entries when `N = k + 2`; `wFam (k+1) r w` has `k + 2 = N` entries (compare `OE_low_unconditional`, where `wFam k r w` has `k + 1 = N` entries). Speeds are the moving runners; the runner at rest is not counted, so a vector of `N` speeds means `N + 1` runners and the Lonely Runner value is `1/(N+1)`.
Hypotheses: those of the individual statements (numerical bounds, structural conditions and, where named in the list above, window predicates such as `PrimeWin`, `CopWin`, `PrimeWindow7`, which later modules discharge for explicit ranges). The unproved predicates `DusartPi`, `LRCHyp`, `CopWinHyp` are not hypotheses of any statement in this module.
Axiom audit: covered by `Axioms19` (`#print axioms`; declarations not printed there are bricks of printed ones, so their axioms are bounded by the printed lines).
-/

namespace LRSpectrumFull
namespace Sext6
namespace Gap

/-! ### `ML` depends only on the set of entries -/

theorem gap_congr_range {k l : ℕ} (v : Fin (k + 1) → ℤ) (u : Fin (l + 1) → ℤ)
    (h1 : ∀ i, ∃ j, v i = u j) (h2 : ∀ j, ∃ i, u j = v i) : gap v = gap u := by
  funext t
  apply le_antisymm
  · apply le_gap
    intro j
    obtain ⟨i, hi⟩ := h2 j
    rw [hi]
    exact gap_le v t i
  · apply le_gap
    intro i
    obtain ⟨j, hj⟩ := h1 i
    rw [hj]
    exact gap_le u t j

theorem ML_congr_range {k l : ℕ} (v : Fin (k + 1) → ℤ) (u : Fin (l + 1) → ℤ)
    (h1 : ∀ i, ∃ j, v i = u j) (h2 : ∀ j, ∃ i, u j = v i) : ML v = ML u := by
  unfold ML
  rw [gap_congr_range v u h1 h2]

/-! ### The specification of `D` -/

/-- `D` is the least integer `≥ N + 1 + r` coprime to `r` (`D0` of the accompanying notes on the one-entry deletion). -/
structure DSpec (N r D : ℕ) : Prop where
  hr : 1 ≤ r
  hN : 2 * r ≤ N
  hN3 : 3 ≤ N
  hD1 : N + 1 + r ≤ D
  hcop : Nat.Coprime D r
  hmin : ∀ b : ℕ, N + 1 + r ≤ b → Nat.Coprime b r → D ≤ b

noncomputable def dFam (N r : ℕ) : ℕ := sInf {b : ℕ | N + 1 + r ≤ b ∧ Nat.Coprime b r}

/-- Lemma B0: the window `[N+r+1, N+2r]` contains an integer `≡ 1 (mod r)`. -/
theorem exists_window_r {N r : ℕ} (hr : 1 ≤ r) :
    ∃ b : ℕ, N + 1 + r ≤ b ∧ b ≤ N + 2 * r ∧ Nat.Coprime b r := by
  obtain ⟨q, m, hq1, hq2⟩ : ∃ q m : ℕ, r * q + m = N + 2 * r - 1 ∧ m < r :=
    ⟨(N + 2 * r - 1) / r, (N + 2 * r - 1) % r, Nat.div_add_mod _ _, Nat.mod_lt _ (by omega)⟩
  obtain ⟨P, hP⟩ : ∃ P : ℕ, P = r * q := ⟨_, rfl⟩
  rw [← hP] at hq1
  refine ⟨P + 1, by omega, by omega, ?_⟩
  rw [hP]
  exact (Nat.coprime_mul_left_add_left 1 r q).mpr (Nat.coprime_one_left r)

theorem spec_dFam {N r : ℕ} (hr : 1 ≤ r) (hN : 2 * r ≤ N) (hN3 : 3 ≤ N) :
    DSpec N r (dFam N r) := by
  obtain ⟨b, hb1, _, hb3⟩ := exists_window_r (N := N) hr
  have hne : ({b : ℕ | N + 1 + r ≤ b ∧ Nat.Coprime b r}).Nonempty := ⟨b, hb1, hb3⟩
  have hmem := Nat.sInf_mem hne
  exact ⟨hr, hN, hN3, hmem.1, hmem.2, fun b' h1 h2 => Nat.sInf_le ⟨h1, h2⟩⟩

theorem DSpec.le_window {N r D : ℕ} (h : DSpec N r D) : D ≤ N + 2 * r := by
  obtain ⟨b, hb1, hb2, hb3⟩ := exists_window_r (N := N) h.hr
  exact (h.hmin b hb1 hb3).trans hb2

theorem DSpec.le_two_N {N r D : ℕ} (h : DSpec N r D) : D ≤ 2 * N := by
  have := h.le_window
  have := h.hN
  omega

/-! ### The speed set `[1,N] \ {r}` -/

/-- The speeds of `v` are exactly `[1,N] \ {r}` (as a set). -/
structure IsB (N r : ℕ) {k : ℕ} (v : Fin (k + 1) → ℤ) : Prop where
  sub : ∀ i, 1 ≤ v i ∧ v i ≤ (N : ℤ) ∧ v i ≠ (r : ℤ)
  cov : ∀ x : ℕ, 1 ≤ x → x ≤ N → x ≠ r → ∃ i, v i = (x : ℤ)

/-! ### Lower bound (Lemma B1) -/

theorem exists_inv_r {N r D : ℕ} (hS : DSpec N r D) : ∃ K : ℤ, (D : ℤ) ∣ (r : ℤ) * K - 1 := by
  have hc : IsCoprime (r : ℤ) (D : ℤ) := Nat.isCoprime_iff_coprime.mpr hS.hcop.symm
  obtain ⟨a, b, hab⟩ := hc
  exact ⟨a, ⟨-b, by linear_combination hab⟩⟩

/-- At a time `K/D` with `D ∣ r K - 1`, every speed `x ∈ [1,N] \ {r}` is at distance `≥ 2/D`
from an integer. -/
theorem far_at_inv {N r D : ℕ} (hS : DSpec N r D) (K : ℤ) (hK : (D : ℤ) ∣ (r : ℤ) * K - 1)
    (x : ℤ) (hx1 : 1 ≤ x) (hxN : x ≤ N) (hxr : x ≠ r) :
    2 / (D : ℝ) ≤ nearestIntDist ((x : ℝ) * ((K : ℝ) / D)) := by
  have hD1 := hS.hD1
  have hr := hS.hr
  have hN2 := hS.hN
  have hDpos : 0 < D := by omega
  obtain ⟨s, hs⟩ := hK
  have e : (x : ℝ) * ((K : ℝ) / D) = ((K * x : ℤ) : ℝ) / D := by push_cast; ring
  rw [e]
  have key : ((2 : ℕ) : ℝ) / (D : ℝ) ≤ nearestIntDist (((K * x : ℤ) : ℝ) / D) := by
    apply nid_div_ge hDpos (K * x) 2
    intro n
    by_contra hcon
    push Not at hcon
    have hc2 : |K * x - n * (D : ℤ)| < 2 := by exact_mod_cast hcon
    obtain ⟨hlo, hhi⟩ := abs_lt.mp hc2
    obtain ⟨y, hy⟩ : ∃ y : ℤ, y = K * x - n * (D : ℤ) := ⟨_, rfl⟩
    rw [← hy] at hlo hhi
    have hkey : x - (r : ℤ) * y = (D : ℤ) * ((r : ℤ) * n - s * x) := by
      rw [hy]
      linear_combination (-x) * hs
    have hy3 : y = -1 ∨ y = 0 ∨ y = 1 := by omega
    rcases hy3 with h | h | h
    · rw [h] at hkey
      have hd : (D : ℤ) ∣ x + r := ⟨(r : ℤ) * n - s * x, by linear_combination hkey⟩
      have := Int.eq_zero_of_abs_lt_dvd hd (abs_lt.mpr ⟨by omega, by omega⟩)
      omega
    · rw [h] at hkey
      have hd : (D : ℤ) ∣ x := ⟨(r : ℤ) * n - s * x, by linear_combination hkey⟩
      have := Int.eq_zero_of_abs_lt_dvd hd (abs_lt.mpr ⟨by omega, by omega⟩)
      omega
    · rw [h] at hkey
      have hd : (D : ℤ) ∣ x - r := ⟨(r : ℤ) * n - s * x, by linear_combination hkey⟩
      have := Int.eq_zero_of_abs_lt_dvd hd (abs_lt.mpr ⟨by omega, by omega⟩)
      omega
  have h2c : ((2 : ℕ) : ℝ) = 2 := by norm_num
  rw [h2c] at key
  exact key

/-- **Lemma B1.** Every speed vector with all entries in `[1,N] \ {r}` has `2/D ≤ ML`. -/
theorem ML_ge_delB {k N r D : ℕ} (hS : DSpec N r D) (v : Fin (k + 1) → ℤ)
    (hv : ∀ i, 1 ≤ v i ∧ v i ≤ (N : ℤ) ∧ v i ≠ (r : ℤ)) : 2 / (D : ℝ) ≤ ML v := by
  obtain ⟨K, hK⟩ := exists_inv_r hS
  apply ML_ge_of_far v _ ((K : ℝ) / D)
  intro i
  obtain ⟨h1, h2, h3⟩ := hv i
  exact far_at_inv hS K hK (v i) h1 h2 h3

/-- At every `K/D` with `D ∣ r K - 1` the loneliness of `v` is at least `2/D`. -/
theorem gap_ge_at_inv {k N r D : ℕ} (hS : DSpec N r D) (v : Fin (k + 1) → ℤ)
    (hv : ∀ i, 1 ≤ v i ∧ v i ≤ (N : ℤ) ∧ v i ≠ (r : ℤ)) (K : ℤ)
    (hK : (D : ℤ) ∣ (r : ℤ) * K - 1) : 2 / (D : ℝ) ≤ gap v ((K : ℝ) / D) := by
  apply le_gap
  intro i
  obtain ⟨h1, h2, h3⟩ := hv i
  exact far_at_inv hS K hK (v i) h1 h2 h3

end Gap
end Sext6
end LRSpectrumFull
