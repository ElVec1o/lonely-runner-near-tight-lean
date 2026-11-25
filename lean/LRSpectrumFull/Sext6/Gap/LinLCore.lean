import LRSpectrumFull.Sext6.Gap.LinLCount
import LRSpectrumFull.Sext6.Gap.CopWinCore

/-!
# Theorem L (linear robustness), module 3: double counting and assembly (Stage A)  [2026-11-25]

Source: the accompanying notes on Theorem L, step L8 with the joint count of section 3a (constant 18, no lattice identity).

For `k ≥ 1`, `1 ≤ r`, `r + 2 ≤ N`, a coprime window of size `18k+1` (`CopWinT (18*k+1) N r`, a hypothesis
predicate, never an axiom), and any finite family of speeds, each either in `[1,N] \ {r}` or one of at most
`k` entries `> N`: `1/N ≤ ML`.

* `exists_alive`      : some window `J(D)` is not covered by the bad sets of the added speeds
                        (small speeds: `small_total`; oscillating speeds: `badMeas_osc`; joint count).
* `robust_core_lin`   : Finset form (one time `t` for all speeds).
* `ML_ge_robust_lin`  : the statement for an arbitrary speed vector.
No `sorry`, no `axiom`.

Convention: `N` is a natural number (the size of the ambient interval `[1,N]`); `v : Fin (n+1) → ℤ` is an arbitrary
finite family of speeds (repetitions allowed) and `n` is not linked to `N`; `k` counts the entries `> N`.
Hypotheses: `CopWinT (18*k+1) N r` is a hypothesis predicate, discharged unconditionally in `LinLFinal`.
Axiom audit: `Axioms26`.
-/

namespace LRSpectrumFull
namespace Sext6
namespace Gap
namespace LinL

open MeasureTheory

/-- **Step L8, joint count.** -/
theorem exists_alive {C k N r : ℕ} (hC : 7 ≤ C) (hS : SmallTot C N r) (hk : 1 ≤ k) (hr1 : 1 ≤ r)
    (hr2 : r + 2 ≤ N)
    (F : Finset ℕ) (hF : ∀ D ∈ F, N + 1 + r ≤ D ∧ D + 1 ≤ 2 * N)
    (hcop : (F : Set ℕ).Pairwise Nat.Coprime) (hcard : C * k + 1 ≤ F.card)
    (a b : ℕ → ℤ) (hab : ∀ D ∈ F, a D * (r : ℤ) + b D * (D : ℤ) = 1)
    (W : Finset ℕ) (hWN : ∀ w ∈ W, N < w) (hWk : W.card ≤ k) :
    ∃ D ∈ F, ∑ w ∈ W, badMeas N w ((a D : ℝ) / D - lwd N) ((a D : ℝ) / D + lwd N) < 2 * lwd N := by
  classical
  by_contra hcon
  push Not at hcon
  have hFsub : F ⊆ Finset.Icc (N + 1 + r) (2 * N - 1) := by
    intro D hD
    have h := hF D hD
    exact Finset.mem_Icc.mpr ⟨h.1, by omega⟩
  have hFle : F.card ≤ 2 * N - 1 + 1 - (N + 1 + r) :=
    (Finset.card_le_card hFsub).trans (Nat.card_Icc _ _).le
  have hN2 : F.card + 2 ≤ N := by omega
  have hCk : 7 ≤ C * k := le_trans (by norm_num) (Nat.mul_le_mul hC hk)
  have hN : 10 ≤ N := by omega
  have hNR : (10 : ℝ) ≤ N := by exact_mod_cast hN
  have hNpos : (0 : ℝ) < N := by linarith
  have hd0 : 0 < lwd N := lwd_pos (by omega)
  obtain ⟨Ws, hWs⟩ : ∃ Ws : Finset ℕ,
      Ws = W.filter (fun w : ℕ => 2 * (w : ℝ) ≤ (2 * (N : ℝ) - 1) * N * (N - 2)) := ⟨_, rfl⟩
  obtain ⟨Wo, hWo⟩ : ∃ Wo : Finset ℕ,
      Wo = W.filter (fun w : ℕ => ¬ (2 * (w : ℝ) ≤ (2 * (N : ℝ) - 1) * N * (N - 2))) := ⟨_, rfl⟩
  have hWcard : Ws.card + Wo.card = W.card := by
    rw [hWs, hWo]
    exact Finset.card_filter_add_card_filter_not (s := W)
      (fun w : ℕ => 2 * (w : ℝ) ≤ (2 * (N : ℝ) - 1) * N * (N - 2))
  set M : ℕ → ℕ → ℝ := fun w D =>
    badMeas N w ((a D : ℝ) / D - lwd N) ((a D : ℝ) / D + lwd N) with hM
  have hsplit : ∀ D, ∑ w ∈ W, M w D = ∑ w ∈ Ws, M w D + ∑ w ∈ Wo, M w D := by
    intro D
    rw [hWs, hWo]
    exact (Finset.sum_filter_add_sum_filter_not W _ _).symm
  -- small speeds
  have hS1 : ∑ D ∈ F, ∑ w ∈ Ws, M w D ≤ Ws.card * (C * (2 * lwd N)) := by
    rw [Finset.sum_comm]
    calc ∑ w ∈ Ws, ∑ D ∈ F, M w D ≤ ∑ w ∈ Ws, C * (2 * lwd N) := by
          apply Finset.sum_le_sum
          intro w hw
          rw [hWs] at hw
          obtain ⟨hwW, hsm⟩ := Finset.mem_filter.mp hw
          exact hS hN hr1 hr2 w (hWN w hwW) hsm F hF hcop a b hab
      _ = Ws.card * (C * (2 * lwd N)) := by simp
  -- oscillating speeds
  have hS2 : ∑ D ∈ F, ∑ w ∈ Wo, M w D ≤ F.card * (Wo.card * (7 / (N : ℝ) * (2 * lwd N))) := by
    calc ∑ D ∈ F, ∑ w ∈ Wo, M w D ≤ ∑ D ∈ F, Wo.card * (7 / (N : ℝ) * (2 * lwd N)) := by
          apply Finset.sum_le_sum
          intro D hD
          calc ∑ w ∈ Wo, M w D ≤ ∑ w ∈ Wo, 7 / (N : ℝ) * (2 * lwd N) := by
                apply Finset.sum_le_sum
                intro w hw
                rw [hWo] at hw
                obtain ⟨_, hos⟩ := Finset.mem_filter.mp hw
                have hos' : (2 * (N : ℝ) - 1) * N * (N - 2) < 2 * (w : ℝ) := not_le.mp hos
                have := badMeas_osc hN hos' (lo := (a D : ℝ) / D - lwd N) (hi := (a D : ℝ) / D + lwd N)
                  (by ring)
                have e : ((a D : ℝ) / D + lwd N) - ((a D : ℝ) / D - lwd N) = 2 * lwd N := by ring
                rw [e] at this
                exact this
            _ = Wo.card * (7 / (N : ℝ) * (2 * lwd N)) := by simp
      _ = F.card * (Wo.card * (7 / (N : ℝ) * (2 * lwd N))) := by simp
  have hall : (F.card : ℝ) * (2 * lwd N) ≤ ∑ D ∈ F, ∑ w ∈ W, M w D := by
    calc (F.card : ℝ) * (2 * lwd N) = ∑ D ∈ F, 2 * lwd N := by simp
      _ ≤ ∑ D ∈ F, ∑ w ∈ W, M w D := Finset.sum_le_sum (fun D hD => hcon D hD)
  have htot : ∑ D ∈ F, ∑ w ∈ W, M w D = ∑ D ∈ F, ∑ w ∈ Ws, M w D + ∑ D ∈ F, ∑ w ∈ Wo, M w D := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl (fun D _ => hsplit D)
  have hcomb : (F.card : ℝ) * (2 * lwd N) ≤
      Ws.card * (C * (2 * lwd N)) + F.card * (Wo.card * (7 / (N : ℝ) * (2 * lwd N))) := by
    linarith
  -- divide by 2 lwd
  have hdiv : (F.card : ℝ) ≤ C * Ws.card + F.card * Wo.card * (7 / (N : ℝ)) := by
    have h2 : 0 < 2 * lwd N := by linarith
    have e : Ws.card * (C * (2 * lwd N)) + F.card * (Wo.card * (7 / (N : ℝ) * (2 * lwd N))) =
        (C * Ws.card + F.card * Wo.card * (7 / (N : ℝ))) * (2 * lwd N) := by ring
    rw [e] at hcomb
    exact le_of_mul_le_mul_right hcomb h2
  have hmul : (N : ℝ) * F.card ≤ C * Ws.card * N + 7 * F.card * Wo.card := by
    have := mul_le_mul_of_nonneg_left hdiv hNpos.le
    have e : (N : ℝ) * (C * Ws.card + F.card * Wo.card * (7 / (N : ℝ))) =
        C * Ws.card * N + 7 * F.card * Wo.card := by
      field_simp
    linarith
  have hp : (Ws.card : ℝ) + Wo.card + 0 ≤ k := by
    have : Ws.card + Wo.card ≤ k := by omega
    have h' : ((Ws.card + Wo.card : ℕ) : ℝ) ≤ k := by exact_mod_cast this
    push_cast at h'
    linarith
  have hf1 : ((C : ℝ) * k + 1) ≤ F.card := by exact_mod_cast hcard
  have hC7 : (7 : ℝ) ≤ C := by exact_mod_cast hC
  have hfN : (F.card : ℝ) + 2 ≤ N := by exact_mod_cast hN2
  have t1 : 0 ≤ ((F.card : ℝ) - C * k - 1) * N := mul_nonneg (by linarith) hNpos.le
  have t2 : 0 ≤ (Wo.card : ℝ) * (C * N - 7 * F.card) :=
    mul_nonneg (Nat.cast_nonneg _) (by nlinarith)
  have t3 : 0 ≤ ((k : ℝ) - Ws.card - Wo.card) * (C * N) :=
    mul_nonneg (by linarith) (by positivity)
  nlinarith [t1, t2, t3]

end LinL

open LinL

/-- **Theorem L, Finset form, generic constant `C ≥ 7` with the per-speed total bound `SmallTot C N r`.**
One time `t` serves every retained speed and every added speed. -/
theorem robust_core_linC {C k N r : ℕ} (hC : 7 ≤ C) (hS : SmallTot C N r) (hk : 1 ≤ k) (hr1 : 1 ≤ r)
    (hr2 : r + 2 ≤ N)
    (hP : CopWinT (C * k + 1) N r)
    (W : Finset ℕ) (hWN : ∀ w ∈ W, N < w) (hWk : W.card ≤ k) :
    ∃ t : ℝ, (∀ x : ℕ, 1 ≤ x → x ≤ N → x ≠ r → 1 / (N : ℝ) ≤ nearestIntDist ((x : ℝ) * t)) ∧
      ∀ w ∈ W, 1 / (N : ℝ) ≤ nearestIntDist ((w : ℝ) * t) := by
  classical
  obtain ⟨F, hFcard, hFprop, hFcop⟩ := hP
  have hab' : ∀ D ∈ F, ∃ a b : ℤ, a * (r : ℤ) + b * (D : ℤ) = 1 := by
    intro D hD
    obtain ⟨a, b, h⟩ := Nat.isCoprime_iff_coprime.mpr (hFprop D hD).2.2.symm
    exact ⟨a, b, h⟩
  choose! a b hab using hab'
  have hF2 : ∀ D ∈ F, N + 1 + r ≤ D ∧ D + 1 ≤ 2 * N := fun D hD =>
    ⟨(hFprop D hD).1, (hFprop D hD).2.1⟩
  obtain ⟨D, hDF, hDsum⟩ := LinL.exists_alive hC hS hk hr1 hr2 F hF2 hFcop hFcard a b hab W hWN hWk
  obtain ⟨hDge, hDle, _⟩ := hFprop D hDF
  have hDpos : 0 < D := by omega
  have hN0 : 0 < N := by omega
  have hd0 : 0 < LinL.lwd N := LinL.lwd_pos (by omega)
  have hDR : (0 : ℝ) < D := by exact_mod_cast hDpos
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN0
  have hsum : ∑ w ∈ W, LinL.badMeas N w ((a D : ℝ) / D - LinL.lwd N) ((a D : ℝ) / D + LinL.lwd N) <
      ((a D : ℝ) / D + LinL.lwd N) - ((a D : ℝ) / D - LinL.lwd N) := by
    have e : ((a D : ℝ) / D + LinL.lwd N) - ((a D : ℝ) / D - LinL.lwd N) = 2 * LinL.lwd N := by ring
    rw [e]
    exact hDsum
  obtain ⟨t, ht, hgood⟩ := LinL.exists_good_point_gen ((a D : ℝ) / D - LinL.lwd N)
    ((a D : ℝ) / D + LinL.lwd N) (by linarith) N W hsum
  have hDle' : (D : ℝ) ≤ 2 * N - 1 := by
    have : (D : ℝ) + 1 ≤ 2 * N := by exact_mod_cast hDle
    linarith
  have ht' : |t - (a D : ℝ) / D| ≤ 1 / ((D : ℝ) * N * N) := by
    have h1 : |t - (a D : ℝ) / D| ≤ LinL.lwd N := by
      rw [abs_le]; constructor <;> linarith [ht.1, ht.2]
    have h2 : LinL.lwd N ≤ 1 / ((D : ℝ) * N * N) := by
      unfold LinL.lwd
      apply one_div_le_one_div_of_le (by positivity)
      nlinarith [mul_pos hNR hNR]
    linarith
  refine ⟨t, ?_, hgood⟩
  intro x hx1 hxN hxr
  obtain ⟨c0, c1, c2⟩ := retained_cond (N := N) (r := r) hDge hx1 hxN hxr
  exact far_window hDpos hDle hN0 hN0 (r : ℤ) (a D) (b D) (hab D hDF) hxN c0 c1 c2 ht'

/-- **Theorem L, speed-vector form, generic constant.** -/
theorem ML_ge_robust_linC {C n k N r : ℕ} (hC : 7 ≤ C) (hS : SmallTot C N r) (hk : 1 ≤ k)
    (hr1 : 1 ≤ r) (hr2 : r + 2 ≤ N)
    (hP : CopWinT (C * k + 1) N r) (v : Fin (n + 1) → ℤ)
    (hv : ∀ i, (1 ≤ v i ∧ v i ≤ (N : ℤ) ∧ v i ≠ (r : ℤ)) ∨ (N : ℤ) < v i)
    (hcard : (Finset.univ.filter (fun i : Fin (n + 1) => (N : ℤ) < v i)).card ≤ k) :
    1 / (N : ℝ) ≤ ML v := by
  classical
  obtain ⟨t, ht1, ht2⟩ := robust_core_linC hC hS hk hr1 hr2 hP
    ((Finset.univ.filter (fun i : Fin (n + 1) => (N : ℤ) < v i)).image (fun i => (v i).toNat))
    (by
      intro w hw
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hw
      have := (Finset.mem_filter.mp hi).2
      omega)
    (Finset.card_image_le.trans hcard)
  refine ML_ge_of_far v (1 / (N : ℝ)) t ?_
  intro i
  have e : 0 ≤ v i → ((v i : ℤ) : ℝ) = (((v i).toNat : ℕ) : ℝ) := by
    intro hnn
    have h := Int.toNat_of_nonneg hnn
    exact_mod_cast h.symm
  rcases hv i with ⟨h1, h2, h3⟩ | hbig
  · rw [e (by omega)]
    apply ht1 <;> omega
  · rw [e (by omega)]
    apply ht2
    exact Finset.mem_image.mpr ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hbig⟩, rfl⟩

/-- **Theorem L (Stage A), Finset form** (constant 18). -/
theorem robust_core_lin {k N r : ℕ} (hk : 1 ≤ k) (hr1 : 1 ≤ r) (hr2 : r + 2 ≤ N)
    (hP : CopWinT (18 * k + 1) N r)
    (W : Finset ℕ) (hWN : ∀ w ∈ W, N < w) (hWk : W.card ≤ k) :
    ∃ t : ℝ, (∀ x : ℕ, 1 ≤ x → x ≤ N → x ≠ r → 1 / (N : ℝ) ≤ nearestIntDist ((x : ℝ) * t)) ∧
      ∀ w ∈ W, 1 / (N : ℝ) ≤ nearestIntDist ((w : ℝ) * t) :=
  robust_core_linC (by norm_num) (LinL.smallTot_18 N r) hk hr1 hr2 hP W hWN hWk

/-- **Theorem L (Stage A), speed-vector form.**  `v : Fin (n+1) → ℤ` with every entry either in
`[1,N] \ {r}` or `> N`, at most `k` entries `> N`; `CopWinT (18k+1) N r`.  Then `1/N ≤ ML v`. -/
theorem ML_ge_robust_lin {n k N r : ℕ} (hk : 1 ≤ k) (hr1 : 1 ≤ r) (hr2 : r + 2 ≤ N)
    (hP : CopWinT (18 * k + 1) N r) (v : Fin (n + 1) → ℤ)
    (hv : ∀ i, (1 ≤ v i ∧ v i ≤ (N : ℤ) ∧ v i ≠ (r : ℤ)) ∨ (N : ℤ) < v i)
    (hcard : (Finset.univ.filter (fun i : Fin (n + 1) => (N : ℤ) < v i)).card ≤ k) :
    1 / (N : ℝ) ≤ ML v :=
  ML_ge_robust_linC (by norm_num) (LinL.smallTot_18 N r) hk hr1 hr2 hP v hv hcard

end Gap
end Sext6
end LRSpectrumFull
