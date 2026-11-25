import LRSpectrumFull.Sext6.Gap.InsLIP

/-!
# Theorem INS, part 5: descent D1, D3 and the easy half of D2  [2026-11-25]

Source: the accompanying notes on single-speed insertion, sections 5, 6, 7.
Here `N = k + 2 = |V|` is the number of speeds (moving runners) of `V = (v, w)`, `v : Fin (k+1) → ℤ`;
counting the runner at rest there are `N + 1` runners, and the Lonely Runner value of `V` is `1/(N+1)`.

* `descent_D1` : `M ≥ 2`, `k ≥ 1` (so `N ≥ 3`), `w ≥ (2M - 1) M`, `ML (v, w) < 1/N` imply `ML v ≤ 1/N`.
* `descent_D2_forward` : under the same hypotheses, `ML (v, w) < 1/N` implies `ML v ≤ 1/N` and
  `‖w p‖ < 1/N` at every time `p` with `gap v p = 1/N`.
* `descent_D3` : if `ML v ≥ 1/(k+2)` (this is LRC for the `k+1` speeds of `v`) and `ML (v, w) ≤ 1/(k+3)`,
  then `w ≤ (k+2) M`; `LRCHyp` is the hypothesis "LRC for `k+1` speeds" as a predicate and
  `descent_D3_of_LRC` the form that consumes it (`v` injective).
No `sorry`, no `axiom`.

Convention: `v : Fin (k+1) → ℤ` has `k + 1` speeds; `V = (v, w) = Fin.snoc v w` (integer `w`) has `N = k + 2` speeds (moving runners), i.e. `N + 1` runners counting the one at rest. The Lonely Runner value of `V` is `1/(N+1) = 1/(k+3)`; the threshold of D1, D2 is `1/N`.
Hypotheses: `LRCHyp k` (the Lonely Runner statement for `k + 1` distinct speeds) is a `Prop` hypothesis predicate used only by `descent_D3_of_LRC`; it is never instantiated in this development. `descent_D3` itself assumes `ML v ≥ 1/(k+2)` directly. Other numerical hypotheses are those of the individual statements.
Axiom audit: covered by `Axioms20` (`#print axioms`; declarations not printed there are bricks of printed ones, so their axioms are bounded by the printed lines).
-/

namespace LRSpectrumFull
namespace Sext6
namespace Gap

theorem descent_D1 {k : ℕ} (v : Fin (k + 1) → ℤ) (hv : ∀ i, 0 < v i) (M : ℤ)
    (hM : ∀ i, v i ≤ M) (hM2 : 2 ≤ M) (hk : 1 ≤ k) (w : ℤ) (hw : (2 * M - 1) * M ≤ w)
    (hlt : ML (Fin.snoc v w : Fin (k + 2) → ℤ) < 1 / ((k : ℝ) + 2)) :
    ML v ≤ 1 / ((k : ℝ) + 2) := by
  by_contra hcon
  push_neg at hcon
  have hN : (0 : ℝ) < (k : ℝ) + 2 := by positivity
  have hkR : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
  have hw0 : 0 < w := by
    nlinarith [mul_pos (by omega : (0 : ℤ) < 2 * M - 1) (by omega : (0 : ℤ) < M)]
  have hwR : (0 : ℝ) < (w : ℝ) := by exact_mod_cast hw0
  have hM0R : (2 : ℝ) ≤ (M : ℝ) := by exact_mod_cast hM2
  have hwM : (0 : ℝ) < (w : ℝ) + M := by linarith
  have hwreal : (2 * (M : ℝ) - 1) * M ≤ w := by exact_mod_cast hw
  have hLIP := ML_snoc_ge_LIP v hv M hM w hw0
  rw [div_le_iff₀ hwM] at hLIP
  have hX : ML (Fin.snoc v w : Fin (k + 2) → ℤ) * ((k : ℝ) + 2) < 1 :=
    (lt_div_iff₀ hN).mp hlt
  have hL1' : ((k : ℝ) + 2) * ((w : ℝ) * ML v) < (w : ℝ) + M := by
    have h1 := mul_le_mul_of_nonneg_left hLIP hN.le
    have h2 := mul_lt_mul_of_pos_right hX hwM
    nlinarith
  rcases (ML_le_half v).lt_or_eq with hL | hL
  · have hL0 : 0 < ML v := lt_trans (by positivity) hcon
    obtain ⟨t0, -, ht0⟩ := exists_gap_eq_ML v
    obtain ⟨a, d, hd, hdM, -, b, hb⟩ := equality_time_rational v hv M hM t0 ht0 hL0 hL
    have hdR : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd
    have hdne : (d : ℝ) ≠ 0 := hdR.ne'
    have hdL : (d : ℝ) * ML v = b := by rw [hb]; field_simp
    have hc2 : 1 < ML v * ((k : ℝ) + 2) := (div_lt_iff₀ hN).mp hcon
    have hlt1 : (d : ℝ) < b * ((k : ℝ) + 2) := by
      have : (d : ℝ) * 1 < d * (ML v * ((k : ℝ) + 2)) := mul_lt_mul_of_pos_left hc2 hdR
      nlinarith
    have hint : (d : ℤ) < b * ((k : ℤ) + 2) := by exact_mod_cast hlt1
    have hint2 : (d : ℤ) + 1 ≤ b * ((k : ℤ) + 2) := by linarith
    have hreal : (d : ℝ) + 1 ≤ b * ((k : ℝ) + 2) := by exact_mod_cast hint2
    have e1 : (b : ℝ) * ((k : ℝ) + 2) = d * (ML v * ((k : ℝ) + 2)) := by rw [← hdL]; ring
    have s1 : ((d : ℝ) + 1) * w ≤ (b * ((k : ℝ) + 2)) * w :=
      mul_le_mul_of_nonneg_right hreal hwR.le
    have s2 : (d : ℝ) * (((k : ℝ) + 2) * ((w : ℝ) * ML v)) < d * ((w : ℝ) + M) :=
      mul_lt_mul_of_pos_left hL1' hdR
    have e2 : (b : ℝ) * ((k : ℝ) + 2) * w = d * (((k : ℝ) + 2) * ((w : ℝ) * ML v)) := by
      rw [e1]; ring
    have hwd : (w : ℝ) < d * M := by nlinarith
    have hdM' : (d : ℝ) ≤ 2 * M - 1 := by exact_mod_cast hdM
    have : (d : ℝ) * M ≤ (2 * (M : ℝ) - 1) * M :=
      mul_le_mul_of_nonneg_right hdM' (by linarith)
    linarith
  · rw [hL] at hL1'
    have h1 : 1 * (w : ℝ) ≤ (k : ℝ) * w := mul_le_mul_of_nonneg_right hkR hwR.le
    have h2 : 0 ≤ (M : ℝ) * ((M : ℝ) - 2) := mul_nonneg (by linarith) (by linarith)
    nlinarith

theorem descent_D2_forward {k : ℕ} (v : Fin (k + 1) → ℤ) (hv : ∀ i, 0 < v i) (M : ℤ)
    (hM : ∀ i, v i ≤ M) (hM2 : 2 ≤ M) (hk : 1 ≤ k) (w : ℤ) (hw : (2 * M - 1) * M ≤ w)
    (hlt : ML (Fin.snoc v w : Fin (k + 2) → ℤ) < 1 / ((k : ℝ) + 2)) :
    ML v ≤ 1 / ((k : ℝ) + 2) ∧
      ∀ p : ℝ, gap v p = 1 / ((k : ℝ) + 2) → nearestIntDist ((w : ℝ) * p) < 1 / ((k : ℝ) + 2) := by
  refine ⟨descent_D1 v hv M hM hM2 hk w hw hlt, ?_⟩
  intro p hp
  by_contra hcon
  push_neg at hcon
  have : 1 / ((k : ℝ) + 2) ≤ ML (Fin.snoc v w : Fin (k + 2) → ℤ) := by
    apply ML_ge_of_far (Fin.snoc v w : Fin (k + 2) → ℤ) _ p
    intro i
    rcases Fin.eq_castSucc_or_eq_last i with ⟨j, rfl⟩ | rfl
    · rw [snoc_castSucc_eq]
      have := gap_le v p j
      rw [hp] at this
      exact this
    · rw [snoc_last_eq]
      exact hcon
  linarith

/-- The hypothesis "LRC for `k+1` speeds": every `k+1` distinct positive speeds have `ML ≥ 1/(k+2)`. -/
def LRCHyp (k : ℕ) : Prop :=
  ∀ u : Fin (k + 1) → ℤ, (∀ i, 0 < u i) → Function.Injective u → 1 / ((k : ℝ) + 2) ≤ ML u

/-- **D3** (per instance). -/
theorem descent_D3 {k : ℕ} (v : Fin (k + 1) → ℤ) (hv : ∀ i, 0 < v i) (M : ℤ)
    (hM : ∀ i, v i ≤ M) (w : ℤ) (hw : 0 < w) (hLRC : 1 / ((k : ℝ) + 2) ≤ ML v)
    (hV : ML (Fin.snoc v w : Fin (k + 2) → ℤ) ≤ 1 / ((k : ℝ) + 3)) :
    (w : ℝ) ≤ ((k : ℝ) + 2) * M := by
  have hw' : (0 : ℝ) < (w : ℝ) := by exact_mod_cast hw
  have hM1 : 1 ≤ M := by
    have := hv 0
    have := hM 0
    omega
  have hMR : (1 : ℝ) ≤ (M : ℝ) := by exact_mod_cast hM1
  have hwM : (0 : ℝ) < (w : ℝ) + M := by linarith
  have hk2 : (0 : ℝ) < (k : ℝ) + 2 := by positivity
  have hk3 : (0 : ℝ) < (k : ℝ) + 3 := by positivity
  have hLIP := ML_snoc_ge_LIP v hv M hM w hw
  rw [div_le_iff₀ hwM] at hLIP
  have h1 : ML (Fin.snoc v w : Fin (k + 2) → ℤ) * ((k : ℝ) + 3) ≤ 1 := by
    have := (le_div_iff₀ hk3).mp hV
    exact this
  have h2 : 1 ≤ ML v * ((k : ℝ) + 2) := (div_le_iff₀ hk2).mp hLRC
  have sa : ((k : ℝ) + 3) * ((w : ℝ) * ML v) ≤ (w : ℝ) + M := by
    nlinarith [mul_le_mul_of_nonneg_left hLIP hk3.le, mul_le_mul_of_nonneg_right h1 hwM.le]
  have sb : (w : ℝ) ≤ ((k : ℝ) + 2) * ((w : ℝ) * ML v) := by
    nlinarith [mul_le_mul_of_nonneg_left h2 hw'.le]
  have sc := mul_le_mul_of_nonneg_left sa hk2.le
  have sd := mul_le_mul_of_nonneg_left sb hk3.le
  nlinarith [sc, sd]

theorem descent_D3_of_LRC {k : ℕ} (hL : LRCHyp k) (v : Fin (k + 1) → ℤ) (hv : ∀ i, 0 < v i)
    (hinj : Function.Injective v) (M : ℤ) (hM : ∀ i, v i ≤ M) (w : ℤ) (hw : 0 < w)
    (hV : ML (Fin.snoc v w : Fin (k + 2) → ℤ) ≤ 1 / ((k : ℝ) + 3)) :
    (w : ℝ) ≤ ((k : ℝ) + 2) * M :=
  descent_D3 v hv M hM w hw (hL v hv hinj) hV

end Gap
end Sext6
end LRSpectrumFull
