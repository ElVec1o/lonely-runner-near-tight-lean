import LRSpectrumFull.Sext6.Gap.OEAll
import LRSpectrumFull.Sext6.Gap.OneOverR
import LRSpectrumFull.Sext6.Gap.Value
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Proposition 1.3 and Theorem FS1 (Fan-Sun shape of the one-entry values)  [2026-11-25]

Source: the accompanying paper draft (Proposition 1.3) and the accompanying notes on Theorem FS1.
`N = k + 1` is the number of speeds, `A = N + 1`, `s = N + 1 - r`, `β = betaFam N r`.

* `prop13_ks`   : arithmetic core `(β - m t)(t + 1) < β` from `β < m (t + 1)`, `t ≥ 1` (`t = N - r = s - 1`).
* `prop13_int`  : EXACT corrected form of Proposition 1.3 (no sign claim on `k`): under `Spec N r m β` and `β < m s`
                  there is an integer `k = β - m (s - 1)` with `m r + β = m N + k`, `2 k ≤ N`,
                  `k = 1` if `r = N`, `k s < β` if `r < N`.  (`β < m s` does NOT force `k ≥ 1`: `N=10, r=6, m=2` has `k = -3`.)
* `prop13`      : the same in `ℕ` when additionally `m N < m r + β` (i.e. the value `m/(m r + β)` is `< 1/N`): then `1 ≤ k`.
* `FS1_of_OE`   : Theorem FS1 from the one-entry lower bound (OE-low) as a hypothesis.
* `FS1_upto`    : unconditional for `14 ≤ N ≤ 100000` (uses `OE_low_upto`).
* `FS1_all`     : all `N ≥ 14`, hypothesis `DusartPi` (via `OE_low_all`).
* `FS1_shape_*` : the Fan-Sun shape: `ML ≥ 1/N` or `ML = σ/(σ N + κ)` with `1 ≤ κ`, `2 κ ≤ N`.
No `sorry`, no `axiom`.

Convention: `N = k + 1` is the number of speeds of the vector `v : Fin (k+1) → ℤ`. Speeds are the moving runners; the runner at rest is not counted, so a vector of `N` speeds means `N + 1` runners and the Lonely Runner value is `1/(N+1)`.
Hypotheses: `DusartPi` (Dusart's explicit prime-counting bounds, an imported statement carried as a `Prop` hypothesis, never an axiom) is a hypothesis only of the declarations whose statements mention it; the unconditional, `_small`, `_upto` and table statements do not use it.
Axiom audit: covered by `Axioms13` (also reached through the imports of `Axioms16`) (`#print axioms`; declarations not printed there are bricks of printed ones, so their axioms are bounded by the printed lines).
-/

namespace LRSpectrumFull
namespace Sext6
namespace Gap

/-- Arithmetic core of Proposition 1.3: `(β - m t)(t + 1) < β` when `1 ≤ t` and `β < m (t + 1)`. -/
theorem prop13_ks {m t β : ℕ} (ht : 1 ≤ t) (hnt : β < m * (t + 1)) :
    ((β : ℤ) - m * t) * ((t : ℤ) + 1) < β := by
  have h1 : (β : ℤ) < m * (t + 1) := by exact_mod_cast hnt
  have h2 : (0 : ℤ) < t := by exact_mod_cast ht
  have h3 : (β : ℤ) * t < (m * (t + 1)) * t := mul_lt_mul_of_pos_right h1 h2
  nlinarith [h3]

/-- **Proposition 1.3, exact form.**  `k = β - m (s - 1)` with `s = N + 1 - r`. -/
theorem prop13_int {N r m β : ℕ} (hS : Spec N r m β) (hnt : β < m * (N + 1 - r)) :
    ∃ k : ℤ, ((m * r + β : ℕ) : ℤ) = (m : ℤ) * N + k ∧ 2 * k ≤ N ∧
      (r = N → k = 1) ∧ (r < N → k * ((N : ℤ) + 1 - r) < β) := by
  have hr2 := hS.hr2
  have hbN := hS.beta_le_N
  have h2r := hS.two_le_r
  have hb1 := hS.hb1
  obtain ⟨t, rfl⟩ : ∃ t, N = r + t := ⟨N - r, by omega⟩
  have hnt' : β < m * (t + 1) := by
    have e : r + t + 1 - r = t + 1 := by omega
    rw [e] at hnt
    exact hnt
  have hr2' : (2 : ℤ) ≤ r := by exact_mod_cast h2r
  refine ⟨(β : ℤ) - m * t, ?_, ?_, ?_, ?_⟩
  · push_cast
    ring
  · by_cases ht0 : t = 0
    · subst ht0
      have hb1' : β ≤ 1 := hS.hb3 1 (by omega) (Nat.coprime_one_left r)
      have hb2' : β = 1 := by omega
      subst hb2'
      first
        | linarith
        | (push_cast; linarith)
        | (norm_num; linarith)
    · have ht : 1 ≤ t := by omega
      by_cases hk0 : (β : ℤ) - m * t ≤ 0
      · have h0 : (0 : ℤ) ≤ (r : ℤ) + (t : ℤ) := by positivity
        push_cast
        linarith
      · have hkpos : (0 : ℤ) < (β : ℤ) - m * t := by linarith
        have key := prop13_ks ht hnt'
        have hbN' : (β : ℤ) ≤ (r : ℤ) + (t : ℤ) := by exact_mod_cast hbN
        have ht1 : (0 : ℤ) ≤ (t : ℤ) - 1 := by
          have : (1 : ℤ) ≤ t := by exact_mod_cast ht
          linarith
        have hmul := mul_nonneg hkpos.le ht1
        push_cast
        nlinarith [key, hbN', hmul]
  · intro h
    have ht0 : t = 0 := by omega
    subst ht0
    have hb1' : β ≤ 1 := hS.hb3 1 (by omega) (Nat.coprime_one_left r)
    have hb2' : β = 1 := by omega
    subst hb2'
    first
      | norm_num
      | (push_cast; ring)
      | simp
  · intro h
    have ht : 1 ≤ t := by omega
    have key := prop13_ks ht hnt'
    push_cast
    nlinarith [key]

/-- **Proposition 1.3 in `ℕ`.**  If moreover `m N < m r + β` (value `< 1/N`) then `1 ≤ k`. -/
theorem prop13 {N r m β : ℕ} (hS : Spec N r m β) (hnt : β < m * (N + 1 - r))
    (hlt : m * N < m * r + β) :
    ∃ k : ℕ, 1 ≤ k ∧ 2 * k ≤ N ∧ m * r + β = m * N + k ∧
      (r = N → k = 1) ∧ (r < N → k * (N + 1 - r) < β) := by
  have hr2 := hS.hr2
  obtain ⟨k, hk1, hk2, hk3, hk4⟩ := prop13_int hS hnt
  have hlt' : (m : ℤ) * N < m * r + β := by exact_mod_cast hlt
  have hcast : ((m * r + β : ℕ) : ℤ) = (m : ℤ) * r + β := by push_cast; ring
  have hkpos : (1 : ℤ) ≤ k := by linarith
  obtain ⟨k0, rfl⟩ := Int.eq_ofNat_of_zero_le (by omega : (0 : ℤ) ≤ k)
  refine ⟨k0, by omega, by omega, ?_, ?_, ?_⟩
  · have hk1' : (m : ℤ) * r + β = (m : ℤ) * N + k0 := by
      have h7 := hk1
      push_cast at h7
      exact h7
    exact_mod_cast hk1'
  · intro h
    have := hk3 h
    exact_mod_cast this
  · intro h
    have h6 := hk4 h
    have hsub : ((N + 1 - r : ℕ) : ℤ) = (N : ℤ) + 1 - r := by omega
    rw [← hsub] at h6
    exact_mod_cast h6

/-- **Theorem FS1** from the one-entry lower bound `hOE` (OE-low) as a hypothesis, `N ≥ 14`.
Every one-entry modification `([N] \ {r}) ∪ {w}` has `ML ≥ 1/N`, or `2r > N`, `w = m r` with `m ≥ 2`, and either
`ML = 1/(N+1)` (tight) or `ML = m/(m N + κ)` with `1 ≤ κ`, `2 κ ≤ N`. -/
theorem FS1_of_OE {k N : ℕ} (hk : k + 1 = N) (hN : 14 ≤ N)
    (hOE : ∀ r w : ℕ, 1 ≤ r → 2 * r ≤ N → N < w → 1 / (N : ℝ) ≤ ML (wFam k r w))
    {r w : ℕ} (hr1 : 1 ≤ r) (hrN : r ≤ N) (hw : N < w) :
    1 / (N : ℝ) ≤ ML (wFam k r w) ∨
    (N < 2 * r ∧ ∃ m : ℕ, 2 ≤ m ∧ w = m * r ∧
      (ML (wFam k r w) = 1 / ((N : ℝ) + 1) ∨
       ∃ κ : ℕ, 1 ≤ κ ∧ 2 * κ ≤ N ∧ ML (wFam k r w) = (m : ℝ) / ((m * N + κ : ℕ) : ℝ))) := by
  by_cases h2r : 2 * r ≤ N
  · exact Or.inl (hOE r w hr1 h2r hw)
  · have hr1' : N < 2 * r := by omega
    have hN2 : 2 ≤ N := by omega
    by_cases hdiv : r ∣ w
    · obtain ⟨m, hm⟩ := hdiv
      have hmw : w = m * r := by rw [hm, Nat.mul_comm]
      have hm2 : 2 ≤ m := by
        by_contra hcon
        have hm1 : m ≤ 1 := by omega
        have hle : r * m ≤ r * 1 := Nat.mul_le_mul_left r hm1
        omega
      have hV : ML (wFam k r w) = ML (vFam k r m) := by rw [hmw, vFam_eq_wFam]
      by_cases htight : m * sFam N r ≤ betaFam N r
      · refine Or.inr ⟨hr1', m, hm2, hmw, Or.inl ?_⟩
        rw [hV]
        exact (theoremV_tight_iff hk hN2 hr1' hrN hm2).2 htight
      · have hnt : betaFam N r < m * sFam N r := by omega
        have hS := spec_betaFam hN2 hr1' hrN hm2
        have hval : ML (vFam k r m) = (m : ℝ) / ((m * r + betaFam N r : ℕ) : ℝ) := by
          rw [theoremV_alt hk hN2 hr1' hrN hm2, min_eq_left hnt.le]
        by_cases hlt : m * N < m * r + betaFam N r
        · have hnt2 : betaFam N r < m * (N + 1 - r) := hnt
          obtain ⟨κ, hκ1, hκ2, hκ3, -, -⟩ := prop13 hS hnt2 hlt
          refine Or.inr ⟨hr1', m, hm2, hmw, Or.inr ⟨κ, hκ1, hκ2, ?_⟩⟩
          rw [hV, hval, hκ3]
        · refine Or.inl ?_
          rw [hV, hval]
          have hle : m * r + betaFam N r ≤ m * N := by omega
          have hNpos : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
          have hDpos : (0 : ℝ) < ((m * r + betaFam N r : ℕ) : ℝ) := by
            have hbp := hS.beta_pos
            exact_mod_cast (by omega : 0 < m * r + betaFam N r)
          rw [div_le_div_iff₀ hNpos hDpos]
          have hle' : ((m * r + betaFam N r : ℕ) : ℝ) ≤ (m : ℝ) * N := by exact_mod_cast hle
          linarith
    · refine Or.inl ?_
      have h1 := ML_ge_inv hk hr1' hrN hdiv
      have hr0 : (0 : ℝ) < r := by exact_mod_cast (by omega : 0 < r)
      have h2 : 1 / (N : ℝ) ≤ 1 / (r : ℝ) :=
        one_div_le_one_div_of_le hr0 (by exact_mod_cast hrN)
      exact h2.trans h1

/-- **Theorem FS1, unconditional for `14 ≤ N ≤ 10^5`.** -/
theorem FS1_upto {k N r w : ℕ} (hk : k + 1 = N) (hN : 14 ≤ N) (hNb : N ≤ 100000)
    (hr1 : 1 ≤ r) (hrN : r ≤ N) (hw : N < w) :
    1 / (N : ℝ) ≤ ML (wFam k r w) ∨
    (N < 2 * r ∧ ∃ m : ℕ, 2 ≤ m ∧ w = m * r ∧
      (ML (wFam k r w) = 1 / ((N : ℝ) + 1) ∨
       ∃ κ : ℕ, 1 ≤ κ ∧ 2 * κ ≤ N ∧ ML (wFam k r w) = (m : ℝ) / ((m * N + κ : ℕ) : ℝ))) :=
  FS1_of_OE hk hN (fun r' w' h1 h2 h3 => OE_low_upto hk hN hNb h1 h2 h3) hr1 hrN hw

/-- **Theorem FS1, all `N ≥ 14`**, hypothesis `DusartPi` (used only for `N > 10^5`, inside `OE_low_all`). -/
theorem FS1_all (hD : DusartPi) {k N r w : ℕ} (hk : k + 1 = N) (hN : 14 ≤ N)
    (hr1 : 1 ≤ r) (hrN : r ≤ N) (hw : N < w) :
    1 / (N : ℝ) ≤ ML (wFam k r w) ∨
    (N < 2 * r ∧ ∃ m : ℕ, 2 ≤ m ∧ w = m * r ∧
      (ML (wFam k r w) = 1 / ((N : ℝ) + 1) ∨
       ∃ κ : ℕ, 1 ≤ κ ∧ 2 * κ ≤ N ∧ ML (wFam k r w) = (m : ℝ) / ((m * N + κ : ℕ) : ℝ))) :=
  FS1_of_OE hk hN (fun r' w' h1 h2 h3 => OE_low_all hD hk hN h1 h2 h3) hr1 hrN hw

/-- Fan-Sun shape: `ML ≥ 1/N` or `ML = σ/(σ N + κ)` with `1 ≤ σ`, `1 ≤ κ ≤ N/2`. -/
theorem FS1_shape_of_OE {k N : ℕ} (hk : k + 1 = N) (hN : 14 ≤ N)
    (hOE : ∀ r w : ℕ, 1 ≤ r → 2 * r ≤ N → N < w → 1 / (N : ℝ) ≤ ML (wFam k r w))
    {r w : ℕ} (hr1 : 1 ≤ r) (hrN : r ≤ N) (hw : N < w) :
    1 / (N : ℝ) ≤ ML (wFam k r w) ∨
      ∃ σ κ : ℕ, 1 ≤ σ ∧ 1 ≤ κ ∧ 2 * κ ≤ N ∧
        ML (wFam k r w) = (σ : ℝ) / ((σ * N + κ : ℕ) : ℝ) := by
  rcases FS1_of_OE hk hN hOE hr1 hrN hw with h | ⟨_, m, hm2, _, h | ⟨κ, hκ1, hκ2, hκ⟩⟩
  · exact Or.inl h
  · refine Or.inr ⟨1, 1, le_rfl, le_rfl, by omega, ?_⟩
    rw [h]
    simp
  · exact Or.inr ⟨m, κ, by omega, hκ1, hκ2, hκ⟩

theorem FS1_shape_upto {k N r w : ℕ} (hk : k + 1 = N) (hN : 14 ≤ N) (hNb : N ≤ 100000)
    (hr1 : 1 ≤ r) (hrN : r ≤ N) (hw : N < w) :
    1 / (N : ℝ) ≤ ML (wFam k r w) ∨
      ∃ σ κ : ℕ, 1 ≤ σ ∧ 1 ≤ κ ∧ 2 * κ ≤ N ∧
        ML (wFam k r w) = (σ : ℝ) / ((σ * N + κ : ℕ) : ℝ) :=
  FS1_shape_of_OE hk hN (fun r' w' h1 h2 h3 => OE_low_upto hk hN hNb h1 h2 h3) hr1 hrN hw

theorem FS1_shape_all (hD : DusartPi) {k N r w : ℕ} (hk : k + 1 = N) (hN : 14 ≤ N)
    (hr1 : 1 ≤ r) (hrN : r ≤ N) (hw : N < w) :
    1 / (N : ℝ) ≤ ML (wFam k r w) ∨
      ∃ σ κ : ℕ, 1 ≤ σ ∧ 1 ≤ κ ∧ 2 * κ ≤ N ∧
        ML (wFam k r w) = (σ : ℝ) / ((σ * N + κ : ℕ) : ℝ) :=
  FS1_shape_of_OE hk hN (fun r' w' h1 h2 h3 => OE_low_all hD hk hN h1 h2 h3) hr1 hrN hw

end Gap
end Sext6
end LRSpectrumFull
