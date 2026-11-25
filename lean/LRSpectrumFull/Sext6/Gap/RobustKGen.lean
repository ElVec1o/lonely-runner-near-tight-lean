import LRSpectrumFull.Sext6.Gap.RobustCorA
import LRSpectrumFull.Sext6.Gap.OEPrimeDusart

/-!
# Sharpened Dusart discharge for `PrimeWin k N r`, general `k`  [2026-11-25]

Hypothesis predicate `DusartPi` (as in `OEPrimeDusart.lean`; imported statement, not an axiom).
With `L = ln(3N/2)` and `T = 3k(k+1)+1`: for `N ≥ 732` (so `L ≥ 7`) and `8 T L ≤ 3 N`,
`π(2N) - π(N + N/2) ≥ 3N/(8L) ≥ T`.  Compare `OEPrimeDusart`/`RobustCorD`: `3N/(10 L)` and `10 T L ≤ 3 N`,
which was then weakened to `67 T² ≤ N` through `ln y ≤ 2 √y`; here the logarithm is kept and bounded by the
tangent line `ln y ≤ ln y₀ - 1 + y/y₀`.

* `key_realT2`, `window_T_of_dusart2` : `DusartPi → 732 ≤ N → T·8·ln(3N/2) ≤ 3N → T ≤ #primes in [N+1+N/2, 2N]`.
* `log_le_tangent`, `exp_nat_ge`, `disch_tangent`, `disch_nat` : discharge of `T·8·ln(3N/2) ≤ 3N` from an
  integer `m` and a rational lower bound `E ≤ e^m`.
* `disch_closed`, `primeWin_of_dusart_closed` : closed form for every `k`:
  `16 T (ln(24 T) - 1) ≤ 5 N` and `N ≥ 732` suffice (`N ≥ 3.2 T (ln(24T) - 1)`, i.e. `~ 3.2 T ln T`).
* `winK2`, `winK3`, `prime_append`, `AscB_nodup` (linear-time sortedness => `Nodup`) : block lemmas used by the generated modules `RobustKBlk{K}p{J}`
  (`winK3`: `T` consecutive entries of one nodup prime table, bounds by kernel `decide`).
No `sorry`, no `axiom`.

Convention: `N` is a natural number (the size of the ambient interval `[1,N]`); `v : Fin (n+1) → ℤ` is an arbitrary finite family of speeds (repetitions allowed) and `n` is not linked to `N`; `k` counts the entries `> N`. Speeds are the moving runners; the runner at rest is not counted, so a vector of `N` speeds means `N + 1` runners and the Lonely Runner value is `1/(N+1)`.
Hypotheses: `DusartPi` (Dusart's explicit prime-counting bounds, an imported statement carried as a `Prop` hypothesis, never an axiom) is a hypothesis only of the declarations whose statements mention it; the unconditional, `_small`, `_upto` and table statements do not use it.
Axiom audit: covered by `Axioms10` (first); every later audit module imports this module (`#print axioms`; declarations not printed there are bricks of printed ones, so their axioms are bounded by the printed lines).
-/

namespace LRSpectrumFull
namespace Sext6
namespace Gap

theorem winK2 {T N : ℕ} (ps : List ℕ) (a b : ℕ) (hnd : ps.Nodup) (hlen : T ≤ ps.length)
    (hlo : ∀ p ∈ ps, a ≤ p) (hhi : ∀ p ∈ ps, p ≤ b) (hpr : ∀ p ∈ ps, p.Prime)
    (ha : N + 1 + N / 2 ≤ a) (hb : b ≤ 2 * N) :
    T ≤ ((Finset.Icc (N + 1 + N / 2) (2 * N)).filter Nat.Prime).card :=
  winK ps hnd hlen hpr (fun p hp => le_trans ha (hlo p hp)) (fun p hp => le_trans (hhi p hp) hb)

theorem prime_append {l1 l2 : List ℕ} (h1 : ∀ p ∈ l1, p.Prime) (h2 : ∀ p ∈ l2, p.Prime) :
    ∀ p ∈ l1 ++ l2, p.Prime := by
  intro p hp
  rcases List.mem_append.mp hp with h | h
  · exact h1 p h
  · exact h2 p h

/-- Linear-time strict ascent test (a quadratic `Nodup` check costs memory proportional to the square of the length). -/
def AscB : List ℕ → Bool
  | a :: b :: l => decide (a < b) && AscB (b :: l)
  | _ => true

theorem AscB_pairwise : ∀ (l : List ℕ), AscB l = true → l.Pairwise (· < ·)
  | [], _ => List.Pairwise.nil
  | [a], _ => List.pairwise_singleton _ _
  | a :: b :: l, h => by
      simp only [AscB, Bool.and_eq_true, decide_eq_true_eq] at h
      have ih := AscB_pairwise (b :: l) h.2
      refine List.Pairwise.cons ?_ ih
      intro x hx
      rcases List.mem_cons.mp hx with rfl | hx'
      · exact h.1
      · exact lt_trans h.1 ((List.pairwise_cons.mp ih).1 x hx')

theorem AscB_nodup {l : List ℕ} (h : AscB l = true) : l.Nodup :=
  (AscB_pairwise l h).imp (fun h => ne_of_lt h)

/-- Block lemma, shared-table form: `T` consecutive entries `PL[i], ..., PL[i+T-1]` of a nodup list of primes. -/
theorem winK3 {T N : ℕ} (PL : List ℕ) (i a b : ℕ) (hnd : PL.Nodup) (hpr : ∀ p ∈ PL, p.Prime)
    (hlen : T ≤ ((PL.drop i).take T).length) (hlo : ∀ p ∈ (PL.drop i).take T, a ≤ p)
    (hhi : ∀ p ∈ (PL.drop i).take T, p ≤ b) (ha : N + 1 + N / 2 ≤ a) (hb : b ≤ 2 * N) :
    T ≤ ((Finset.Icc (N + 1 + N / 2) (2 * N)).filter Nat.Prime).card :=
  winK2 ((PL.drop i).take T) a b
    (List.Nodup.sublist ((List.take_sublist T _).trans (List.drop_sublist i PL)) hnd) hlen hlo hhi
    (fun p hp => hpr p (List.mem_of_mem_drop (List.mem_of_mem_take hp))) ha hb

theorem key_realT2 {N L M T : ℝ} (hN : 732 ≤ N) (hL : 7 ≤ L) (hT : T * (8 * L) ≤ 3 * N)
    (hM1 : L ≤ M) (hM2 : M ≤ L + 1 / 3) :
    T ≤ 2 * N / M * (1 + 1 / M) - 3 * N / 2 / L * (1 + (6381 / 5000) / L) := by
  have hL0 : 0 < L := by linarith
  have hM0 : 0 < M := by linarith
  have hN0 : 0 < N := by linarith
  have hu : L + 1 / 3 ≠ 0 := by positivity
  have hv : 3 * L + 1 ≠ 0 := by positivity
  have e1 : 2 * N / M * (1 + 1 / M) = 2 * N * ((M + 1) / M ^ 2) := by
    field_simp
  have e2 : 3 * N / 2 / L * (1 + (6381 / 5000) / L)
      = 3 * N / 2 * ((L + 6381 / 5000) / L ^ 2) := by
    field_simp
  have h2 : (L + 4 / 3) / (L + 1 / 3) ^ 2 ≤ (M + 1) / M ^ 2 := by
    have h := g_mono hM0 hM2
    have e : L + 1 / 3 + 1 = L + 4 / 3 := by ring
    rwa [e] at h
  have hs : 0 ≤ L - 7 := by linarith
  have hpoly : 0 ≤ 11250 * L ^ 3 - 44787 * L ^ 2 - 133608 * L - 19143 := by
    have e : 11250 * L ^ 3 - 44787 * L ^ 2 - 133608 * L - 19143
        = 11250 * (L - 7) ^ 3 + 191463 * (L - 7) ^ 2 + 893124 * (L - 7) + 709788 := by ring
    rw [e]
    have h3 := pow_nonneg hs 3
    have h2' := pow_nonneg hs 2
    linarith
  have hE : 3 / (8 * L) ≤
      2 * ((L + 4 / 3) / (L + 1 / 3) ^ 2) - 3 / 2 * ((L + 6381 / 5000) / L ^ 2) := by
    rw [← sub_nonneg]
    have e : 2 * ((L + 4 / 3) / (L + 1 / 3) ^ 2) - 3 / 2 * ((L + 6381 / 5000) / L ^ 2)
        - 3 / (8 * L)
        = (11250 * L ^ 3 - 44787 * L ^ 2 - 133608 * L - 19143)
          / (10000 * L ^ 2 * (3 * L + 1) ^ 2) := by
      field_simp
      ring
    rw [e]
    exact div_nonneg hpoly (by positivity)
  have h7 : T ≤ 3 * N / (8 * L) := by
    rw [le_div_iff₀ (by positivity)]
    exact hT
  rw [e1, e2]
  have h5 : 2 * N * ((L + 4 / 3) / (L + 1 / 3) ^ 2) ≤ 2 * N * ((M + 1) / M ^ 2) :=
    mul_le_mul_of_nonneg_left h2 (by positivity)
  have h6 : N * (3 / (8 * L)) ≤
      N * (2 * ((L + 4 / 3) / (L + 1 / 3) ^ 2) - 3 / 2 * ((L + 6381 / 5000) / L ^ 2)) :=
    mul_le_mul_of_nonneg_left hE hN0.le
  have e3 : N * (3 / (8 * L)) = 3 * N / (8 * L) := by ring
  nlinarith [h5, h6, h7, e3]

theorem log_ge_7 {y : ℝ} (hy : 1097 ≤ y) : 7 ≤ Real.log y := by
  have hy0 : 0 < y := by linarith
  rw [Real.le_log_iff_exp_le hy0]
  have h1 : Real.exp 1 < 2.7182818286 := Real.exp_one_lt_d9
  have h2 : Real.exp 7 = Real.exp 1 ^ 7 := by
    have := Real.exp_nat_mul 1 7
    simpa using this
  rw [h2]
  have h3 : Real.exp 1 ^ 7 ≤ (2.7182818286 : ℝ) ^ 7 :=
    pow_le_pow_left₀ (Real.exp_pos 1).le h1.le 7
  have h4 : (2.7182818286 : ℝ) ^ 7 ≤ 1097 := by norm_num
  linarith

theorem window_T_of_dusart2 (hD : DusartPi) {T N : ℕ} (hN : 732 ≤ N)
    (hT : (T : ℝ) * (8 * Real.log (3 * (N : ℝ) / 2)) ≤ 3 * N) :
    T ≤ ((Finset.Icc (N + 1 + N / 2) (2 * N)).filter Nat.Prime).card := by
  obtain ⟨hlow, hup⟩ := hD
  have hNR : (732 : ℝ) ≤ N := by exact_mod_cast hN
  have hx1 : (599 : ℝ) ≤ 2 * N := by linarith
  have hlo := hlow (2 * N) hx1
  have hf1 : ⌊(2 * (N : ℝ))⌋₊ = 2 * N := by
    have : (2 * (N : ℝ)) = ((2 * N : ℕ) : ℝ) := by push_cast; ring
    rw [this, Nat.floor_natCast]
  rw [hf1] at hlo
  have hx2 : (1 : ℝ) < 3 * N / 2 := by linarith
  have hu := hup (3 * N / 2) hx2
  have hf2 : ⌊(3 * (N : ℝ) / 2)⌋₊ = N + N / 2 := by
    have : (3 * (N : ℝ) / 2) = ((3 * N : ℕ) : ℝ) / ((2 : ℕ) : ℝ) := by push_cast; ring
    rw [this, Nat.floor_div_eq_div]
    omega
  rw [hf2] at hu
  have hy : (1097 : ℝ) ≤ 3 * N / 2 := by linarith
  have hL7 : 7 ≤ Real.log (3 * (N : ℝ) / 2) := log_ge_7 hy
  have hc0 : 0 ≤ Real.log (4 / 3) := Real.log_nonneg (by norm_num)
  have hc1 : Real.log (4 / 3) ≤ 1 / 3 := by
    have := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 4 / 3)
    linarith
  have hM : Real.log (2 * (N : ℝ)) = Real.log (3 * (N : ℝ) / 2) + Real.log (4 / 3) := by
    rw [← Real.log_mul (by positivity) (by norm_num)]
    congr 1
    ring
  have hkey := key_realT2 (N := (N : ℝ)) (L := Real.log (3 * (N : ℝ) / 2))
    (M := Real.log (2 * (N : ℝ))) (T := (T : ℝ)) hNR hL7 hT (by linarith) (by linarith)
  have hcount := card_primes_Icc (m := N + N / 2) (n := 2 * N) (by omega)
  have e3 : N + N / 2 + 1 = N + 1 + N / 2 := by omega
  rw [e3] at hcount
  have hreal : ((Nat.primeCounting (N + N / 2) : ℕ) : ℝ) + (T : ℝ) ≤
      ((Nat.primeCounting (2 * N) : ℕ) : ℝ) := by linarith
  have hnat : Nat.primeCounting (N + N / 2) + T ≤ Nat.primeCounting (2 * N) := by
    exact_mod_cast hreal
  omega

/-- `PrimeWin k N r` for every `r` with `2 r ≤ N`, from `DusartPi`, once `N ≥ 732` and
`T · 8 ln(3N/2) ≤ 3N` with `T = 3k(k+1)+1`. -/
theorem primeWin_of_dusart2 (hD : DusartPi) {k N : ℕ} (hN : 732 ≤ N)
    (hT : ((3 * k * (k + 1) + 1 : ℕ) : ℝ) * (8 * Real.log (3 * (N : ℝ) / 2)) ≤ 3 * N) :
    ∀ r : ℕ, 2 * r ≤ N → PrimeWin k N r :=
  primeWin_of_window (by omega) (window_T_of_dusart2 hD hN hT)

/-- Tangent line bound `ln y ≤ ln y₀ - 1 + y / y₀`. -/
theorem log_le_tangent {y y0 : ℝ} (hy : 0 < y) (hy0 : 0 < y0) :
    Real.log y ≤ Real.log y0 - 1 + y / y0 := by
  have h := Real.log_le_sub_one_of_pos (div_pos hy hy0)
  rw [Real.log_div hy.ne' hy0.ne'] at h
  linarith

theorem exp_nat_ge (m : ℕ) : (2.7182818283 : ℝ) ^ m ≤ Real.exp m := by
  have h2 : Real.exp m = Real.exp 1 ^ m := by
    have := Real.exp_nat_mul 1 m
    simpa using this
  rw [h2]
  exact pow_le_pow_left₀ (by norm_num) Real.exp_one_gt_d9.le m

theorem disch_tangent {T N E : ℝ} {m : ℕ} (hE0 : 0 < E) (hE : E ≤ Real.exp m) (hT : 0 ≤ T)
    (hN : 0 < N) (h : 8 * T * ((m : ℝ) - 1) + 12 * T * N / E ≤ 3 * N) :
    T * (8 * Real.log (3 * N / 2)) ≤ 3 * N := by
  have hy : 0 < 3 * N / 2 := by positivity
  have h1 := log_le_tangent hy (Real.exp_pos m)
  rw [Real.log_exp] at h1
  have h2 : (3 * N / 2) / Real.exp m ≤ (3 * N / 2) / E := by gcongr
  have h3 : Real.log (3 * N / 2) ≤ (m : ℝ) - 1 + (3 * N / 2) / E := by linarith
  have h4 : T * (8 * Real.log (3 * N / 2)) ≤ T * (8 * ((m : ℝ) - 1 + (3 * N / 2) / E)) :=
    mul_le_mul_of_nonneg_left (by linarith) hT
  have h5 : T * (8 * ((m : ℝ) - 1 + (3 * N / 2) / E))
      = 8 * T * ((m : ℝ) - 1) + 12 * T * N / E := by ring
  linarith

/-- Natural-number form of the discharge: `m = m1 + 1`, `E ≤ 2.7182818283^m`, and
`8 T m1 E + 12 T N ≤ 3 N E` give `T · 8 ln(3N/2) ≤ 3N`. -/
theorem disch_nat {T m1 E N : ℕ} (hE0 : 0 < E) (hE : (E : ℝ) ≤ (2.7182818283 : ℝ) ^ (m1 + 1))
    (hN : 0 < N) (h : 8 * T * m1 * E + 12 * T * N ≤ 3 * N * E) :
    (T : ℝ) * (8 * Real.log (3 * (N : ℝ) / 2)) ≤ 3 * N := by
  have hE0R : (0 : ℝ) < E := by exact_mod_cast hE0
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN
  have hR : 8 * (T : ℝ) * m1 * E + 12 * T * N ≤ 3 * N * E := by exact_mod_cast h
  refine disch_tangent (m := m1 + 1) hE0R (le_trans hE (exp_nat_ge (m1 + 1))) (Nat.cast_nonneg T)
    hNR ?_
  have e : ((((m1 + 1 : ℕ)) : ℝ) - 1) = m1 := by push_cast; ring
  rw [e]
  have h12 : 12 * (T : ℝ) * N / E ≤ 3 * N - 8 * T * m1 := by
    rw [div_le_iff₀ hE0R]
    nlinarith [hR]
  linarith

/-- Closed form, every `k`: `16 T (ln(24 T) - 1) ≤ 5 N` implies `T · 8 ln(3N/2) ≤ 3 N`. -/
theorem disch_closed {T N : ℝ} (hT : 0 < T) (hN : 0 < N)
    (h : 16 * T * (Real.log (24 * T) - 1) ≤ 5 * N) :
    T * (8 * Real.log (3 * N / 2)) ≤ 3 * N := by
  have hy : 0 < 3 * N / 2 := by positivity
  have hT0 : T ≠ 0 := hT.ne'
  have h1 := log_le_tangent hy (by positivity : (0 : ℝ) < 24 * T)
  have h4 : T * (8 * Real.log (3 * N / 2))
      ≤ T * (8 * (Real.log (24 * T) - 1 + (3 * N / 2) / (24 * T))) :=
    mul_le_mul_of_nonneg_left (by linarith) hT.le
  have h5 : T * (8 * (Real.log (24 * T) - 1 + (3 * N / 2) / (24 * T)))
      = 8 * T * (Real.log (24 * T) - 1) + N / 2 := by
    first
      | (field_simp; ring)
      | field_simp
  linarith

/-- **General `k`** (closed-form threshold): `DusartPi`, `N ≥ 732` and `16 T (ln(24T) - 1) ≤ 5 N`,
`T = 3k(k+1)+1`, give `PrimeWin k N r` for every `r` with `2 r ≤ N`. -/
theorem primeWin_of_dusart_closed (hD : DusartPi) {k N : ℕ} (hN : 732 ≤ N)
    (h : 16 * ((3 * k * (k + 1) + 1 : ℕ) : ℝ) *
      (Real.log (24 * ((3 * k * (k + 1) + 1 : ℕ) : ℝ)) - 1) ≤ 5 * N) :
    ∀ r : ℕ, 2 * r ≤ N → PrimeWin k N r := by
  have hT : (0 : ℝ) < ((3 * k * (k + 1) + 1 : ℕ) : ℝ) := by positivity
  have hN0 : (0 : ℝ) < N := by
    have : (732 : ℝ) ≤ N := by exact_mod_cast hN
    linarith
  exact primeWin_of_dusart2 hD hN (disch_closed hT hN0 h)

end Gap
end Sext6
end LRSpectrumFull
