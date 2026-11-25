import LRSpectrumFull.Sext6.Gap.OELowCore
import LRSpectrumFull.Sext6.Gap.RobustSpoil
import LRSpectrumFull.Sext6.Gap.RobustMeasure

/-!
# Theorem S (k-robustness of the one-entry theorem): assembly  [2026-11-25]

Source: the accompanying notes on Theorem S section 3.

For `k ≥ 1`, `1 ≤ r`, `r + 2 ≤ N`, at least `3k(k+1)+1` primes in `[N+1+r, 2N-1]` (`PrimeWin k N r`, a
hypothesis predicate, never an axiom), and any finite family of speeds each of which is either in
`[1,N] \ {r}` or is one of at most `k` "large" entries `> N`: `1/N ≤ ML`.

* `far_window`     : Lemma Lip (window persistence, radius `1/(D N L)`).
* `real_sum_lt`    : the real inequality `Σ_u (2 l/N + 4/(N u)) < l` for the large speeds.
* `robust_core`    : existence of one time `t` good for all speeds (Finset form).
* `ML_ge_robust`   : the statement for an arbitrary speed vector `v : Fin (n+1) → ℤ`.
No `sorry`, no `axiom`.

Convention: `N` is a natural number (the size of the ambient interval `[1,N]`); `v : Fin (n+1) → ℤ` is an arbitrary finite family of speeds (repetitions allowed) and `n` is not linked to `N`; `k` counts the entries `> N`. Speeds are the moving runners; the runner at rest is not counted, so a vector of `N` speeds means `N + 1` runners and the Lonely Runner value is `1/(N+1)`.
Hypotheses: those of the individual statements (numerical bounds, structural conditions and, where named in the list above, window predicates such as `PrimeWin`, `CopWin`, `PrimeWindow7`, which later modules discharge for explicit ranges). The unproved predicates `DusartPi`, `LRCHyp`, `CopWinHyp` are not hypotheses of any statement in this module.
Axiom audit: covered by `Axioms7` (first); every later audit module imports this module (`#print axioms`; declarations not printed there are bricks of printed ones, so their axioms are bounded by the printed lines).
-/

namespace LRSpectrumFull
namespace Sext6
namespace Gap

/-- Hypothesis predicate: at least `3k(k+1)+1` primes in `[N+1+r, 2N-1]`. -/
def PrimeWin (k N r : ℕ) : Prop :=
  3 * k * (k + 1) + 1 ≤ ((Finset.Icc (N + 1 + r) (2 * N - 1)).filter Nat.Prime).card

/-- **Lemma Lip.**  `a r + b D = 1`, `D + 1 ≤ 2N`, a speed `x ≤ L` avoiding the classes `0, r, -r` mod `D`:
for `|t - a/D| ≤ 1/(D N L)` we have `1/N ≤ ‖x t‖`. -/
theorem far_window {D N L : ℕ} (hD : 0 < D) (hD1 : D + 1 ≤ 2 * N) (hN : 0 < N) (hL : 0 < L)
    (r a b : ℤ) (hab : a * r + b * (D : ℤ) = 1) {x : ℕ} (hxL : x ≤ L)
    (h0 : ¬ ((D : ℤ) ∣ (x : ℤ))) (h1 : ¬ ((D : ℤ) ∣ (x : ℤ) - r)) (h2 : ¬ ((D : ℤ) ∣ (x : ℤ) + r))
    {t : ℝ} (ht : |t - (a : ℝ) / D| ≤ 1 / ((D : ℝ) * N * L)) :
    1 / (N : ℝ) ≤ nearestIntDist ((x : ℝ) * t) := by
  have hfar := far_of_cond hD r a b (x : ℤ) hab h0 h1 h2
  have hcc : (((x : ℕ) : ℤ) : ℝ) = (x : ℝ) := by norm_cast
  rw [hcc] at hfar
  have hDR : (0 : ℝ) < D := by exact_mod_cast hD
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN
  have hLR : (0 : ℝ) < L := by exact_mod_cast hL
  have hDne : (D : ℝ) ≠ 0 := hDR.ne'
  have hNne : (N : ℝ) ≠ 0 := hNR.ne'
  have hLne : (L : ℝ) ≠ 0 := hLR.ne'
  have hD1R : (D : ℝ) + 1 ≤ 2 * N := by exact_mod_cast hD1
  have hlip := nearestIntDist_lipschitz ((x : ℝ) * ((a : ℝ) / D)) ((x : ℝ) * t)
  have hx0 : (0 : ℝ) ≤ x := Nat.cast_nonneg _
  have hxL' : (x : ℝ) ≤ L := by exact_mod_cast hxL
  have hQ : (0 : ℝ) ≤ 1 / ((D : ℝ) * N * L) := by positivity
  have habs : |(x : ℝ) * ((a : ℝ) / D) - (x : ℝ) * t| ≤ 1 / ((D : ℝ) * N) := by
    have e1 : (x : ℝ) * ((a : ℝ) / D) - (x : ℝ) * t = (x : ℝ) * ((a : ℝ) / D - t) := by ring
    rw [e1, abs_mul, abs_of_nonneg hx0, abs_sub_comm]
    calc (x : ℝ) * |t - (a : ℝ) / D| ≤ (x : ℝ) * (1 / ((D : ℝ) * N * L)) := by gcongr
      _ ≤ (L : ℝ) * (1 / ((D : ℝ) * N * L)) := by gcongr
      _ = 1 / ((D : ℝ) * N) := by
          first
            | (field_simp; done)
            | (field_simp; ring)
  have hkey : 1 / (N : ℝ) ≤ (2 : ℝ) / D - 1 / ((D : ℝ) * N) := by
    have e : (2 : ℝ) / D - 1 / ((D : ℝ) * N) - 1 / N = (2 * N - 1 - D) / ((D : ℝ) * N) := by
      first
        | (field_simp; done)
        | (field_simp; ring)
    have : 0 ≤ (2 * (N : ℝ) - 1 - D) / ((D : ℝ) * N) := by
      apply div_nonneg
      · linarith
      · positivity
    linarith
  have hl := (abs_sub_le_iff.mp hlip).1
  linarith

/-- The real inequality for the large speeds. `l = 2 δ`, `δ = 1/(D N L)`, large speeds `> 8 k N L`. -/
theorem real_sum_lt {k N L D : ℕ} (hk : 1 ≤ k) (hN8 : 8 * k ≤ N) (hL : 0 < L) (hN : 0 < N)
    (hD0 : 0 < D) (hD : D + 1 ≤ 2 * N) {δ l : ℝ} (hδ : δ = 1 / ((D : ℝ) * N * L)) (hl : l = 2 * δ)
    (U : Finset ℕ) (hUk : U.card ≤ k) (hUlarge : ∀ u ∈ U, 8 * k * N * L < u) :
    ∑ u ∈ U, (2 * l / (N : ℝ) + 4 / ((N : ℝ) * (u : ℝ))) < l := by
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN
  have hLR : (0 : ℝ) < L := by exact_mod_cast hL
  have hDR : (0 : ℝ) < D := by exact_mod_cast hD0
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk
  have hNne : (N : ℝ) ≠ 0 := hNR.ne'
  have hLne : (L : ℝ) ≠ 0 := hLR.ne'
  have hkne : (k : ℝ) ≠ 0 := hkR.ne'
  have h8 : (8 : ℝ) * k ≤ N := by exact_mod_cast hN8
  have hDlt : (D : ℝ) < 2 * N := by
    have : (D : ℝ) + 1 ≤ 2 * N := by exact_mod_cast hD
    linarith
  have hδpos : 0 < δ := by rw [hδ]; exact one_div_pos.mpr (mul_pos (mul_pos hDR hNR) hLR)
  have hlpos : 0 < l := by rw [hl]; linarith
  have hterm : ∀ u ∈ U, 2 * l / (N : ℝ) + 4 / ((N : ℝ) * (u : ℝ)) ≤
      2 * l / (N : ℝ) + 4 / ((N : ℝ) * (8 * k * N * L)) := by
    intro u hu
    have hu' : ((8 * k * N * L : ℕ) : ℝ) < u := by exact_mod_cast hUlarge u hu
    push_cast at hu'
    have hu'' := hu'.le
    have hpos : (0 : ℝ) < (N : ℝ) * (8 * k * N * L) :=
      mul_pos hNR (mul_pos (mul_pos (mul_pos (by norm_num) hkR) hNR) hLR)
    have : (4 : ℝ) / ((N : ℝ) * (u : ℝ)) ≤ 4 / ((N : ℝ) * (8 * k * N * L)) := by
      apply div_le_div_of_nonneg_left (by norm_num) hpos
      exact mul_le_mul_of_nonneg_left hu'' hNR.le
    linarith
  set T0 : ℝ := 2 * l / (N : ℝ) + 4 / ((N : ℝ) * (8 * k * N * L)) with hT0
  have hpos0 : (0 : ℝ) < (N : ℝ) * (8 * k * N * L) :=
    mul_pos hNR (mul_pos (mul_pos (mul_pos (by norm_num) hkR) hNR) hLR)
  have hT0nn : 0 ≤ T0 := by
    rw [hT0]
    exact add_nonneg (div_nonneg (by linarith) hNR.le) (div_nonneg (by norm_num) hpos0.le)
  have hsum1 : ∑ u ∈ U, (2 * l / (N : ℝ) + 4 / ((N : ℝ) * (u : ℝ))) ≤ ∑ u ∈ U, T0 :=
    Finset.sum_le_sum hterm
  have hsum2 : ∑ u ∈ U, T0 = (U.card : ℝ) * T0 := by simp
  have hcardR : (U.card : ℝ) ≤ k := by exact_mod_cast hUk
  have hsum3 : (U.card : ℝ) * T0 ≤ (k : ℝ) * T0 := mul_le_mul_of_nonneg_right hcardR hT0nn
  have hA : (k : ℝ) * (2 * l / N) ≤ l / 4 := by
    have e : (k : ℝ) * (2 * l / N) = (2 * k * l) / N := by ring
    rw [e, div_le_iff₀ hNR]
    nlinarith [mul_nonneg hlpos.le (sub_nonneg.mpr h8)]
  have hB : (k : ℝ) * (4 / ((N : ℝ) * (8 * k * N * L))) = 1 / (2 * N * N * L) := by
    first
      | (field_simp; done)
      | (field_simp; ring)
  have hC : 1 / (2 * (N : ℝ) * N * L) < l / 2 := by
    have e : l / 2 = 1 / ((D : ℝ) * N * L) := by rw [hl, hδ]; ring
    rw [e]
    apply one_div_lt_one_div_of_lt (mul_pos (mul_pos hDR hNR) hLR)
    have h1 : (D : ℝ) * N * L < 2 * N * N * L := by
      have := mul_pos (mul_pos (sub_pos.mpr hDlt) hNR) hLR
      nlinarith
    linarith
  have hfin : (k : ℝ) * T0 < l := by
    have e : (k : ℝ) * T0 = (k : ℝ) * (2 * l / N) + (k : ℝ) * (4 / ((N : ℝ) * (8 * k * N * L))) := by
      rw [hT0]; ring
    rw [e, hB]
    linarith
  linarith

/-- **Theorem S, Finset form.**  One time `t` serves every retained speed and every added speed. -/
theorem robust_core {k N r : ℕ} (hk : 1 ≤ k) (hr1 : 1 ≤ r) (hr2 : r + 2 ≤ N) (hP : PrimeWin k N r)
    (W : Finset ℕ) (hWN : ∀ w ∈ W, N < w) (hWk : W.card ≤ k) :
    ∃ t : ℝ, (∀ x : ℕ, 1 ≤ x → x ≤ N → x ≠ r → 1 / (N : ℝ) ≤ nearestIntDist ((x : ℝ) * t)) ∧
      ∀ w ∈ W, 1 / (N : ℝ) ≤ nearestIntDist ((w : ℝ) * t) := by
  classical
  obtain ⟨P, hPdef⟩ : ∃ P : Finset ℕ, P = (Finset.Icc (N + 1 + r) (2 * N - 1)).filter Nat.Prime :=
    ⟨_, rfl⟩
  have hPprop : ∀ p ∈ P, p.Prime ∧ N + 2 ≤ p ∧ N + 1 + r ≤ p ∧ p + 1 ≤ 2 * N := by
    intro p hp
    rw [hPdef] at hp
    have h := Finset.mem_filter.mp hp
    have h2 := Finset.mem_Icc.mp h.1
    exact ⟨h.2, by omega, by omega, by omega⟩
  have hPcard : 3 * k * (k + 1) + 1 ≤ P.card := by rw [hPdef]; exact hP
  have hPle : P.card ≤ 2 * N - 1 + 1 - (N + 1 + r) := by
    rw [hPdef]
    exact (Finset.card_filter_le _ _).trans (Nat.card_Icc _ _).le
  have hX : 3 * k * (k + 1) + 2 + r ≤ N := by omega
  have h8 : 8 * k ≤ 3 * k * (k + 1) + 3 := by
    have h : (8 * (k : ℤ)) ≤ 3 * (k : ℤ) * ((k : ℤ) + 1) + 3 := by
      nlinarith [sq_nonneg ((k : ℤ) - 1), (Nat.cast_nonneg k : (0 : ℤ) ≤ k)]
    exact_mod_cast h
  have hN8 : 8 * k ≤ N := by omega
  have hN3 : 3 ≤ N := by omega
  obtain ⟨S, hSW, L, hNL, hSL, hLc, hlarge, hsp⟩ :=
    chain (N := N) (r := r) (c := 8 * k * N) (P := P) (fun p hp => ⟨(hPprop p hp).1, (hPprop p hp).2.1⟩)
      (by omega) (by omega) (Nat.mul_le_mul_right N hN8) W.card W N 0 le_rfl le_rfl (by simp)
      (fun x hx => hWN x hx)
  have hSK : S.card ≤ k := (Finset.card_le_card hSW).trans hWk
  have hspoil : (spoilSet P r S).card ≤ 3 * k * (k + 1) := by
    have h1 := sum_six S.card
    have h2 : 3 * S.card * (S.card + 1) ≤ 3 * k * (k + 1) :=
      Nat.mul_le_mul (Nat.mul_le_mul_left 3 hSK) (by omega)
    omega
  obtain ⟨D, hDP, hDnot⟩ := Finset.exists_mem_notMem_of_card_lt_card
    (s := spoilSet P r S) (t := P) (by omega)
  obtain ⟨hDprime, hDge2, hDge, hDle⟩ := hPprop D hDP
  have hclean : ∀ w ∈ S, ¬ BadAt r D w := by
    intro w hw hbad
    apply hDnot
    rw [mem_spoilSet]
    exact ⟨hDP, w, hw, hbad⟩
  have hcop : Nat.Coprime D r := by
    rw [Nat.Prime.coprime_iff_not_dvd hDprime]
    intro hd
    have := Nat.le_of_dvd (by omega) hd
    omega
  obtain ⟨a, b, hab⟩ : IsCoprime (r : ℤ) (D : ℤ) := Nat.isCoprime_iff_coprime.mpr hcop.symm
  have hDpos : 0 < D := by omega
  have hN0 : 0 < N := by omega
  have hL0 : 0 < L := by omega
  have hDR : (0 : ℝ) < D := by exact_mod_cast hDpos
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN0
  have hLR : (0 : ℝ) < L := by exact_mod_cast hL0
  obtain ⟨δ, hδ⟩ : ∃ δ : ℝ, δ = 1 / ((D : ℝ) * N * L) := ⟨_, rfl⟩
  have hδpos : 0 < δ := by rw [hδ]; exact one_div_pos.mpr (mul_pos (mul_pos hDR hNR) hLR)
  obtain ⟨t0, ht0⟩ : ∃ t0 : ℝ, t0 = (a : ℝ) / D := ⟨_, rfl⟩
  obtain ⟨l, hl⟩ : ∃ l : ℝ, l = (t0 + δ) - (t0 - δ) := ⟨_, rfl⟩
  have hl2 : l = 2 * δ := by rw [hl]; ring
  have hUk : (W \ S).card ≤ k := (Finset.card_le_card Finset.sdiff_subset).trans hWk
  have hU1 : ∀ u ∈ W \ S, 1 ≤ u := by
    intro u hu
    have := hWN u (Finset.mem_sdiff.mp hu).1
    omega
  have hUl : ∀ u ∈ W \ S, 8 * k * N * L < u := by
    intro u hu
    have h := Finset.mem_sdiff.mp hu
    exact hlarge u h.1 h.2
  have hsum : ∑ u ∈ W \ S, (2 * (t0 + δ - (t0 - δ)) / (N : ℝ) + 4 / ((N : ℝ) * (u : ℝ))) <
      (t0 + δ) - (t0 - δ) := by
    have := real_sum_lt hk hN8 hL0 hN0 hDpos hDle hδ hl2 (W \ S) hUk hUl
    rw [hl] at this
    exact this
  obtain ⟨t, ht, hgood⟩ := exists_good_point (t0 - δ) (t0 + δ) (by linarith) N (by omega) (W \ S) hU1 hsum
  have ht' : |t - (a : ℝ) / D| ≤ 1 / ((D : ℝ) * N * L) := by
    rw [← hδ, ← ht0]
    exact abs_le.mpr ⟨by linarith [ht.1], by linarith [ht.2]⟩
  refine ⟨t, ?_, ?_⟩
  · intro x hx1 hxN hxr
    obtain ⟨c0, c1, c2⟩ := retained_cond (N := N) (r := r) hDge hx1 hxN hxr
    exact far_window hDpos hDle hN0 hL0 (r : ℤ) a b hab (by omega) c0 c1 c2 ht'
  · intro w hw
    by_cases hwS : w ∈ S
    · have hcl := hclean w hwS
      unfold BadAt at hcl
      push Not at hcl
      exact far_window hDpos hDle hN0 hL0 (r : ℤ) a b hab (hSL w hwS) hcl.1 hcl.2.1 hcl.2.2 ht'
    · exact hgood w (Finset.mem_sdiff.mpr ⟨hw, hwS⟩)

/-- **Theorem S (speed-vector form).**  `v : Fin (n+1) → ℤ` with every entry either in `[1,N] \ {r}` or
`> N`, at most `k` entries `> N`; `PrimeWin k N r`.  Then `1/N ≤ ML v`. -/
theorem ML_ge_robust {n k N r : ℕ} (hk : 1 ≤ k) (hr1 : 1 ≤ r) (hr2 : r + 2 ≤ N)
    (hP : PrimeWin k N r) (v : Fin (n + 1) → ℤ)
    (hv : ∀ i, (1 ≤ v i ∧ v i ≤ (N : ℤ) ∧ v i ≠ (r : ℤ)) ∨ (N : ℤ) < v i)
    (hcard : (Finset.univ.filter (fun i : Fin (n + 1) => (N : ℤ) < v i)).card ≤ k) :
    1 / (N : ℝ) ≤ ML v := by
  classical
  obtain ⟨t, ht1, ht2⟩ := robust_core hk hr1 hr2 hP
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

end Gap
end Sext6
end LRSpectrumFull
