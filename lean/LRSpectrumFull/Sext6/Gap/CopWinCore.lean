import LRSpectrumFull.Sext6.Gap.RobustCorA
import LRSpectrumFull.Sext6.Gap.CopWinSpoil

/-!
# CopWin, step 2: Theorem S with a coprime window in place of a prime window  [2026-11-25]

Route G of the accompanying notes on the coprime-window route.  New file; nothing built is edited.

* `CopWinT T N r` : `T` pairwise coprime numbers in `[N+1+r, 2N-1]`, each coprime to `r` (hypothesis predicate).
* `CopWin k N r := CopWinT (3k(k+1)+1) N r`.
* `copWin_of_primeWin`  : `1 ≤ r`, `PrimeWin k N r` gives `CopWin k N r` (distinct primes are coprime).
* `robust_core_cop`, `ML_ge_robust_cop` : same statements as `robust_core`, `ML_ge_robust`, hypothesis `CopWin`.
* `ML_ge_robust_of_prime` : consistency, the old theorem re-derived from the coprime one.
* `cor_a_cop`           : Corollary S'(a) from `CopWin`.
Primality is used nowhere in the Theorem S core here.  No `sorry`, no `axiom`.

Convention: `N` is a natural number (the size of the ambient interval `[1,N]`); `v : Fin (n+1) → ℤ` is an arbitrary finite family of speeds (repetitions allowed) and `n` is not linked to `N`; `k` counts the entries `> N`. Speeds are the moving runners; the runner at rest is not counted, so a vector of `N` speeds means `N + 1` runners and the Lonely Runner value is `1/(N+1)`.
Hypotheses: those of the individual statements (numerical bounds, structural conditions and, where named in the list above, window predicates such as `PrimeWin`, `CopWin`, `PrimeWindow7`, which later modules discharge for explicit ranges). The unproved predicates `DusartPi`, `LRCHyp`, `CopWinHyp` are not hypotheses of any statement in this module.
Axiom audit: covered by `CopWinAxioms11` (first); every later audit module imports this module (`#print axioms`; declarations not printed there are bricks of printed ones, so their axioms are bounded by the printed lines).
-/

namespace LRSpectrumFull
namespace Sext6
namespace Gap

/-- `T` pairwise coprime moduli in the window `[N+1+r, 2N-1]` (written `D + 1 ≤ 2N`), each coprime to `r`. -/
def CopWinT (T N r : ℕ) : Prop :=
  ∃ P : Finset ℕ, T ≤ P.card ∧
    (∀ D ∈ P, N + 1 + r ≤ D ∧ D + 1 ≤ 2 * N ∧ Nat.Coprime D r) ∧
    (P : Set ℕ).Pairwise Nat.Coprime

/-- The window predicate of Theorem S. -/
def CopWin (k N r : ℕ) : Prop := CopWinT (3 * k * (k + 1) + 1) N r

/-- A positive-size coprime window forces room: `r + 2 ≤ N`. -/
theorem copWinT_le {T N r : ℕ} (hT : 1 ≤ T) (h : CopWinT T N r) : r + 2 ≤ N := by
  obtain ⟨P, hcard, hprop, _⟩ := h
  have hpos : 0 < P.card := by omega
  obtain ⟨x, hx⟩ := Finset.card_pos.mp hpos
  have := hprop x hx
  omega

theorem copWin_le {k N r : ℕ} (h : CopWin k N r) : r + 2 ≤ N :=
  copWinT_le (by omega) h

/-- Monotonicity in `T`. -/
theorem copWinT_mono {T T' N r : ℕ} (hT : T' ≤ T) (h : CopWinT T N r) : CopWinT T' N r := by
  obtain ⟨P, hcard, hprop, hcop⟩ := h
  exact ⟨P, le_trans hT hcard, hprop, hcop⟩

/-- Primes in the window give a coprime window (`1 ≤ r` is needed: nothing but `1` is coprime to `0`). -/
theorem copWin_of_primeWin {k N r : ℕ} (hr : 1 ≤ r) (h : PrimeWin k N r) : CopWin k N r := by
  refine ⟨(Finset.Icc (N + 1 + r) (2 * N - 1)).filter Nat.Prime, h, ?_, ?_⟩
  · intro D hD
    obtain ⟨h1, h2⟩ := Finset.mem_filter.mp hD
    obtain ⟨hlo, hhi⟩ := Finset.mem_Icc.mp h1
    refine ⟨hlo, by omega, ?_⟩
    rw [Nat.Prime.coprime_iff_not_dvd h2]
    intro hd
    have := Nat.le_of_dvd (by omega) hd
    omega
  · intro p hp q hq hne
    exact (Nat.coprime_primes (Finset.mem_filter.mp (Finset.mem_coe.mp hp)).2
      (Finset.mem_filter.mp (Finset.mem_coe.mp hq)).2).mpr hne

/-- **Theorem S, Finset form, coprime window.**  One time `t` serves every retained speed and every
added speed. -/
theorem robust_core_cop {k N r : ℕ} (hk : 1 ≤ k) (hr1 : 1 ≤ r) (hr2 : r + 2 ≤ N) (hP : CopWin k N r)
    (W : Finset ℕ) (hWN : ∀ w ∈ W, N < w) (hWk : W.card ≤ k) :
    ∃ t : ℝ, (∀ x : ℕ, 1 ≤ x → x ≤ N → x ≠ r → 1 / (N : ℝ) ≤ nearestIntDist ((x : ℝ) * t)) ∧
      ∀ w ∈ W, 1 / (N : ℝ) ≤ nearestIntDist ((w : ℝ) * t) := by
  classical
  obtain ⟨P, hPcard, hPprop0, hPcop⟩ := hP
  have hPprop : ∀ p ∈ P, N + 2 ≤ p ∧ N + 1 + r ≤ p ∧ p + 1 ≤ 2 * N ∧ Nat.Coprime p r := by
    intro p hp
    have h := hPprop0 p hp
    have h1 := h.1
    exact ⟨by omega, h.1, h.2.1, h.2.2⟩
  have hPle : P.card ≤ 2 * N - 1 + 1 - (N + 1 + r) := by
    have hsub : P ⊆ Finset.Icc (N + 1 + r) (2 * N - 1) := by
      intro p hp
      have h := hPprop p hp
      exact Finset.mem_Icc.mpr ⟨h.2.1, by omega⟩
    exact (Finset.card_le_card hsub).trans (Nat.card_Icc _ _).le
  have hX : 3 * k * (k + 1) + 2 + r ≤ N := by omega
  have h8 : 8 * k ≤ 3 * k * (k + 1) + 3 := by
    have h : (8 * (k : ℤ)) ≤ 3 * (k : ℤ) * ((k : ℤ) + 1) + 3 := by
      nlinarith [sq_nonneg ((k : ℤ) - 1), (Nat.cast_nonneg k : (0 : ℤ) ≤ k)]
    exact_mod_cast h
  have hN8 : 8 * k ≤ N := by omega
  have hN3 : 3 ≤ N := by omega
  obtain ⟨S, hSW, L, hNL, hSL, hLc, hlarge, hsp⟩ :=
    chain_cop (N := N) (r := r) (c := 8 * k * N) (P := P) hPcop (fun p hp => (hPprop p hp).1)
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
  obtain ⟨hDge2, hDge, hDle, hcop⟩ := hPprop D hDP
  have hclean : ∀ w ∈ S, ¬ BadAt r D w := by
    intro w hw hbad
    apply hDnot
    rw [mem_spoilSet]
    exact ⟨hDP, w, hw, hbad⟩
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

/-- **Theorem S (speed-vector form), coprime window.**  Same statement as `ML_ge_robust`,
with `CopWin k N r` in place of `PrimeWin k N r`. -/
theorem ML_ge_robust_cop {n k N r : ℕ} (hk : 1 ≤ k) (hr1 : 1 ≤ r) (hr2 : r + 2 ≤ N)
    (hP : CopWin k N r) (v : Fin (n + 1) → ℤ)
    (hv : ∀ i, (1 ≤ v i ∧ v i ≤ (N : ℤ) ∧ v i ≠ (r : ℤ)) ∨ (N : ℤ) < v i)
    (hcard : (Finset.univ.filter (fun i : Fin (n + 1) => (N : ℤ) < v i)).card ≤ k) :
    1 / (N : ℝ) ≤ ML v := by
  classical
  obtain ⟨t, ht1, ht2⟩ := robust_core_cop hk hr1 hr2 hP
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

/-- Consistency: the prime-window theorem `ML_ge_robust` re-derived from the coprime-window one. -/
theorem ML_ge_robust_of_prime {n k N r : ℕ} (hk : 1 ≤ k) (hr1 : 1 ≤ r) (hr2 : r + 2 ≤ N)
    (hP : PrimeWin k N r) (v : Fin (n + 1) → ℤ)
    (hv : ∀ i, (1 ≤ v i ∧ v i ≤ (N : ℤ) ∧ v i ≠ (r : ℤ)) ∨ (N : ℤ) < v i)
    (hcard : (Finset.univ.filter (fun i : Fin (n + 1) => (N : ℤ) < v i)).card ≤ k) :
    1 / (N : ℝ) ≤ ML v :=
  ML_ge_robust_cop hk hr1 hr2 (copWin_of_primeWin hr1 hP) v hv hcard

/-- **Corollary S'(a), coprime window.**  `CopWin k N r` for every `1 ≤ r`, `2 r ≤ N`; at most `k`
entries `> N`; `ML v < 1/N`: every integer of `[1, N/2]` is an entry of `v`. -/
theorem cor_a_cop {n k N : ℕ} (hk : 1 ≤ k)
    (hP : ∀ r : ℕ, 1 ≤ r → 2 * r ≤ N → CopWin k N r)
    (v : Fin (n + 1) → ℤ) (hpos : ∀ i, 1 ≤ v i)
    (hcard : (Finset.univ.filter (fun i : Fin (n + 1) => (N : ℤ) < v i)).card ≤ k)
    (hML : ML v < 1 / (N : ℝ)) :
    ∀ r : ℕ, 1 ≤ r → 2 * r ≤ N → ∃ i, v i = (r : ℤ) := by
  intro r hr1 hr2
  by_contra hne
  push Not at hne
  have hPr := hP r hr1 hr2
  have hrN := copWin_le hPr
  have := ML_ge_robust_cop (n := n) (k := k) (N := N) (r := r) hk hr1 hrN hPr v
    (by
      intro i
      by_cases hbig : (N : ℤ) < v i
      · exact Or.inr hbig
      · exact Or.inl ⟨hpos i, not_lt.mp hbig, hne i⟩) hcard
  exact absurd hML (not_lt.mpr this)

end Gap
end Sext6
end LRSpectrumFull
