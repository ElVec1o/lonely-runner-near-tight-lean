import LRSpectrumFull.Sext6.Gap.Cheb30Upper

/-!
# Chebyshev's 30-combination: prime powers in the window (3N/2, 2N]  [2026-11-25]

`CopWinC T N r` : there is a finite set `S` of at least `T` pairwise coprime naturals, each in
`[N+1+r, 2N-1]`, each coprime to `r`.

Main theorem `copWinC_of_cheb`: if `6 l (T + 3 l + 60) + 1200 ≤ N` with `l = Nat.log 2 N + 2`, then
`CopWinC T N r` for every `1 ≤ r` with `2 r ≤ N`.  Proof: Chebyshev's two-sided bound on `ψ`
(`Cheb30Stirling`, `Cheb30Upper`) puts at least `T + log₂ N + 1` prime powers in `(N + N/2, 2N]`;
prime powers in that window are pairwise coprime (a second power of the same prime would exceed `2N`);
at most `log₂ r` of them share a prime with `r` (their primes are distinct divisors of `r`).
No `sorry`, no `axiom`.

Convention: No speed vector is involved in this module (number theory or real analysis); `N` denotes a natural number, the size of the ambient interval `[1,N]`.
Hypotheses: those of the individual statements (numerical bounds, structural conditions and, where named in the list above, window predicates such as `PrimeWin`, `CopWin`, `PrimeWindow7`, which later modules discharge for explicit ranges). The unproved predicates `DusartPi`, `LRCHyp`, `CopWinHyp` are not hypotheses of any statement in this module.
Axiom audit: covered by `Cheb30Axioms` (first); every later audit module imports this module (`#print axioms`; declarations not printed there are bricks of printed ones, so their axioms are bounded by the printed lines).
-/

open scoped ArithmeticFunction.vonMangoldt
open scoped Nat
open scoped Classical
open Finset

namespace LRSpectrumFull
namespace Sext6
namespace Gap
namespace Cheb30

/-- `T` pairwise coprime moduli in `[N+1+r, 2N-1]`, each coprime to `r`. -/
def CopWinC (T N r : ℕ) : Prop :=
  ∃ S : Finset ℕ, T ≤ S.card ∧
    (∀ D ∈ S, N + 1 + r ≤ D ∧ D ≤ 2 * N - 1 ∧ Nat.Coprime D r) ∧
    (S : Set ℕ).Pairwise Nat.Coprime

/-! ### Elementary part -/

theorem same_prime_false {p i j N : ℕ} (hp : p.Prime) (hij : i < j) (h1 : N + N / 2 < p ^ i)
    (h2 : p ^ j ≤ 2 * N) : False := by
  have h3 : p ^ (i + 1) ≤ p ^ j := Nat.pow_le_pow_right hp.pos hij
  have h4 : p ^ i * 2 ≤ p ^ i * p := Nat.mul_le_mul_left _ hp.two_le
  rw [pow_succ] at h3
  omega

theorem primePow_pairwise (N : ℕ) :
    (((Ioc (N + N / 2) (2 * N)).filter IsPrimePow : Finset ℕ) : Set ℕ).Pairwise Nat.Coprime := by
  intro a ha b hb hne
  simp only [Finset.coe_filter, Finset.mem_Ioc, Set.mem_setOf_eq] at ha hb
  obtain ⟨⟨ha1, ha2⟩, p, i, hp, hi, rfl⟩ := ha
  obtain ⟨⟨hb1, hb2⟩, q, j, hq, hj, rfl⟩ := hb
  have hp' : p.Prime := Nat.prime_iff.mpr hp
  have hq' : q.Prime := Nat.prime_iff.mpr hq
  by_cases hpq : p = q
  · subst hpq
    have hij : i ≠ j := fun h => hne (by rw [h])
    rcases lt_or_gt_of_ne hij with h | h
    · exact (same_prime_false hp' h ha1 hb2).elim
    · exact (same_prime_false hp' h hb1 ha2).elim
  · exact Nat.Coprime.pow _ _ ((Nat.coprime_primes hp' hq').mpr hpq)

/-- At most `log₂ r` members of a pairwise coprime set share a factor with `r`. -/
theorem bad_card_le (P : Finset ℕ) (hP : (P : Set ℕ).Pairwise Nat.Coprime)
    {r : ℕ} (hr : 1 ≤ r) :
    (P.filter (fun p => ¬ Nat.Coprime p r)).card ≤ Nat.log 2 r := by
  set B := P.filter (fun p => ¬ Nat.Coprime p r) with hB
  let f : ℕ → ℕ := fun p => Nat.minFac (Nat.gcd p r)
  have hfp : ∀ p ∈ B, (f p).Prime ∧ f p ∣ p ∧ f p ∣ r := by
    intro p hp
    rw [hB, Finset.mem_filter] at hp
    have hg : Nat.gcd p r ≠ 1 := fun h => hp.2 h
    exact ⟨Nat.minFac_prime hg, (Nat.minFac_dvd _).trans (Nat.gcd_dvd_left p r),
      (Nat.minFac_dvd _).trans (Nat.gcd_dvd_right p r)⟩
  have hinj : Set.InjOn f B := by
    intro p hp q hq hpq
    by_contra hne
    have hcop : Nat.Coprime p q :=
      hP (Finset.mem_filter.mp hp).1 (Finset.mem_filter.mp hq).1 hne
    have h1 : f p ∣ p := (hfp p hp).2.1
    have h2 : f p ∣ q := hpq ▸ (hfp q hq).2.1
    have h3 : f p ∣ Nat.gcd p q := Nat.dvd_gcd h1 h2
    rw [Nat.Coprime.gcd_eq_one hcop] at h3
    have := (hfp p hp).1.one_lt
    have h4 := Nat.dvd_one.mp h3
    omega
  have hcardI : (B.image f).card = B.card := Finset.card_image_of_injOn hinj
  have hprod : ∏ q ∈ B.image f, q ∣ r := by
    apply Finset.prod_primes_dvd r
    · intro q hq
      obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hq
      exact (hfp p hp).1.prime
    · intro q hq
      obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hq
      exact (hfp p hp).2.2
  have hpow : 2 ^ (B.image f).card ≤ ∏ q ∈ B.image f, q := by
    apply Finset.pow_card_le_prod
    intro q hq
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hq
    exact (hfp p hp).1.two_le
  have hle : ∏ q ∈ B.image f, q ≤ r := Nat.le_of_dvd (by omega) hprod
  rw [← hcardI]
  exact Nat.le_log_of_pow_le (by norm_num) (le_trans hpow hle)

/-! ### Analytic part -/

theorem window_psi_diff (N : ℕ) :
    psiN (2 * N) - psiN (N + N / 2) ≤
      (((Ioc (N + N / 2) (2 * N)).filter IsPrimePow).card : ℝ) * Real.log ((2 * N : ℕ) : ℝ) := by
  have hle : N + N / 2 ≤ 2 * N := by omega
  rw [psiN_sub hle]
  have h1 : ∑ d ∈ (Ioc (N + N / 2) (2 * N)).filter IsPrimePow, Λ d =
      ∑ d ∈ Ioc (N + N / 2) (2 * N), Λ d :=
    Finset.sum_filter_of_ne (fun d _ hd => ArithmeticFunction.vonMangoldt_ne_zero_iff.mp hd)
  rw [← h1]
  have hb : ∀ d ∈ (Ioc (N + N / 2) (2 * N)).filter IsPrimePow,
      Λ d ≤ Real.log ((2 * N : ℕ) : ℝ) := by
    intro d hd
    rw [Finset.mem_filter, Finset.mem_Ioc] at hd
    refine ArithmeticFunction.vonMangoldt_le_log.trans (Real.log_le_log ?_ ?_)
    · exact_mod_cast (by omega : 0 < d)
    · exact_mod_cast hd.1.2
  calc _ ≤ _ := Finset.sum_le_card_nsmul _ _ _ hb
    _ = _ := by rw [nsmul_eq_mul]

/-- The final real inequality, in isolation. -/
theorem window_arith {N T k A m1 m2 lam1 lam2 lam C P : ℝ}
    (hT : 0 ≤ T) (hk : 0 ≤ k) (hA1 : 91 / 100 ≤ A) (hA2 : A ≤ 95 / 100)
    (hN : 6 * (k + 2) * (T + 3 * (k + 2) + 60) + 1200 ≤ N)
    (hm1a : 2 * N ≤ 30 * m1 + 29) (hm2 : 60 * m2 ≤ 3 * N + 58)
    (hlam1 : lam1 ≤ 7 / 10 * (k + 2)) (hlam2 : lam2 ≤ 7 / 10 * (k + 2))
    (hlam : lam ≤ 7 / 10 * (k + 2)) (hlam0 : 0 ≤ lam)
    (hC0 : 0 ≤ C) (hC : C ≤ k + 2) (hP : P ≤ T + k)
    (hdiff : (30 * A * m1 - 3 * lam1 - 3) -
      (36 * A * m2 + (36 * A + 2 * lam2 + 2) * C + 100) ≤ P * lam) : False := by
  have hprod : 0 ≤ 6 * (k + 2) * (T + 3 * (k + 2) + 60) :=
    mul_nonneg (by linarith) (by linarith)
  have hX : N / 5 - 319 / 5 ≤ 30 * m1 - 36 * m2 := by linarith
  have hX0 : 0 ≤ 30 * m1 - 36 * m2 := by linarith
  have hAX : 91 / 100 * (30 * m1 - 36 * m2) ≤ A * (30 * m1 - 36 * m2) :=
    mul_le_mul_of_nonneg_right hA1 hX0
  have hE1 : (36 * A + 2 * lam2 + 2) * C ≤ (36 * (95 / 100) + 2 * (7 / 10 * (k + 2)) + 2) * (k + 2) :=
    mul_le_mul (by linarith) hC hC0 (by linarith)
  have hE2 : P * lam ≤ (T + k) * (7 / 10 * (k + 2)) :=
    mul_le_mul hP hlam hlam0 (by linarith)
  nlinarith [hAX, hE1, hE2, mul_nonneg hk hT, mul_nonneg hk hk]

theorem window_card_lower (T N : ℕ)
    (hN : 6 * (Nat.log 2 N + 2) * (T + 3 * (Nat.log 2 N + 2) + 60) + 1200 ≤ N) :
    T + Nat.log 2 N + 1 ≤ ((Ioc (N + N / 2) (2 * N)).filter IsPrimePow).card := by
  by_contra hcon
  replace hcon := not_le.mp hcon
  have hN0 : 1200 ≤ N := le_trans (Nat.le_add_left 1200 _) hN
  have hdiff := window_psi_diff N
  obtain ⟨P, hP⟩ : ∃ P, P = ((Ioc (N + N / 2) (2 * N)).filter IsPrimePow).card := ⟨_, rfl⟩
  rw [← hP] at hdiff hcon
  obtain ⟨k, hk⟩ : ∃ k, k = Nat.log 2 N := ⟨_, rfl⟩
  rw [← hk] at hN hcon
  have hPle : (P : ℝ) ≤ (T : ℝ) + (k : ℝ) := by exact_mod_cast (by omega : P ≤ T + k)
  obtain ⟨m1, hm1⟩ : ∃ m1, m1 = 2 * N / 30 := ⟨_, rfl⟩
  obtain ⟨m2, hm2⟩ : ∃ m2, m2 = (N + N / 2 + 29) / 30 := ⟨_, rfl⟩
  have hm1a : 2 * N ≤ 30 * m1 + 29 := by omega
  have hm1b : 30 * m1 ≤ 2 * N := by omega
  have hm2a : N + N / 2 ≤ 30 * m2 := by omega
  have hm2b : 60 * m2 ≤ 3 * N + 58 := by omega
  have hm2c : 30 * m2 ≤ 2 * N := by omega
  have hm1pos : 1 ≤ m1 := by omega
  have hm2pos : 1 ≤ m2 := by omega
  have hlow : 30 * A30 * m1 - 3 * Real.log (30 * m1) - 3 ≤ psiN (2 * N) :=
    le_trans (b30_bounds m1 hm1pos).1 (le_trans (b30_le_psiN m1) (psiN_mono hm1b))
  have hup : psiN (N + N / 2) ≤ 36 * A30 * m2 +
      (36 * A30 + 2 * Real.log (30 * m2) + 2) * (Nat.clog 6 m2 : ℝ) + 100 :=
    le_trans (psiN_mono hm2a) (psiN_upper m2 hm2pos)
  have hNr : (1200 : ℝ) ≤ N := by exact_mod_cast hN0
  have hm1r : (1 : ℝ) ≤ m1 := by exact_mod_cast hm1pos
  have hm2r : (1 : ℝ) ≤ m2 := by exact_mod_cast hm2pos
  have hpos1 : (0 : ℝ) < 30 * m1 := by linarith
  have hpos2 : (0 : ℝ) < 30 * m2 := by linarith
  have hposN : (0 : ℝ) < 2 * N := by linarith
  have hlam1 : Real.log (30 * (m1 : ℝ)) ≤ Real.log (2 * (N : ℝ)) :=
    Real.log_le_log hpos1 (by exact_mod_cast hm1b)
  have hlam2 : Real.log (30 * (m2 : ℝ)) ≤ Real.log (2 * (N : ℝ)) :=
    Real.log_le_log hpos2 (by exact_mod_cast hm2c)
  have hNk : N < 2 ^ (k + 1) := by
    have := Nat.lt_pow_succ_log_self (b := 2) (by norm_num) N
    rw [← hk] at this
    exact this
  have h2N : (2 : ℝ) * N < 2 ^ (k + 2) := by
    have : (N : ℝ) < 2 ^ (k + 1) := by exact_mod_cast hNk
    calc (2 : ℝ) * N < 2 * 2 ^ (k + 1) := by linarith
      _ = 2 ^ (k + 2) := by ring
  have hlam : Real.log (2 * (N : ℝ)) ≤ 7 / 10 * ((k : ℝ) + 2) := by
    have h := Real.log_lt_log hposN h2N
    rw [Real.log_pow] at h
    have h2 := Real.log_two_lt_d9
    push_cast at h
    have h3 : ((k : ℝ) + 2) * Real.log 2 ≤ ((k : ℝ) + 2) * (7 / 10) :=
      mul_le_mul_of_nonneg_left (by norm_num at h2; linarith) (by positivity)
    linarith
  have hlam0 : 0 ≤ Real.log (2 * (N : ℝ)) :=
    Real.log_nonneg (by linarith)
  have hCn : Nat.clog 6 m2 ≤ k + 1 := by
    apply Nat.clog_le_of_le_pow
    calc m2 ≤ N := by omega
      _ ≤ 2 ^ (k + 1) := hNk.le
      _ ≤ 6 ^ (k + 1) := Nat.pow_le_pow_left (by norm_num) _
  have hC : (Nat.clog 6 m2 : ℝ) ≤ (k : ℝ) + 2 := by
    have : (Nat.clog 6 m2 : ℝ) ≤ (k : ℝ) + 1 := by exact_mod_cast hCn
    linarith
  have hNr' : 6 * ((k : ℝ) + 2) * ((T : ℝ) + 3 * ((k : ℝ) + 2) + 60) + 1200 ≤ N := by
    exact_mod_cast hN
  have hm1a' : (2 : ℝ) * N ≤ 30 * m1 + 29 := by exact_mod_cast hm1a
  have hm2' : (60 : ℝ) * m2 ≤ 3 * N + 58 := by exact_mod_cast hm2b
  push_cast at hdiff
  refine window_arith (N := (N : ℝ)) (T := (T : ℝ)) (k := (k : ℝ)) (A := A30)
    (m1 := (m1 : ℝ)) (m2 := (m2 : ℝ)) (lam1 := Real.log (30 * (m1 : ℝ)))
    (lam2 := Real.log (30 * (m2 : ℝ))) (lam := Real.log (2 * (N : ℝ)))
    (C := (Nat.clog 6 m2 : ℝ)) (P := (P : ℝ)) (Nat.cast_nonneg _) (Nat.cast_nonneg _)
    A30_ge A30_le hNr' hm1a' hm2' (by linarith) (by linarith) hlam hlam0 (Nat.cast_nonneg _)
    hC hPle ?_
  linarith [hlow, hup, hdiff]

theorem copWinC_of_cheb (T N : ℕ)
    (hN : 6 * (Nat.log 2 N + 2) * (T + 3 * (Nat.log 2 N + 2) + 60) + 1200 ≤ N)
    (r : ℕ) (hr : 1 ≤ r) (hrN : 2 * r ≤ N) : CopWinC T N r := by
  have hN0 : 1200 ≤ N := le_trans (Nat.le_add_left 1200 _) hN
  have hcard := window_card_lower T N hN
  have hpw := primePow_pairwise N
  obtain ⟨Q, hQ⟩ : ∃ Q, Q = (Ioc (N + N / 2) (2 * N)).filter IsPrimePow := ⟨_, rfl⟩
  rw [← hQ] at hcard hpw
  have hmem : ∀ D, D ∈ Q ↔ (N + N / 2 < D ∧ D ≤ 2 * N) ∧ IsPrimePow D := by
    intro D
    rw [hQ, Finset.mem_filter, Finset.mem_Ioc]
  have hbad := bad_card_le Q hpw hr
  have hlog : Nat.log 2 r ≤ Nat.log 2 N := Nat.log_mono_right (by omega)
  refine ⟨Q.filter (fun D => D ≠ 2 * N ∧ Nat.Coprime D r), ?_, ?_, ?_⟩
  · have h1 := Finset.card_filter_add_card_filter_not (s := Q) (fun D => D ≠ 2 * N ∧ Nat.Coprime D r)
    have h2 : (Q.filter (fun D => ¬ (D ≠ 2 * N ∧ Nat.Coprime D r))) ⊆
        insert (2 * N) (Q.filter (fun p => ¬ Nat.Coprime p r)) := by
      intro D hD
      rw [Finset.mem_filter] at hD
      rw [Finset.mem_insert, Finset.mem_filter]
      by_cases h : D = 2 * N
      · exact Or.inl h
      · exact Or.inr ⟨hD.1, fun hc => hD.2 ⟨h, hc⟩⟩
    have h3 := Finset.card_le_card h2
    have h4 := Finset.card_insert_le (2 * N) (Q.filter (fun p => ¬ Nat.Coprime p r))
    omega
  · intro D hD
    have h1 := Finset.mem_filter.mp hD
    have hDQ := h1.1
    have hne := h1.2.1
    have hcop := h1.2.2
    have h := ((hmem D).mp hDQ).1
    refine ⟨by omega, by omega, hcop⟩
  · exact hpw.mono (Finset.coe_subset.mpr (Finset.filter_subset _ _))

end Cheb30
end Gap
end Sext6
end LRSpectrumFull
