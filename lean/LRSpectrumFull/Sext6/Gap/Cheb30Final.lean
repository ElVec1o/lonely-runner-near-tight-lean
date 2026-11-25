import LRSpectrumFull.Sext6.Gap.Cheb30Window

/-!
# Chebyshev's 30-combination: the clean corollary  [2026-11-25]

`copWinC_of_cheb_N` : for `N ≥ 10^5` and `67 T² ≤ N` (the shape of the Dusart-based window lemma),
`CopWinC T N r` holds for every `1 ≤ r`, `2 r ≤ N`.  No `DusartPi` hypothesis.
No `sorry`, no `axiom`.

Convention: No speed vector is involved in this module (number theory or real analysis); `N` denotes a natural number, the size of the ambient interval `[1,N]`.
Hypotheses: those of the individual statements (numerical bounds, structural conditions and, where named in the list above, window predicates such as `PrimeWin`, `CopWin`, `PrimeWindow7`, which later modules discharge for explicit ranges). The unproved predicates `DusartPi`, `LRCHyp`, `CopWinHyp` are not hypotheses of any statement in this module.
Axiom audit: covered by `Cheb30Axioms` (first); every later audit module imports this module (`#print axioms`; declarations not printed there are bricks of printed ones, so their axioms are bounded by the printed lines).
-/

namespace LRSpectrumFull
namespace Sext6
namespace Gap
namespace Cheb30

theorem l_sq_bound : ∀ k : ℕ, 16 ≤ k → 100 * (k + 2) ^ 2 ≤ 2 ^ k := by
  intro k hk
  induction k, hk using Nat.le_induction with
  | base => norm_num
  | succ k hk ih =>
    rw [pow_succ 2 k]
    nlinarith [ih, hk]

theorem cheb_hyp (T N : ℕ) (hN : 100000 ≤ N) (hT : 67 * T ^ 2 ≤ N) :
    6 * (Nat.log 2 N + 2) * (T + 3 * (Nat.log 2 N + 2) + 60) + 1200 ≤ N := by
  have hN0 : N ≠ 0 := by omega
  have h2k : 2 ^ (Nat.log 2 N) ≤ N := Nat.pow_log_le_self 2 hN0
  have hk16 : 16 ≤ Nat.log 2 N :=
    Nat.le_log_of_pow_le (by norm_num) (by norm_num; omega)
  have hb := l_sq_bound _ hk16
  obtain ⟨k, hk⟩ : ∃ k, k = Nat.log 2 N := ⟨_, rfl⟩
  rw [← hk] at hk16 hb h2k ⊢
  have h1 : (100 * (k + 2) ^ 2 : ℤ) ≤ N := by exact_mod_cast hb.trans h2k
  have h2 : (67 * T ^ 2 : ℤ) ≤ N := by exact_mod_cast hT
  have h3 : (100000 : ℤ) ≤ N := by exact_mod_cast hN
  have h4 : (16 : ℤ) ≤ k := by exact_mod_cast hk16
  have hT0 : (0 : ℤ) ≤ T := by positivity
  have key : (6 * (k + 2) * (T + 3 * (k + 2) + 60) + 1200 : ℤ) ≤ N := by
    nlinarith [sq_nonneg (4 * ((k : ℤ) + 2) - 5 * T), mul_nonneg (by linarith : (0 : ℤ) ≤ k - 16)
      (by linarith : (0 : ℤ) ≤ k + 2)]
  exact_mod_cast key

theorem copWinC_of_cheb_N (T N : ℕ) (hN : 100000 ≤ N) (hT : 67 * T ^ 2 ≤ N)
    (r : ℕ) (hr : 1 ≤ r) (hrN : 2 * r ≤ N) : CopWinC T N r :=
  copWinC_of_cheb T N (cheb_hyp T N hN hT) r hr hrN

end Cheb30
end Gap
end Sext6
end LRSpectrumFull
