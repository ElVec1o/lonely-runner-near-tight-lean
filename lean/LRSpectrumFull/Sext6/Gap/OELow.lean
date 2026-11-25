import LRSpectrumFull.Sext6.Gap.OELowCore
import LRSpectrumFull.Sext6.Gap.OELowPigeon
import LRSpectrumFull.Sext6.Gap.OELowCube

/-!
# Theorem OE-low (assembly)  [2026-11-24]

For `1 ≤ r`, `2 r ≤ N`, `w > N`:  `1/N ≤ ML ([N] \ {r} ∪ {w})`, under explicit hypotheses.

* `OE_low_of_primes_gen`  : `N ≥ 3`, seven primes in `[N + 1 + r, 2N]`  ⟹  the bound (all `w > N`).
* `OE_low_of_primes`      : the same with `N ≥ 14` (the shape asked for in the brief).
* `PrimeWindow7`, `OE_low_of_window` : hypothesis (H-primes) as a predicate on `N`.
* `WitnessCover`, `ML_ge_inv_of_cover`, `OE_low_of_cover` : the exact interface for the finite range
  (`14 ≤ N ≤ 78`, not formalised here): per `(N, r, w)` a Lemma-W witness or a Lemma-L modulus.
Source: the accompanying notes on Theorem OE sections 3 and 7 (LR-8).
No `sorry`, no `axiom`; the only extra hypotheses are the explicit ones named above.

Convention: `N = k + 1` is the number of entries (speeds) of the one-entry vector `wFam k r w = ([1,N] \ {r}) ∪ {w}`. Speeds are the moving runners; the runner at rest is not counted, so a vector of `N` speeds means `N + 1` runners and the Lonely Runner value is `1/(N+1)`.
Hypotheses: The prime-window hypothesis (seven primes in `[N+1+r, 2N]`, or its predicate `PrimeWindow7 N`) and the finite-range interface `WitnessCover` are explicit hypotheses of the assembly theorems; `OE_low_of_primes_gen` needs `N ≥ 3`, `OE_low_of_primes` needs `N ≥ 14`.
Axiom audit: covered by `Axioms5` (first); every later audit module imports this module (`#print axioms`; declarations not printed there are bricks of printed ones, so their axioms are bounded by the printed lines).
-/

namespace LRSpectrumFull
namespace Sext6
namespace Gap

theorem cube_add_le (N r : ℕ) : N ^ 3 + r ≤ (N + 1 + r) ^ 3 := by
  have h : (N + 1 + r) ^ 3 =
      N ^ 3 + (3 * N ^ 2 * (1 + r) + 3 * N * (1 + r) ^ 2 + (1 + r) ^ 3) := by ring
  have h2 : 1 + r ≤ (1 + r) ^ 3 := Nat.le_self_pow (by norm_num) _
  rw [h]
  omega

/-- **Theorem OE-low, conditional on the prime window.**  `N ≥ 3`, `1 ≤ r`, `2 r ≤ N`, `w > N`, and at least
seven primes in `[N + 1 + r, 2N]`  ⟹  `1/N ≤ ML ([N] \ {r} ∪ {w})`. -/
theorem OE_low_of_primes_gen {k N r w : ℕ} (hk : k + 1 = N) (hN : 3 ≤ N) (hr1 : 1 ≤ r)
    (hr : 2 * r ≤ N) (hw : N < w)
    (hP : 7 ≤ ((Finset.Icc (N + 1 + r) (2 * N)).filter Nat.Prime).card) :
    1 / (N : ℝ) ≤ ML (wFam k r w) := by
  by_cases hlarge : N ^ 3 ≤ w
  · exact ML_ge_inv_of_cube hk hN hr1 hr hlarge
  · have hsmall : w < N ^ 3 := Nat.lt_of_not_le hlarge
    have hS_prime : ∀ p ∈ (Finset.Icc (N + 1 + r) (2 * N)).filter Nat.Prime, p.Prime :=
      fun p hp => (Finset.mem_filter.mp hp).2
    have hS_ge : ∀ p ∈ (Finset.Icc (N + 1 + r) (2 * N)).filter Nat.Prime, N + 1 + r ≤ p :=
      fun p hp => (Finset.mem_Icc.mp (Finset.mem_filter.mp hp).1).1
    have hex : ∃ p ∈ (Finset.Icc (N + 1 + r) (2 * N)).filter Nat.Prime,
        ¬ ((p : ℤ) ∣ (w : ℤ)) ∧ ¬ ((p : ℤ) ∣ (w : ℤ) - (r : ℤ)) ∧
          ¬ ((p : ℤ) ∣ (w : ℤ) + (r : ℤ)) := by
      by_contra hcon
      have hfail : ∀ p ∈ (Finset.Icc (N + 1 + r) (2 * N)).filter Nat.Prime,
          ((p : ℤ) ∣ (w : ℤ)) ∨ ((p : ℤ) ∣ (w : ℤ) - (r : ℤ)) ∨ ((p : ℤ) ∣ (w : ℤ) + (r : ℤ)) := by
        intro p hp
        by_contra hf
        simp only [not_or] at hf
        exact hcon ⟨p, hp, hf.1, hf.2.1, hf.2.2⟩
      have h1 := pigeon_small _ hS_prime hS_ge hP (by omega) hw hfail
      have h3 := cube_add_le N r
      omega
    obtain ⟨p, hp, h0, h1, h2⟩ := hex
    have hpm := Finset.mem_filter.mp hp
    have hpI := Finset.mem_Icc.mp hpm.1
    have hpp := hpm.2
    have hcop : Nat.Coprime p r := by
      rw [Nat.Prime.coprime_iff_not_dvd hpp]
      intro hd
      have := Nat.le_of_dvd (by omega) hd
      omega
    exact ML_ge_inv_fam hk hr1 (by omega) hpI.1 hpI.2 hcop h0 h1 h2

/-- **Theorem OE-low (conditional on seven primes in `[N+1+r, 2N]`), `N ≥ 14` form.** -/
theorem OE_low_of_primes {k N r w : ℕ} (hk : k + 1 = N) (hN : 14 ≤ N) (hr1 : 1 ≤ r)
    (hr : 2 * r ≤ N) (hw : N < w)
    (hP : 7 ≤ ((Finset.Icc (N + 1 + r) (2 * N)).filter Nat.Prime).card) :
    1 / (N : ℝ) ≤ ML (wFam k r w) :=
  OE_low_of_primes_gen hk (by omega) hr1 hr hw hP

/-- Hypothesis (H-primes) as a predicate on `N`: every window `[N+1+r, 2N]`, `2 r ≤ N`, holds seven primes.
True for every `N ≥ 79` (sieve to `10^7`, Rosser-Schoenfeld beyond; NOT proved here). -/
def PrimeWindow7 (N : ℕ) : Prop :=
  ∀ r : ℕ, 2 * r ≤ N → 7 ≤ ((Finset.Icc (N + 1 + r) (2 * N)).filter Nat.Prime).card

theorem OE_low_of_window {k N r w : ℕ} (hk : k + 1 = N) (hN : 14 ≤ N) (hW : PrimeWindow7 N)
    (hr1 : 1 ≤ r) (hr : 2 * r ≤ N) (hw : N < w) : 1 / (N : ℝ) ≤ ML (wFam k r w) :=
  OE_low_of_primes hk hN hr1 hr hw (hW r hr)

/-- The per-`(N, r, w)` certificate target for the finite range: a Lemma-W witness modulus, or a
Lemma-L modulus. -/
def WitnessCover (N r w : ℕ) : Prop :=
  (∃ D, N + 1 + r ≤ D ∧ D ≤ 2 * N ∧ Nat.Coprime D r ∧ ¬ ((D : ℤ) ∣ (w : ℤ)) ∧
      ¬ ((D : ℤ) ∣ (w : ℤ) - (r : ℤ)) ∧ ¬ ((D : ℤ) ∣ (w : ℤ) + (r : ℤ))) ∨
  (∃ D E, N + 1 + r ≤ D ∧ D + E = 2 * N ∧ 1 ≤ E ∧ Nat.Coprime D r ∧ D * N ^ 2 ≤ 2 * E * w)

theorem ML_ge_inv_of_cover {k N r w : ℕ} (hk : k + 1 = N) (hN : 2 ≤ N) (hr1 : 1 ≤ r)
    (hr2 : r ≤ N) (h : WitnessCover N r w) : 1 / (N : ℝ) ≤ ML (wFam k r w) := by
  rcases h with ⟨D, hD, hDN, hcop, h0, h1, h2⟩ | ⟨D, E, hD, hDE, hE, hcop, hw⟩
  · exact ML_ge_inv_fam hk hr1 hr2 hD hDN hcop h0 h1 h2
  · exact ML_ge_inv_large hk hN hD hDE hE hcop hw

/-- **Reduction of Theorem OE-low to a finite certificate.**  For `N ≥ 3`, `1 ≤ r`, `2 r ≤ N`: if every
`w` with `N < w < N ^ 3` is covered by `WitnessCover`, then `1/N ≤ ML` for every `w > N`. -/
theorem OE_low_of_cover {k N r : ℕ} (hk : k + 1 = N) (hN : 3 ≤ N) (hr1 : 1 ≤ r)
    (hr : 2 * r ≤ N) (hcov : ∀ w, N < w → w < N ^ 3 → WitnessCover N r w) (w : ℕ) (hw : N < w) :
    1 / (N : ℝ) ≤ ML (wFam k r w) := by
  by_cases hlarge : N ^ 3 ≤ w
  · exact ML_ge_inv_of_cube hk hN hr1 hr hlarge
  · exact ML_ge_inv_of_cover hk (by omega) hr1 (by omega) (hcov w hw (Nat.lt_of_not_le hlarge))

end Gap
end Sext6
end LRSpectrumFull
