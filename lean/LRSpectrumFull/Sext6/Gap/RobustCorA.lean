import LRSpectrumFull.Sext6.Gap.RobustCore
import LRSpectrumFull.Sext6.Gap.OneOverR
import Mathlib.NumberTheory.PrimeCounting
import Mathlib.Tactic.NormNum.Prime

/-!
# Corollary S' (shape of every speed vector below `1/N`) and PrimeWin transfer lemmas  [2026-11-25]

Source: the accompanying notes on Theorem S (Corollary S').
Vectors `v : Fin (n+1) → ℤ` (a finite family, repetitions allowed), all entries `≥ 1`.

* `primeWin_le`     : `PrimeWin k N r → r + 2 ≤ N`.
* `winK`            : `T` distinct primes in `[N+1+N/2, 2N]` give `T ≤ #primes there` (generalises `win7`).
* `primeWin_of_window` : `T_k ≤ #(primes in [N+1+N/2, 2N]) → ∀ r, 2r ≤ N → PrimeWin k N r`.
* `cor_a` (S'(a))   : `PrimeWin k N r` for every `1 ≤ r`, `2r ≤ N`; `≤ k` entries `> N`; `ML v < 1/N`
                      ⟹ every integer `r ∈ [1, N/2]` is an entry of `v`.
* `cor_b` (S'(b))   : `N < 2 r ≤ 2 N`, `r` not an entry, `ML v < 1/N` ⟹ `r` divides an entry `> N`
                      (no bound on the number of large entries, no prime count).
No `sorry`, no `axiom`.

Convention: `N` is a natural number (the size of the ambient interval `[1,N]`); `v : Fin (n+1) → ℤ` is an arbitrary finite family of speeds (repetitions allowed) and `n` is not linked to `N`; `k` counts the entries `> N`. Speeds are the moving runners; the runner at rest is not counted, so a vector of `N` speeds means `N + 1` runners and the Lonely Runner value is `1/(N+1)`.
Hypotheses: those of the individual statements (numerical bounds, structural conditions and, where named in the list above, window predicates such as `PrimeWin`, `CopWin`, `PrimeWindow7`, which later modules discharge for explicit ranges). The unproved predicates `DusartPi`, `LRCHyp`, `CopWinHyp` are not hypotheses of any statement in this module.
Axiom audit: covered by `Axioms9` (first); every later audit module imports this module (`#print axioms`; declarations not printed there are bricks of printed ones, so their axioms are bounded by the printed lines).
-/

namespace LRSpectrumFull
namespace Sext6
namespace Gap

/-- A `PrimeWin` forces room: `r + 2 ≤ N`. -/
theorem primeWin_le {k N r : ℕ} (h : PrimeWin k N r) : r + 2 ≤ N := by
  unfold PrimeWin at h
  have hpos : 0 < ((Finset.Icc (N + 1 + r) (2 * N - 1)).filter Nat.Prime).card := by omega
  obtain ⟨x, hx⟩ := Finset.card_pos.mp hpos
  have hx' := (Finset.mem_Icc.mp (Finset.mem_filter.mp hx).1)
  omega

/-- `T` distinct primes in `[N+1+N/2, 2N]` give `T ≤` the number of primes there. -/
theorem winK {T N : ℕ} (ps : List ℕ) (hnd : ps.Nodup) (hlen : T ≤ ps.length)
    (hpr : ∀ p ∈ ps, p.Prime) (hlo : ∀ p ∈ ps, N + 1 + N / 2 ≤ p) (hhi : ∀ p ∈ ps, p ≤ 2 * N) :
    T ≤ ((Finset.Icc (N + 1 + N / 2) (2 * N)).filter Nat.Prime).card := by
  have hsub : ps.toFinset ⊆ (Finset.Icc (N + 1 + N / 2) (2 * N)).filter Nat.Prime := by
    intro p hp
    rw [List.mem_toFinset] at hp
    exact Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨hlo p hp, hhi p hp⟩, hpr p hp⟩
  have h := Finset.card_le_card hsub
  rw [List.toFinset_card_of_nodup hnd] at h
  omega

/-- From the single window at `r = N/2` (up to `2N`) to `PrimeWin` for every `r` with `2 r ≤ N`:
the window shrinks as `r` grows and `2N` is not prime. -/
theorem primeWin_of_window {k N : ℕ} (hN : 2 ≤ N)
    (h : 3 * k * (k + 1) + 1 ≤ ((Finset.Icc (N + 1 + N / 2) (2 * N)).filter Nat.Prime).card) :
    ∀ r : ℕ, 2 * r ≤ N → PrimeWin k N r := by
  intro r hr
  unfold PrimeWin
  refine le_trans h (Finset.card_le_card ?_)
  intro x hx
  obtain ⟨hx1, hx2⟩ := Finset.mem_filter.mp hx
  obtain ⟨hlo, hhi⟩ := Finset.mem_Icc.mp hx1
  have hne : x ≠ 2 * N := by
    intro he
    rw [he] at hx2
    exact Nat.not_prime_mul (by norm_num) (by omega) hx2
  exact Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨by omega, by omega⟩, hx2⟩

/-- **Corollary S'(a).**  If `PrimeWin k N r` holds for every `1 ≤ r`, `2 r ≤ N`, then every vector of
positive integers with at most `k` entries above `N` and `ML v < 1/N` contains every integer of `[1, N/2]`. -/
theorem cor_a {n k N : ℕ} (hk : 1 ≤ k)
    (hP : ∀ r : ℕ, 1 ≤ r → 2 * r ≤ N → PrimeWin k N r)
    (v : Fin (n + 1) → ℤ) (hpos : ∀ i, 1 ≤ v i)
    (hcard : (Finset.univ.filter (fun i : Fin (n + 1) => (N : ℤ) < v i)).card ≤ k)
    (hML : ML v < 1 / (N : ℝ)) :
    ∀ r : ℕ, 1 ≤ r → 2 * r ≤ N → ∃ i, v i = (r : ℤ) := by
  intro r hr1 hr2
  by_contra hne
  push Not at hne
  have hPr := hP r hr1 hr2
  have hrN := primeWin_le hPr
  have := ML_ge_robust (n := n) (k := k) (N := N) (r := r) hk hr1 hrN hPr v
    (by
      intro i
      by_cases hbig : (N : ℤ) < v i
      · exact Or.inr hbig
      · exact Or.inl ⟨hpos i, not_lt.mp hbig, hne i⟩) hcard
  exact absurd hML (not_lt.mpr this)

/-- **Corollary S'(b).**  `N < 2 r ≤ 2 N`, `r` not an entry of the positive vector `v`, `ML v < 1/N`:
then `r` divides some entry of `v` above `N`.  No bound on the number of large entries. -/
theorem cor_b {n N r : ℕ} (hr1 : N < 2 * r) (hr2 : r ≤ N)
    (v : Fin (n + 1) → ℤ) (hpos : ∀ i, 1 ≤ v i)
    (hML : ML v < 1 / (N : ℝ)) (hmiss : ∀ i, v i ≠ (r : ℤ)) :
    ∃ i, (N : ℤ) < v i ∧ (r : ℤ) ∣ v i := by
  by_contra hcon
  push Not at hcon
  have hr0 : 0 < r := by omega
  have hrR : (0 : ℝ) < r := by exact_mod_cast hr0
  have hnd : ∀ i, ¬ ((r : ℤ) ∣ v i) := by
    intro i hd
    by_cases hbig : (N : ℤ) < v i
    · exact hcon i hbig hd
    · obtain ⟨c, hc⟩ := hd
      have h1 := hpos i
      have h2 : v i ≤ (N : ℤ) := not_lt.mp hbig
      have hr0' : (0 : ℤ) < r := by exact_mod_cast hr0
      have hc1 : 1 ≤ c := by
        by_contra hc0
        push Not at hc0
        nlinarith
      have hrN' : (N : ℤ) < 2 * r := by exact_mod_cast hr1
      rcases (by omega : c = 1 ∨ 2 ≤ c) with hc1' | hc2
      · rw [hc1'] at hc
        exact hmiss i (by linarith)
      · nlinarith
  have hfar : 1 / (N : ℝ) ≤ ML v := by
    refine ML_ge_of_far v (1 / (N : ℝ)) (1 / (r : ℝ)) ?_
    intro i
    have e : ((v i : ℤ) : ℝ) * (1 / (r : ℝ)) = ((v i : ℤ) : ℝ) / r := by
      rw [mul_one_div]
    rw [e]
    have hNR : (r : ℝ) ≤ N := by exact_mod_cast hr2
    exact (one_div_le_one_div_of_le hrR hNR).trans (nid_div_ge_inv hr0 (v i) (hnd i))
  exact absurd hML (not_lt.mpr hfar)

end Gap
end Sext6
end LRSpectrumFull
