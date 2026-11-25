import LRSpectrumFull.Sext6.Gap.OELow
import Mathlib.NumberTheory.PrimeCounting
import Mathlib.Tactic.NormNum.Prime

/-!
# Theorem OE-low, prime window: generic lemmas  [2026-11-24]

* `win7`        : seven distinct primes in `[N+1+N/2, 2N]` give seven primes in that interval (as a card bound).
* `window_mono` : the case `r = N/2` implies `PrimeWindow7 N` (the interval only grows as `r` decreases).
* `card_primes_Icc` : `π n = π m + #(primes in [m+1, n])` for `m ≤ n` (used by the analytic step).
No `sorry`, no `axiom`.

Convention: No speed vector is involved in this module (number theory or real analysis); `N` denotes a natural number, the size of the ambient interval `[1,N]`.
Hypotheses: those of the individual statements (numerical bounds, structural conditions and, where named in the list above, window predicates such as `PrimeWin`, `CopWin`, `PrimeWindow7`, which later modules discharge for explicit ranges). The unproved predicates `DusartPi`, `LRCHyp`, `CopWinHyp` are not hypotheses of any statement in this module.
Axiom audit: covered by `Axioms6` (first); every later audit module imports this module (`#print axioms`; declarations not printed there are bricks of printed ones, so their axioms are bounded by the printed lines).
-/

namespace LRSpectrumFull
namespace Sext6
namespace Gap

theorem win7 {N : ℕ} (ps : List ℕ) (hnd : ps.Nodup) (hlen : 7 ≤ ps.length)
    (hpr : ∀ p ∈ ps, p.Prime) (hlo : ∀ p ∈ ps, N + 1 + N / 2 ≤ p) (hhi : ∀ p ∈ ps, p ≤ 2 * N) :
    7 ≤ ((Finset.Icc (N + 1 + N / 2) (2 * N)).filter Nat.Prime).card := by
  have hsub : ps.toFinset ⊆ (Finset.Icc (N + 1 + N / 2) (2 * N)).filter Nat.Prime := by
    intro p hp
    rw [List.mem_toFinset] at hp
    exact Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨hlo p hp, hhi p hp⟩, hpr p hp⟩
  have h := Finset.card_le_card hsub
  rw [List.toFinset_card_of_nodup hnd] at h
  omega

theorem window_mono {N : ℕ}
    (h : 7 ≤ ((Finset.Icc (N + 1 + N / 2) (2 * N)).filter Nat.Prime).card) : PrimeWindow7 N := by
  intro r hr
  refine le_trans h (Finset.card_le_card ?_)
  apply Finset.filter_subset_filter
  intro x hx
  rw [Finset.mem_Icc] at hx ⊢
  omega

/-- `π n = π m + #(primes in [m+1, n])`. -/
theorem card_primes_Icc {m n : ℕ} (h : m ≤ n) :
    Nat.primeCounting n =
      Nat.primeCounting m + ((Finset.Icc (m + 1) n).filter Nat.Prime).card := by
  have e1 : ∀ k, Nat.primeCounting k = ((Finset.range (k + 1)).filter Nat.Prime).card := by
    intro k
    unfold Nat.primeCounting Nat.primeCounting'
    exact Nat.count_eq_card_filter_range _ _
  rw [e1 n, e1 m]
  have hr : Finset.range (n + 1) = Finset.range (m + 1) ∪ Finset.Icc (m + 1) n := by
    ext x
    simp only [Finset.mem_range, Finset.mem_union, Finset.mem_Icc]
    omega
  have hd : Disjoint ((Finset.range (m + 1)).filter Nat.Prime)
      ((Finset.Icc (m + 1) n).filter Nat.Prime) := by
    rw [Finset.disjoint_left]
    intro x hx1 hx2
    have := (Finset.mem_range.mp (Finset.mem_filter.mp hx1).1)
    have := (Finset.mem_Icc.mp (Finset.mem_filter.mp hx2).1).1
    omega
  rw [hr, Finset.filter_union, Finset.card_union_of_disjoint hd]

end Gap
end Sext6
end LRSpectrumFull
