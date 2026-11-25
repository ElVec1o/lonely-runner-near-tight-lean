import LRSpectrumFull.Sext6.Gap.OELowCore

/-!
# Theorem OE-low, the unconditional large-`w` branch  [2026-11-24]

For `1 ≤ r`, `2 r ≤ N`, `N ≥ 3`, there is an integer `D` with `N + 1 + r ≤ D ≤ 2N - 1` and `gcd(D, r) = 1`
(`D = N + r + 1` if `r ∣ N`, else `D = r (⌊N/r⌋ + 2) + 1`; both are `≡ 1 mod r`).  Lemma L with this `D`
then covers every `w ≥ N³`, with no prime-window hypothesis at all.

* `exists_coprime_window` : the integer `D`.
* `ML_ge_inv_of_cube`     : `N ≥ 3`, `1 ≤ r`, `2 r ≤ N`, `N³ ≤ w` ⟹ `1/N ≤ ML ([N] \ {r} ∪ {w})`.
No `sorry`, no `axiom`.

Convention: `N = k + 1` is the number of entries (speeds) of the one-entry vector `wFam k r w = ([1,N] \ {r}) ∪ {w}`. Speeds are the moving runners; the runner at rest is not counted, so a vector of `N` speeds means `N + 1` runners and the Lonely Runner value is `1/(N+1)`.
Hypotheses: those of the individual statements (numerical bounds, structural conditions and, where named in the list above, window predicates such as `PrimeWin`, `CopWin`, `PrimeWindow7`, which later modules discharge for explicit ranges). The unproved predicates `DusartPi`, `LRCHyp`, `CopWinHyp` are not hypotheses of any statement in this module.
Axiom audit: covered by `Axioms5` (first); every later audit module imports this module (`#print axioms`; declarations not printed there are bricks of printed ones, so their axioms are bounded by the printed lines).
-/

namespace LRSpectrumFull
namespace Sext6
namespace Gap

/-- A modulus coprime to `r` in the window `[N + 1 + r, 2N - 1]`. -/
theorem exists_coprime_window {N r : ℕ} (hN : 3 ≤ N) (hr1 : 1 ≤ r) (hr : 2 * r ≤ N) :
    ∃ D, N + 1 + r ≤ D ∧ D + 1 ≤ 2 * N ∧ Nat.Coprime D r := by
  by_cases hdvd : r ∣ N
  · obtain ⟨q, hq⟩ := hdvd
    refine ⟨N + 1 + r, le_rfl, by omega, ?_⟩
    have e : N + 1 + r = r * (q + 1) + 1 := by rw [hq]; ring
    rw [e]
    exact (Nat.coprime_mul_left_add_left 1 r (q + 1)).mpr (Nat.coprime_one_left r)
  · have hmod : 0 < N % r := Nat.pos_of_ne_zero (fun h => hdvd (Nat.dvd_of_mod_eq_zero h))
    have hlt : N % r < r := Nat.mod_lt _ (by omega)
    have hdm : r * (N / r) + N % r = N := Nat.div_add_mod N r
    have hne : N ≠ 2 * r := fun h => hdvd ⟨2, by omega⟩
    obtain ⟨c, hc⟩ : ∃ c, c = r * (N / r) := ⟨_, rfl⟩
    obtain ⟨m, hm⟩ : ∃ m, m = N % r := ⟨_, rfl⟩
    rw [← hc, ← hm] at hdm
    rw [← hm] at hmod hlt
    have e : r * (N / r + 2) + 1 = c + 2 * r + 1 := by rw [hc]; ring
    refine ⟨r * (N / r + 2) + 1, ?_, ?_, ?_⟩
    · rw [e]; omega
    · rw [e]; omega
    · exact (Nat.coprime_mul_left_add_left 1 r (N / r + 2)).mpr (Nat.coprime_one_left r)

/-- **Unconditional large-`w` branch.**  For `N ≥ 3`, `1 ≤ r`, `2 r ≤ N` and `N ^ 3 ≤ w`:
`1/N ≤ ML (([N] \ {r}) ∪ {w})`. -/
theorem ML_ge_inv_of_cube {k N r w : ℕ} (hk : k + 1 = N) (hN : 3 ≤ N) (hr1 : 1 ≤ r)
    (hr : 2 * r ≤ N) (hw : N ^ 3 ≤ w) : 1 / (N : ℝ) ≤ ML (wFam k r w) := by
  obtain ⟨D, hD1, hD2, hcop⟩ := exists_coprime_window hN hr1 hr
  obtain ⟨E, hE⟩ : ∃ E, D + E = 2 * N := ⟨2 * N - D, by omega⟩
  refine ML_ge_inv_large hk (by omega) hD1 hE (by omega) hcop ?_
  have h1 : D * N ^ 2 ≤ 2 * N * N ^ 2 := Nat.mul_le_mul_right (N ^ 2) (by omega)
  have h2 : 2 * N * N ^ 2 = 2 * N ^ 3 := by ring
  have h3 : 2 * N ^ 3 ≤ 2 * w := Nat.mul_le_mul_left 2 hw
  have h4 : 2 * w ≤ 2 * E * w := Nat.mul_le_mul_right w (by omega)
  calc D * N ^ 2 ≤ 2 * N * N ^ 2 := h1
    _ = 2 * N ^ 3 := h2
    _ ≤ 2 * w := h3
    _ ≤ 2 * E * w := h4

end Gap
end Sext6
end LRSpectrumFull
