/-
# L1' (clean prime forces the residues to contain a unit multiple of {1..6}), VERIFIED target,
and the named hypotheses for the parts not proved (L2, L3, L4, scaling), as Props in a structure.
-/
import LRSpectrumFull.Sext6.L1

namespace LRSpectrumFull
namespace Sext6

/-- **L1'.** If `p` is clean, `p ∤ v_i`, and `ML v ≤ 1/7`, then for some unit `u` mod `p`, each of
`u·1, …, u·6` is, up to sign, one of the speeds mod `p`. -/
theorem L1prime (p : ℕ) (hp : 0 < p) (hclean : CleanPrime p) (v : Fin 6 → ℤ)
    (hML : ML v ≤ 1 / 7) (hnd : ∀ i, ¬ (p : ℤ) ∣ v i) :
    ∃ u : ℤ, ¬ (p : ℤ) ∣ u ∧ ∀ i ∈ Finset.Icc (1 : ℤ) 6,
      ∃ j, (p : ℤ) ∣ v j - u * i ∨ (p : ℤ) ∣ v j + u * i := by
  have hcard : (Finset.univ.image v).card ≤ 6 := by
    calc (Finset.univ.image v).card ≤ (Finset.univ : Finset (Fin 6)).card := Finset.card_image_le
      _ = 6 := by simp
  have hnz : ∀ r ∈ Finset.univ.image v, ¬ (p : ℤ) ∣ r := by
    intro r hr
    obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hr
    exact hnd j
  obtain ⟨u, hu, h⟩ := hclean _ hcard hnz (L1 v hML p hp)
  refine ⟨u, hu, fun i hi => ?_⟩
  obtain ⟨r, hr, hr'⟩ := h i hi
  obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hr
  exact ⟨j, hr'⟩

/-- The second ratio-closed sextuple. -/
def v2 : Fin 6 → ℤ := fun i => [10, 12, 15, 20, 30, 60].getD i.val 0

/-- Named hypotheses for the pieces NOT proved in this pilot (never axioms).  Each is a Prop whose
statement is the paper's, fully quantified. -/
structure PRRPieces : Prop where
  /-- ML is invariant under positive integer dilation. -/
  dilation : ∀ (c : ℤ) (v : Fin 6 → ℤ), 0 < c → ML (fun i => c * v i) = ML v
  /-- L2 (pair counting): if all of the 150 clean primes are clean and `v ≤ H`, every pairwise ratio
  of a tight sextuple is `a/b` with `a ≠ b ∈ {1..6}`. -/
  L2 : ∀ v : Fin 6 → ℤ, Function.Injective v → (∀ i, 0 < v i) → (∀ i, v i < 17010000) →
    ML v ≤ 1 / 7 → ∀ i j, i ≠ j → ∃ a b : ℤ, a ∈ Finset.Icc (1 : ℤ) 6 ∧ b ∈ Finset.Icc (1 : ℤ) 6 ∧
      a ≠ b ∧ b * v i = a * v j
  /-- L3 (ratio-closed primitive sextuples). -/
  L3 : ∀ v : Fin 6 → ℤ, Function.Injective v → (∀ i, 0 < v i) → Primitive v →
    (∀ i j, i ≠ j → ∃ a b : ℤ, a ∈ Finset.Icc (1 : ℤ) 6 ∧ b ∈ Finset.Icc (1 : ℤ) 6 ∧
      a ≠ b ∧ b * v i = a * v j) →
    (∃ σ : Equiv.Perm (Fin 6), ∀ i, v i = (σ i : ℕ) + 1) ∨
    (∃ σ : Equiv.Perm (Fin 6), ∀ i, v i = v2 (σ i))
  /-- L4: ML of the second ratio-closed sextuple exceeds 1/7 (it equals 1/4). -/
  L4 : ¬ ML v2 ≤ 1 / 7

end Sext6
end LRSpectrumFull

#print axioms LRSpectrumFull.Sext6.L1prime
