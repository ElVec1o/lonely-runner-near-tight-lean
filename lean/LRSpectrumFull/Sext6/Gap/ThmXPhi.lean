import LRSpectrumFull.Sext6.Gap.ThmXMain
import Mathlib.Data.Nat.Totient
import Mathlib.Data.Finset.Sort

/-!
# Theorem X, part 4: the window `W` as a `Finset`, `|W| = φ(r)`, and the vectors `IsV`  [2026-11-25]

Source: the accompanying notes on Theorem X, Sections 0 (i) and 3 (i).

* `winSet N r`      : `W = {D ∈ [N+r+1, N+2r] : gcd(D, r) = 1}` as a `Finset ℕ`.
* `mem_winSet`      : membership.
* `winSet_card`     : `|W| = φ(r)` for every `N` and `r` (`r` consecutive integers form a complete residue system;
  Mathlib: `Nat.filter_coprime_Ico_eq_totient`).
* `isV_out_eq`      : for `IsV N r v`, the entries of `v` exceeding `N` are exactly the elements of `W`.
* `isV_out_card`    : hence `|V \ [N]| = φ(r)` (entries of `v` above `N`, as a `Finset ℤ`).
* `isV_ne_r`        : the runner `r` is not an entry.
* `exists_isV`      : for `2 ≤ r`, `2 r ≤ N` some `v : Fin (m+1) → ℤ` satisfies `IsV N r v` (existence of the family).
No `sorry`, no `axiom`.

Convention: `N` is the size of the ambient interval `[N]`; entries of `v` are integers, `IsV N r v` says the entry set is
exactly `([1,N] \ {r}) ∪ W` (repetitions and order allowed).
Hypotheses: those of the individual statements.
Axiom audit: covered by `Axioms25`.
-/

namespace LRSpectrumFull
namespace Sext6
namespace Gap

/-- The window `W = {D ∈ [N+r+1, N+2r] : gcd(D, r) = 1}`. -/
def winSet (N r : ℕ) : Finset ℕ :=
  (Finset.Icc (N + r + 1) (N + 2 * r)).filter (fun D => Nat.Coprime D r)

theorem mem_winSet {N r D : ℕ} :
    D ∈ winSet N r ↔ N + r + 1 ≤ D ∧ D ≤ N + 2 * r ∧ Nat.Coprime D r := by
  unfold winSet
  rw [Finset.mem_filter, Finset.mem_Icc]
  tauto

/-- (i) `|W| = φ(r)`. -/
theorem winSet_card (N r : ℕ) : (winSet N r).card = Nat.totient r := by
  have h := Nat.filter_coprime_Ico_eq_totient r (N + r + 1)
  rw [← h]
  have hI : Finset.Icc (N + r + 1) (N + 2 * r) = Finset.Ico (N + r + 1) (N + r + 1 + r) := by
    ext x
    simp only [Finset.mem_Icc, Finset.mem_Ico]
    omega
  unfold winSet
  rw [hI]
  congr 1
  exact Finset.filter_congr (fun x _ => Nat.coprime_comm)

/-- The entries of `v` exceeding `N`, as a `Finset ℤ`. -/
def outEntries {k : ℕ} (N : ℕ) (v : Fin (k + 1) → ℤ) : Finset ℤ :=
  (Finset.univ.image v).filter (fun z : ℤ => (N : ℤ) < z)

/-- For `IsV N r v` the entries above `N` are exactly the elements of `W`. -/
theorem isV_out_eq {N r k : ℕ} (v : Fin (k + 1) → ℤ) (hV : IsV N r v) :
    outEntries N v = (winSet N r).image (fun D : ℕ => (D : ℤ)) := by
  ext z
  unfold outEntries
  simp only [Finset.mem_filter, Finset.mem_image, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨⟨i, rfl⟩, hz⟩
    rcases hV.sub i with ⟨_, h2, _⟩ | ⟨w, hw, h1, h2, h3⟩
    · exact absurd hz (not_lt.mpr h2)
    · exact ⟨w, mem_winSet.mpr ⟨h1, h2, h3⟩, hw.symm⟩
  · rintro ⟨D, hD, rfl⟩
    obtain ⟨h1, h2, h3⟩ := mem_winSet.mp hD
    obtain ⟨i, hi⟩ := hV.cov D (Or.inr ⟨h1, h2, h3⟩)
    refine ⟨⟨i, hi⟩, ?_⟩
    have : ((N + r + 1 : ℕ) : ℤ) ≤ (D : ℤ) := by exact_mod_cast h1
    push_cast at this
    have hr : (0 : ℤ) ≤ r := by positivity
    omega

/-- `|V \ [N]| = φ(r)`: the number of distinct entries above `N` is `φ(r)`. -/
theorem isV_out_card {N r k : ℕ} (v : Fin (k + 1) → ℤ) (hV : IsV N r v) :
    (outEntries N v).card = Nat.totient r := by
  rw [isV_out_eq v hV, Finset.card_image_of_injective _ Nat.cast_injective, winSet_card]

/-- The runner `r` is not an entry of `v`. -/
theorem isV_ne_r {N r k : ℕ} (v : Fin (k + 1) → ℤ) (hV : IsV N r v) (i : Fin (k + 1)) :
    v i ≠ (r : ℤ) := by
  rcases hV.sub i with ⟨_, _, h3⟩ | ⟨w, hw, h1, _, _⟩
  · exact h3
  · intro h
    rw [hw] at h
    have : w = r := by exact_mod_cast h
    omega

/-- Existence of the family: for `2 ≤ r` and `2 r ≤ N` there is a vector with `IsV N r v`. -/
theorem exists_isV {N r : ℕ} (hr2 : 2 ≤ r) (hN : 2 * r ≤ N) :
    ∃ (m : ℕ) (v : Fin (m + 1) → ℤ), IsV N r v := by
  obtain ⟨S, hSmem⟩ : ∃ S : Finset ℕ, ∀ x, x ∈ S ↔
      ((1 ≤ x ∧ x ≤ N ∧ x ≠ r) ∨ (N + r + 1 ≤ x ∧ x ≤ N + 2 * r ∧ Nat.Coprime x r)) := by
    refine ⟨(Finset.Icc 1 N).erase r ∪ winSet N r, fun x => ?_⟩
    rw [Finset.mem_union, Finset.mem_erase, Finset.mem_Icc, mem_winSet]
    tauto
  have h1 : 1 ∈ S := (hSmem 1).mpr (Or.inl ⟨le_rfl, by omega, by omega⟩)
  have hpos : 0 < S.card := Finset.card_pos.mpr ⟨1, h1⟩
  obtain ⟨m, hm⟩ : ∃ m, S.card = m + 1 := ⟨S.card - 1, by omega⟩
  refine ⟨m, fun i => ((S.orderEmbOfFin hm i : ℕ) : ℤ), ?_, ?_⟩
  · intro i
    have hmem := (hSmem _).mp (Finset.orderEmbOfFin_mem S hm i)
    rcases hmem with ⟨hlo, hhi, hne⟩ | ⟨a, b, c⟩
    · left
      refine ⟨by exact_mod_cast hlo, by exact_mod_cast hhi, ?_⟩
      intro h
      exact hne (by exact_mod_cast h)
    · right
      exact ⟨_, rfl, a, b, c⟩
  · intro x hx
    have hxS : x ∈ S := (hSmem x).mpr hx
    have hrange := Finset.range_orderEmbOfFin S hm
    have : x ∈ Set.range (S.orderEmbOfFin hm) := by
      rw [hrange]; exact_mod_cast hxS
    obtain ⟨i, hi⟩ := this
    exact ⟨i, by simp [hi]⟩

end Gap
end Sext6
end LRSpectrumFull
