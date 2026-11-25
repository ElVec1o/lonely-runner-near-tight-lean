/-
# PairGrid: the 30-grid exclusion table for relative labelings (F2 pair-agreement, part 1).  [AK, 2026-11-24]
Assembles `PairTab1..6` (kernel decisions, one per value of c_1) into `pair_excl`; see `PairDefs.lean` for the
exact correspondence with `AJ_pairlift/gridlift.c` (D = 30).
-/
import LRSpectrumFull.Sext6.PairTab1
import LRSpectrumFull.Sext6.PairTab2
import LRSpectrumFull.Sext6.PairTab3
import LRSpectrumFull.Sext6.PairTab4
import LRSpectrumFull.Sext6.PairTab5
import LRSpectrumFull.Sext6.PairTab6

namespace LRSpectrumFull
namespace Sext6

theorem T1_true : T1 := by
  intro c1 h
  simp only [V6, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl
  exacts [T2_1, T2_2, T2_3, T2_4, T2_5, T2_6]

/-- **Core table.** Every non-identical signed permutation with first entry positive is excluded by a pool
witness.  Decided by the kernel; the nested premises prune the 12^6 tree to the 23,040 labelings. -/
theorem core_table :
    ∀ c1 ∈ V6, ∀ c2 ∈ V12, c2.natAbs ≠ c1.natAbs →
    ∀ c3 ∈ V12, c3.natAbs ≠ c1.natAbs → c3.natAbs ≠ c2.natAbs →
    ∀ c4 ∈ V12, c4.natAbs ≠ c1.natAbs → c4.natAbs ≠ c2.natAbs → c4.natAbs ≠ c3.natAbs →
    ∀ c5 ∈ V12, c5.natAbs ≠ c1.natAbs → c5.natAbs ≠ c2.natAbs → c5.natAbs ≠ c3.natAbs →
      c5.natAbs ≠ c4.natAbs →
    ∀ c6 ∈ V12, c6.natAbs ≠ c1.natAbs → c6.natAbs ≠ c2.natAbs → c6.natAbs ≠ c3.natAbs →
      c6.natAbs ≠ c4.natAbs → c6.natAbs ≠ c5.natAbs →
    ¬ (c1 = 1 ∧ c2 = 2 ∧ c3 = 3 ∧ c4 = 4 ∧ c5 = 5 ∧ c6 = 6) →
    ∃ w ∈ pool30, good6 w c1 c2 c3 c4 c5 c6 := T1_true

theorem mem_V12 (z : ℤ) (h1 : 1 ≤ z.natAbs) (h2 : z.natAbs ≤ 6) : z ∈ V12 := by
  simp only [V12, List.mem_cons, List.not_mem_nil, or_false]; omega

theorem mem_V6 (z : ℤ) (h1 : 1 ≤ z) (h2 : z ≤ 6) : z ∈ V6 := by
  simp only [V6, List.mem_cons, List.not_mem_nil, or_false]; omega

/-- **Pair exclusion (grid).** Every relative labeling `(sigma, eta)` (with `eta_1 = +1`) other than the
identical one has a 30-grid witness. -/
theorem pair_excl (σ : Equiv.Perm (Fin 6)) (η : Fin 6 → ℤ) (hη : ∀ m, η m = 1 ∨ η m = -1)
    (h0 : η 0 = 1) (hne : ∃ m : Fin 6, η m * (((σ m : ℕ) : ℤ) + 1) ≠ ((m : ℕ) : ℤ) + 1) :
    Excl30 (fun m => η m * (((σ m : ℕ) : ℤ) + 1)) := by
  set c : Fin 6 → ℤ := fun m => η m * (((σ m : ℕ) : ℤ) + 1) with hc
  have habs : ∀ m, (c m).natAbs = (σ m : ℕ) + 1 := by
    intro m
    rcases hη m with h | h <;> simp [hc, h] <;> omega
  have hlt : ∀ m, (σ m : ℕ) < 6 := fun m => (σ m).isLt
  have hmem : ∀ m, c m ∈ V12 := fun m => mem_V12 _ (by rw [habs]; omega) (by rw [habs]; have := hlt m; omega)
  have hne' : ∀ i j : Fin 6, i ≠ j → (c i).natAbs ≠ (c j).natAbs := by
    intro i j hij h
    rw [habs, habs] at h
    exact hij (σ.injective (Fin.ext (by omega)))
  have hc0 : c 0 ∈ V6 := by
    have : c 0 = ((σ 0 : ℕ) : ℤ) + 1 := by simp [hc, h0]
    have := hlt 0
    exact mem_V6 _ (by omega) (by omega)
  have hnid : ¬ (c 0 = 1 ∧ c 1 = 2 ∧ c 2 = 3 ∧ c 3 = 4 ∧ c 4 = 5 ∧ c 5 = 6) := by
    rintro ⟨e0, e1, e2, e3, e4, e5⟩
    obtain ⟨m, hm⟩ := hne
    fin_cases m <;> simp_all [hc]
  obtain ⟨w, -, hw⟩ := core_table (c 0) hc0 (c 1) (hmem 1) (hne' 1 0 (by decide))
    (c 2) (hmem 2) (hne' 2 0 (by decide)) (hne' 2 1 (by decide))
    (c 3) (hmem 3) (hne' 3 0 (by decide)) (hne' 3 1 (by decide)) (hne' 3 2 (by decide))
    (c 4) (hmem 4) (hne' 4 0 (by decide)) (hne' 4 1 (by decide)) (hne' 4 2 (by decide))
      (hne' 4 3 (by decide))
    (c 5) (hmem 5) (hne' 5 0 (by decide)) (hne' 5 1 (by decide)) (hne' 5 2 (by decide))
      (hne' 5 3 (by decide)) (hne' 5 4 (by decide)) hnid
  obtain ⟨g1, g2, g3, g4, g5, g6⟩ := hw
  refine ⟨w.1, w.2, fun m => ?_⟩
  fin_cases m
  · simpa [slotGood] using g1
  · simpa [slotGood] using g2
  · simpa [slotGood] using g3
  · simpa [slotGood] using g4
  · simpa [slotGood] using g5
  · simpa [slotGood] using g6

/-- Reduction of the slot value to residues mod 30. -/
theorem bdist30_mod (x : ℤ) : bdist 30 (x % 30) = bdist 30 x := by
  unfold bdist
  have : x % 30 % 30 = x % 30 := Int.emod_emod_of_dvd x (dvd_refl _)
  simp [this]

theorem bdist30_congr (x y : ℤ) (h : x % 30 = y % 30) : bdist 30 x = bdist 30 y := by
  rw [← bdist30_mod x, ← bdist30_mod y, h]

/-- **Negative control.** The identical labeling `c_m = m` is NOT excluded: no grid point at all. -/
theorem identical_not_excl30 : ¬ Excl30 (fun m => ((m : ℕ) : ℤ) + 1) := by
  rintro ⟨a, b, h⟩
  have key : ∀ a' ∈ List.range 30, ∀ b' ∈ List.range 30,
      ∃ k ∈ [1, 2, 3, 4, 5, 6], ¬ slotGood (a' : ℤ) (b' : ℤ) k k := by decide +kernel
  have ha : a % 30 = (((a % 30).toNat : ℕ) : ℤ) := by
    have := Int.emod_nonneg a (by norm_num : (30 : ℤ) ≠ 0); omega
  have hb : b % 30 = (((b % 30).toNat : ℕ) : ℤ) := by
    have := Int.emod_nonneg b (by norm_num : (30 : ℤ) ≠ 0); omega
  have ha' : (a % 30).toNat ∈ List.range 30 := by
    have := Int.emod_lt_of_pos a (by norm_num : (0 : ℤ) < 30); simp [List.mem_range]; omega
  have hb' : (b % 30).toNat ∈ List.range 30 := by
    have := Int.emod_lt_of_pos b (by norm_num : (0 : ℤ) < 30); simp [List.mem_range]; omega
  obtain ⟨k, hk, hbad⟩ := key _ ha' _ hb'
  apply hbad
  rw [← ha, ← hb]
  have hk' : ∃ m : Fin 6, k = ((m : ℕ) : ℤ) + 1 := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl
    · exact ⟨0, by simp⟩
    · exact ⟨1, by simp⟩
    · exact ⟨2, by simp⟩
    · exact ⟨3, by simp⟩
    · exact ⟨4, by simp⟩
    · exact ⟨5, by simp⟩
  obtain ⟨m, rfl⟩ := hk'
  have hm := h m
  unfold slotGood
  have hmod : (((a % 30) * (((m : ℕ) : ℤ) + 1) + (b % 30) * (((m : ℕ) : ℤ) + 1)) % 30)
      = ((a * (((m : ℕ) : ℤ) + 1) + b * (((m : ℕ) : ℤ) + 1)) % 30) :=
    (((Int.mod_modEq a 30).mul_right _).add ((Int.mod_modEq b 30).mul_right _))
  rw [bdist30_congr _ _ hmod]
  simpa [add_mul] using hm

end Sext6
end LRSpectrumFull

#print axioms LRSpectrumFull.Sext6.core_table
#print axioms LRSpectrumFull.Sext6.pair_excl
