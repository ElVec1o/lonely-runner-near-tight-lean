/-
# Gen/TwoDir: the two-direction bound for any number of speeds  

Generalises `Sext6.LRC5_collision` and `Sext6.two_dir` (T2Core) from `Fin 6` / `LRC 5` to `Fin (k+1)` / `LRC k`
(`k >= 1`; `Sext6.LRC k` = k distinct positive speeds have `ML >= 1/(k+1)`).
* `LRC_collision_gen` : `LRC k` gives `ML u >= 1/(k+1)` for `k+1` nonzero speeds with two equal absolute values.
* `two_dir_gen`       : `1/(k+1) - delta/2 <= ML v` when `w` is a `delta`-rounding of `t v`, not parallel to `v`.
* `two_dir_six'`      : sanity corollary, the `k = 5` instance restated as T2Core's `two_dir`.
Reuses `coalesce`, `ML_transfer`, `ML_le_of_range` of T2Core (already generic).  Proof = T2Core's with 6 -> k+1,
5 -> k, padding interval `Icc (M+1) (M+k)`.
-/
import LRSpectrumFull.Sext6.T2Core

namespace LRSpectrumFull
namespace Sext6

theorem LRC_collision_gen (k : ℕ) (hk : 1 ≤ k) (hL : Sext6.LRC k) (u : Fin (k + 1) → ℤ)
    (hne : ∀ i, u i ≠ 0) (a b : Fin (k + 1)) (hab : a ≠ b) (habs : |u a| = |u b|) :
    (1 : ℝ) / ((k : ℝ) + 1) ≤ ML u := by
  classical
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  set S : Finset ℤ := Finset.univ.image (fun i => |u i|) with hS
  have hSpos : ∀ s ∈ S, 0 < s := by
    intro s hs
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.1 hs
    exact abs_pos.2 (hne i)
  have hScard : S.card ≤ j + 1 := by
    have hle : S.card ≤ j + 1 + 1 := by
      have := Finset.card_image_le (s := (Finset.univ : Finset (Fin (j + 1 + 1)))) (f := fun i => |u i|)
      simpa using this
    have hne' : S.card ≠ j + 1 + 1 := by
      intro h6
      have hinj : Set.InjOn (fun i => |u i|) (↑(Finset.univ : Finset (Fin (j + 1 + 1)))) := by
        rw [← Finset.card_image_iff]; simpa using h6
      exact hab (hinj (Finset.mem_coe.2 (Finset.mem_univ a)) (Finset.mem_coe.2 (Finset.mem_univ b)) habs)
    omega
  set M : ℤ := ∑ s ∈ S, s with hM
  have hM0 : 0 ≤ M := Finset.sum_nonneg (fun s hs => (hSpos s hs).le)
  have hsM : ∀ s ∈ S, s ≤ M := fun s hs =>
    Finset.single_le_sum (f := fun s : ℤ => s) (fun s hs => (hSpos s hs).le) hs
  set T : Finset ℤ := S ∪ Finset.Icc (M + 1) (M + ((j + 1 : ℕ) : ℤ)) with hT
  have hTcard : j + 1 ≤ T.card := by
    have h1 : (Finset.Icc (M + 1) (M + ((j + 1 : ℕ) : ℤ))).card = j + 1 := by
      rw [Int.card_Icc]; omega
    calc j + 1 = (Finset.Icc (M + 1) (M + ((j + 1 : ℕ) : ℤ))).card := h1.symm
      _ ≤ T.card := Finset.card_le_card Finset.subset_union_right
  obtain ⟨U, hSU, hUT, hUcard⟩ := Finset.exists_subsuperset_card_eq
    (Finset.subset_union_left : S ⊆ T) hScard hTcard
  have hUpos : ∀ s ∈ U, 0 < s := by
    intro s hs
    rcases Finset.mem_union.1 (hUT hs) with h | h
    · exact hSpos s h
    · have := (Finset.mem_Icc.1 h).1; omega
  set y : Fin (j + 1) → ℤ := fun i => U.orderEmbOfFin hUcard i with hy
  have hyinj : Function.Injective y := (U.orderEmbOfFin hUcard).injective
  have hypos : ∀ i, 0 < y i := fun i => hUpos _ (Finset.orderEmbOfFin_mem U hUcard i)
  have h6 := hL j rfl y hyinj hypos
  have hrange : ∀ i, ∃ jj, |u i| = y jj := by
    intro i
    have : |u i| ∈ Set.range (U.orderEmbOfFin hUcard) := by
      rw [Finset.range_orderEmbOfFin]
      exact hSU (Finset.mem_image.2 ⟨i, Finset.mem_univ _, rfl⟩)
    obtain ⟨jj, hj⟩ := this
    exact ⟨jj, hj.symm⟩
  have hle := ML_le_of_range y u hrange
  linarith

/-- **Two-direction bound, general.**  `LRC k` (k distinct positive speeds have `ML >= 1/(k+1)`) and a
`delta`-rounding `w` of `t v`, not parallel to `v`, give `ML v >= 1/(k+1) - delta/2` for `v : Fin (k+1) -> Z`. -/
theorem two_dir_gen (k : ℕ) (hk : 1 ≤ k) (hL : Sext6.LRC k) (v w : Fin (k + 1) → ℤ)
    (hv : ∀ i, v i ≠ 0) (t δ : ℝ) (he : ∀ i, |(w i : ℝ) - t * v i| ≤ δ)
    (hnp : ∃ i j, v i * w j - v j * w i ≠ 0) :
    (1 : ℝ) / ((k : ℝ) + 1) - δ / 2 ≤ ML v := by
  obtain ⟨α, β, a, b, hab, hne, habs⟩ := coalesce v w hv hnp
  have h1 := LRC_collision_gen k hk hL (fun i => α * v i + β * w i) hne a b hab habs
  have h2 := ML_transfer v w α β t δ he
  linarith

/-- Sanity: the `k = 5` instance is T2Core's `two_dir`. -/
theorem two_dir_six' (h5 : Sext6.LRC 5) (v w : Fin 6 → ℤ) (hv : ∀ k, v k ≠ 0) (t δ : ℝ)
    (he : ∀ i, |(w i : ℝ) - t * v i| ≤ δ) (hnp : ∃ i j, v i * w j - v j * w i ≠ 0) :
    (1 : ℝ) / 6 - δ / 2 ≤ ML v := by
  have h := two_dir_gen 5 (by norm_num) h5 v w hv t δ he hnp
  have e : ((5 : ℕ) : ℝ) + 1 = 6 := by norm_num
  rwa [e] at h

end Sext6
end LRSpectrumFull

#print axioms LRSpectrumFull.Sext6.LRC_collision_gen
#print axioms LRSpectrumFull.Sext6.two_dir_gen
#print axioms LRSpectrumFull.Sext6.two_dir_six'
