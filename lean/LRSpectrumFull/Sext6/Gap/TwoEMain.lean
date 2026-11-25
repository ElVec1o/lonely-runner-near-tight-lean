import LRSpectrumFull.Sext6.Gap.TwoEUpper

/-!
# Two-entry sandwich, part 3: `E := sSup (ArcSet ..)` and the statements of Theorem E  [2026-11-25]

Let `V` be a speed vector whose entries are exactly the retained speeds `[1,N] \ {r1,r2}` and the inserted
speeds `w1, w2`, with `N/2 < r1, r2 ≤ N` and `gcd(r1,r2) > 1`.  Put `A = N+1` and
`E = sSup (ArcSet N r1 r2 w1 w2)` (the supremum of the finite one-variable problem; no candidate list is used).

* `two_entry_sandwich` : `E ≤ ML V ≤ max (1/A) E`.  (No hypothesis on `w1, w2` beyond membership in `V`.)
* `two_entry_eq`       : if `A ∤ w1` and `A ∤ w2` then `ML V = max (1/A) E`.
* `two_entry_eq_of_floor` : if `1/A ≤ ML V` then `ML V = max (1/A) E` (this is the whole content when `A ∣ w_j`;
  `1/A ≤ ML V` is the Lonely Runner inequality for `V`, NOT proved here; no iff is stated).
* `two_entry_eq_of_E_ge`  : if `1/A ≤ E` then `ML V = E`.
* `two_entry_lt_iff`   : for `θ > 1/A` and `A ∤ w1, w2`: `ML V < θ ↔ E < θ`  (the exception criterion, `θ = 1/N`).
No `sorry`, no `axiom`.

Convention: `N` is the size of the ambient interval `[1,N]`; the speed vector `v : Fin (k+1) → ℤ` is a finite family (repetitions allowed). Speeds are the moving runners; the runner at rest is not counted, so a vector of `N` speeds means `N + 1` runners and the Lonely Runner value is `1/(N+1)`.
Axiom audit: covered by `Axioms23`.
-/

namespace LRSpectrumFull
namespace Sext6
namespace Gap

theorem arcSet_nonempty {N r1 r2 w1 w2 : ℕ} (hN : 2 ≤ N) (h1 : N < 2 * r1) (h1' : r1 ≤ N) :
    (ArcSet N r1 r2 w1 w2).Nonempty := by
  have hr : 0 < r1 := by omega
  obtain ⟨X, hX1, hX2, hXd⟩ := exists_block r1 ((N : ℤ) + 1 - r1) hr 1 isCoprime_one_left
  refine ⟨arcVal r1 w1 w2 1 X 0, ?_⟩
  simp only [ArcSet, Set.mem_setOf_eq]
  exact ⟨r1, Or.inl rfl, 1, X, 0, isCoprime_one_left, ⟨hX1, by omega, hXd⟩, le_refl _,
    by positivity, rfl⟩

theorem arcSet_bdd (N r1 r2 w1 w2 : ℕ) : BddAbove (ArcSet N r1 r2 w1 w2) := by
  refine ⟨1 / 2, ?_⟩
  rintro y ⟨r, -, c, X, η, -, -, -, -, rfl⟩
  unfold arcVal
  exact ((min_le_right _ _).trans (min_le_left _ _)).trans (nearestIntDist_le_half _)

theorem two_entry_sandwich {k N r1 r2 w1 w2 : ℕ} (hN : 2 ≤ N)
    (h1 : N < 2 * r1) (h1' : r1 ≤ N) (h2 : N < 2 * r2) (h2' : r2 ≤ N)
    (hg : ¬ Nat.Coprime r1 r2) (v : Fin (k + 1) → ℤ)
    (hwith : Within2 N r1 r2 w1 w2 v)
    (hret : ∀ x : ℕ, 1 ≤ x → x ≤ N → x ≠ r1 → x ≠ r2 → ∃ i, v i = (x : ℤ))
    (hw1 : ∃ i, v i = (w1 : ℤ)) (hw2 : ∃ i, v i = (w2 : ℤ)) :
    sSup (ArcSet N r1 r2 w1 w2) ≤ ML v ∧
      ML v ≤ max (1 / ((N : ℝ) + 1)) (sSup (ArcSet N r1 r2 w1 w2)) :=
  ⟨csSup_le (arcSet_nonempty hN h1 h1') (fun y hy => arcVal_le_ML hN h1 h1' h2 h2' v hwith hy),
   two_entry_upper hN h1 h1' h2 h2' hg v hret hw1 hw2 _
     (fun y hy => le_csSup (arcSet_bdd N r1 r2 w1 w2) hy)⟩

theorem two_entry_eq_of_floor {k N r1 r2 w1 w2 : ℕ} (hN : 2 ≤ N)
    (h1 : N < 2 * r1) (h1' : r1 ≤ N) (h2 : N < 2 * r2) (h2' : r2 ≤ N)
    (hg : ¬ Nat.Coprime r1 r2) (v : Fin (k + 1) → ℤ)
    (hwith : Within2 N r1 r2 w1 w2 v)
    (hret : ∀ x : ℕ, 1 ≤ x → x ≤ N → x ≠ r1 → x ≠ r2 → ∃ i, v i = (x : ℤ))
    (hw1 : ∃ i, v i = (w1 : ℤ)) (hw2 : ∃ i, v i = (w2 : ℤ))
    (hfl : 1 / ((N : ℝ) + 1) ≤ ML v) :
    ML v = max (1 / ((N : ℝ) + 1)) (sSup (ArcSet N r1 r2 w1 w2)) := by
  obtain ⟨hlo, hup⟩ := two_entry_sandwich hN h1 h1' h2 h2' hg v hwith hret hw1 hw2
  exact le_antisymm hup (max_le hfl hlo)

theorem two_entry_eq {k N r1 r2 w1 w2 : ℕ} (hN : 2 ≤ N)
    (h1 : N < 2 * r1) (h1' : r1 ≤ N) (h2 : N < 2 * r2) (h2' : r2 ≤ N)
    (hg : ¬ Nat.Coprime r1 r2) (v : Fin (k + 1) → ℤ)
    (hwith : Within2 N r1 r2 w1 w2 v)
    (hret : ∀ x : ℕ, 1 ≤ x → x ≤ N → x ≠ r1 → x ≠ r2 → ∃ i, v i = (x : ℤ))
    (hw1 : ∃ i, v i = (w1 : ℤ)) (hw2 : ∃ i, v i = (w2 : ℤ))
    (hd1 : ¬ (((N + 1 : ℕ) : ℤ) ∣ ((w1 : ℕ) : ℤ)))
    (hd2 : ¬ (((N + 1 : ℕ) : ℤ) ∣ ((w2 : ℕ) : ℤ))) :
    ML v = max (1 / ((N : ℝ) + 1)) (sSup (ArcSet N r1 r2 w1 w2)) :=
  two_entry_eq_of_floor hN h1 h1' h2 h2' hg v hwith hret hw1 hw2
    (ML_ge_floor2 (by omega) v hwith hd1 hd2)

theorem two_entry_eq_of_E_ge {k N r1 r2 w1 w2 : ℕ} (hN : 2 ≤ N)
    (h1 : N < 2 * r1) (h1' : r1 ≤ N) (h2 : N < 2 * r2) (h2' : r2 ≤ N)
    (hg : ¬ Nat.Coprime r1 r2) (v : Fin (k + 1) → ℤ)
    (hwith : Within2 N r1 r2 w1 w2 v)
    (hret : ∀ x : ℕ, 1 ≤ x → x ≤ N → x ≠ r1 → x ≠ r2 → ∃ i, v i = (x : ℤ))
    (hw1 : ∃ i, v i = (w1 : ℤ)) (hw2 : ∃ i, v i = (w2 : ℤ))
    (hE : 1 / ((N : ℝ) + 1) ≤ sSup (ArcSet N r1 r2 w1 w2)) :
    ML v = sSup (ArcSet N r1 r2 w1 w2) := by
  obtain ⟨hlo, hup⟩ := two_entry_sandwich hN h1 h1' h2 h2' hg v hwith hret hw1 hw2
  rw [max_eq_right hE] at hup
  exact le_antisymm hup hlo

theorem two_entry_lt_iff {k N r1 r2 w1 w2 : ℕ} (hN : 2 ≤ N)
    (h1 : N < 2 * r1) (h1' : r1 ≤ N) (h2 : N < 2 * r2) (h2' : r2 ≤ N)
    (hg : ¬ Nat.Coprime r1 r2) (v : Fin (k + 1) → ℤ)
    (hwith : Within2 N r1 r2 w1 w2 v)
    (hret : ∀ x : ℕ, 1 ≤ x → x ≤ N → x ≠ r1 → x ≠ r2 → ∃ i, v i = (x : ℤ))
    (hw1 : ∃ i, v i = (w1 : ℤ)) (hw2 : ∃ i, v i = (w2 : ℤ))
    (hd1 : ¬ (((N + 1 : ℕ) : ℤ) ∣ ((w1 : ℕ) : ℤ)))
    (hd2 : ¬ (((N + 1 : ℕ) : ℤ) ∣ ((w2 : ℕ) : ℤ)))
    (θ : ℝ) (hθ : 1 / ((N : ℝ) + 1) < θ) :
    ML v < θ ↔ sSup (ArcSet N r1 r2 w1 w2) < θ := by
  rw [two_entry_eq hN h1 h1' h2 h2' hg v hwith hret hw1 hw2 hd1 hd2, max_lt_iff]
  exact ⟨fun h => h.2, fun h => ⟨hθ, h⟩⟩

end Gap
end Sext6
end LRSpectrumFull
