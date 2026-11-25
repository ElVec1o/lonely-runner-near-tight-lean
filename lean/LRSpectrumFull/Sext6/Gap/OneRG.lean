import LRSpectrumFull.Sext6.Gap.OneRL2
import LRSpectrumFull.Sext6.Gap.InsLower

/-!
# One-entry deletion `B = [N] \ {r}`, part 6: Proposition G (every integer `w ≥ 4 N`)  [2026-11-25]

Source: the accompanying notes on the one-entry deletion (Plan 3), Proposition G.

`D` is the least integer `≥ N+1+r` coprime to `r`; `X0 = D - 2r` (the speed that is the minus runner at the equality
times `K/D`, `r K ≡ 1 (mod D)`), `2r` is the plus runner.
* `prop_G_core` : for every speed vector `v` with speed set `[N] \ {r}` and every integer `w ≥ 4 N`,
                  `2 w / (D w + 4 r X0) ≤ ML (v, w)`.
                  Proof: the one-sided crossing lemmas `peak_right_lower`, `peak_left_lower` at the equality time
                  `K/D` (slopes `X0` to the right and `2r` to the left; all other runners are at distance `≥ 3/D`),
                  and the algebraic fact that one of the two bounds is `≥ τ = 2 w / (D w + 4 r X0)`, whatever the
                  fractional part `th` of `w K / D` is.  The size hypothesis of the crossing lemmas, `N D (L - th) ≤ w`,
                  holds for `w ≥ 4 N` because `|th| < L = 2/D`.
* `prop_G`      : the same for `ML ([N]_{r → w})` (`wFam`), together with the upper bound `ML ≤ 2/D`
                  (adding an entry never raises `ML`, and `ML ([N] \ {r}) = 2/D`).
The threshold is `4 N` (the notes claim `w_G ≤ 3 N`, obtained there from the exact arc profile; this module does not
formalise the arc profile).  The closed form `2 w / (D w + 4 r X0)` equals `L w h / (w h + 2)` with `L = 2/D`,
`h = 1/(2r) + 1/X0` (see `OneRGh`).
No `sorry`, no `axiom`.

Convention: `N` is the size of the ambient interval `[N]` (`DSpec N r D`, `IsB N r v`): the deletion of `r` leaves `N - 1` distinct speeds, and `k` is not linked to `N` in the `IsB` statements (repetitions and any order are allowed). `bFam k r` lists `[N] \ {r}` and has `k + 1 = N - 1` entries when `N = k + 2`; `wFam (k+1) r w` has `k + 2 = N` entries. Speeds are the moving runners; the runner at rest is not counted, so a vector of `N` speeds means `N + 1` runners and the Lonely Runner value is `1/(N+1)`.
Hypotheses: those of the individual statements. The unproved predicates `DusartPi`, `LRCHyp`, `CopWinHyp` are not hypotheses of any statement in this module.
Axiom audit: covered by `Axioms21`.
-/

namespace LRSpectrumFull
namespace Sext6
namespace Gap

theorem prop_G_core {k N r D : ℕ} (hS : DSpec N r D) (v : Fin (k + 1) → ℤ) (hB : IsB N r v)
    (w : ℤ) (hw0 : 0 < w) (hw : 4 * (N : ℤ) ≤ w) :
    2 * (w : ℝ) / ((D : ℝ) * (w : ℝ) + 4 * (r : ℝ) * ((D : ℝ) - 2 * (r : ℝ))) ≤
      ML (Fin.snoc v w : Fin (k + 2) → ℤ) := by
  have hr := hS.hr
  have hN2 := hS.hN
  have hN3 := hS.hN3
  have hD1 := hS.hD1
  have hv : ∀ i, 0 < v i := fun i => by have := (hB.sub i).1; omega
  have hM : ∀ i, v i ≤ (N : ℤ) := fun i => (hB.sub i).2.1
  have hDpos : (0 : ℝ) < D := by exact_mod_cast (by omega : 0 < D)
  have hDne : (D : ℝ) ≠ 0 := hDpos.ne'
  have hrpos : (0 : ℝ) < r := by exact_mod_cast (by omega : 0 < r)
  have hlam : (0 : ℝ) < (D : ℝ) - 2 * r := by
    have h1 : 2 * r < D := by omega
    have h' : ((2 * r : ℕ) : ℝ) < D := by exact_mod_cast h1
    push_cast at h'
    linarith
  have hL0 : (0 : ℝ) < 2 / (D : ℝ) := div_pos (by norm_num) hDpos
  have hL1 : 2 / (D : ℝ) < 1 / 2 := by
    rw [div_lt_div_iff₀ hDpos (by norm_num)]
    have : (4 : ℝ) < D := by exact_mod_cast (by omega : 4 < D)
    linarith
  obtain ⟨K, hK⟩ := exists_inv_r hS
  have hfar : ∀ i, 2 / (D : ℝ) ≤ nearestIntDist ((v i : ℝ) * ((K : ℝ) / D)) := by
    intro i
    obtain ⟨h1, h2, h3⟩ := hB.sub i
    exact far_at_inv hS K hK (v i) h1 h2 h3
  have hextm : ∀ i (m : ℤ), (v i : ℝ) * ((K : ℝ) / D) = m - 2 / (D : ℝ) →
      (v i : ℝ) ≤ (D : ℝ) - 2 * r := by
    intro i m hm
    have h1 := (mul_minus_iff hDne).mp hm
    have h2 : v i * K = m * D - 2 := by exact_mod_cast h1
    obtain ⟨hx1, hxN, _⟩ := hB.sub i
    have h3 := minus_runner_eq hS K hK (v i) m hx1 hxN h2
    have h4 : (v i : ℝ) = (D : ℝ) - 2 * r := by exact_mod_cast h3
    exact h4.le
  have hextp : ∀ i (n : ℤ), (v i : ℝ) * ((K : ℝ) / D) = n + 2 / (D : ℝ) →
      (v i : ℝ) ≤ 2 * r := by
    intro i n hn
    have h1 := (mul_plus_iff hDne).mp hn
    have h2 : v i * K = n * D + 2 := by exact_mod_cast h1
    obtain ⟨hx1, hxN, _⟩ := hB.sub i
    have h3 := plus_runner_eq hS K hK (v i) n hx1 hxN h2
    have h4 : (v i : ℝ) = 2 * r := by exact_mod_cast h3
    exact h4.le
  have hwR : (0 : ℝ) < (w : ℝ) := by exact_mod_cast hw0
  obtain ⟨z, hz⟩ : ∃ z : ℤ, z = round ((w : ℝ) * ((K : ℝ) / D)) := ⟨_, rfl⟩
  obtain ⟨th, hth⟩ : ∃ th : ℝ, th = (w : ℝ) * ((K : ℝ) / D) - z := ⟨_, rfl⟩
  have hthabs : |th| ≤ 1 / 2 := by rw [hth, hz]; exact abs_sub_round _
  have hwt : (w : ℝ) * ((K : ℝ) / D) = th + z := by rw [hth]; ring
  have hden : (0 : ℝ) < (D : ℝ) * w + 4 * r * ((D : ℝ) - 2 * r) := by
    have h1 : 0 < 4 * (r : ℝ) * ((D : ℝ) - 2 * r) := mul_pos (by linarith) hlam
    have h2 : 0 < (D : ℝ) * w := mul_pos hDpos hwR
    linarith
  have hdenne : (D : ℝ) * w + 4 * r * ((D : ℝ) - 2 * r) ≠ 0 := hden.ne'
  obtain ⟨τ, hτ⟩ : ∃ τ : ℝ, τ = 2 * (w : ℝ) / ((D : ℝ) * w + 4 * r * ((D : ℝ) - 2 * r)) :=
    ⟨_, rfl⟩
  rw [← hτ]
  have hτe : τ * ((D : ℝ) * w + 4 * r * ((D : ℝ) - 2 * r)) = 2 * w := by
    rw [hτ]; field_simp
  have hLD : (2 / (D : ℝ)) * (D : ℝ) = 2 := by field_simp
  by_cases hc : 2 / (D : ℝ) ≤ |th|
  · have hML : 2 / (D : ℝ) ≤ ML (Fin.snoc v w : Fin (k + 2) → ℤ) := by
      apply ML_ge_of_far (Fin.snoc v w : Fin (k + 2) → ℤ) (2 / (D : ℝ)) ((K : ℝ) / D)
      intro u
      rcases Fin.eq_castSucc_or_eq_last u with ⟨j', rfl⟩ | rfl
      · rw [snoc_castSucc_eq]
        exact hfar j'
      · rw [snoc_last_eq, hwt, nearestIntDist_add_int, nid_eq_abs' hthabs]
        exact hc
    refine le_trans ?_ hML
    rw [hτ, div_le_div_iff₀ hden hDpos]
    nlinarith [mul_pos hrpos hlam]
  · have hc' := not_le.mp hc
    obtain ⟨hthl1, hthl2⟩ := abs_lt.mp hc'
    have hNc : ((N : ℤ) : ℝ) = (N : ℝ) := by norm_cast
    have h4N : (4 : ℝ) * (N : ℝ) ≤ (w : ℝ) := by
      have : (4 : ℝ) * ((N : ℤ) : ℝ) ≤ (w : ℝ) := by exact_mod_cast hw
      rw [hNc] at this
      exact this
    have hsz : ∀ x : ℝ, -(2 / (D : ℝ)) < x →
        ((N : ℤ) : ℝ) * (D : ℝ) * (2 / (D : ℝ) - x) ≤ (w : ℝ) := by
      intro x hx
      have h1 : (D : ℝ) * (-(2 / (D : ℝ))) < D * x := mul_lt_mul_of_pos_left hx hDpos
      have h2 : (D : ℝ) * (2 / (D : ℝ) - x) ≤ 4 := by nlinarith [hLD, h1]
      have hN0 : (0 : ℝ) ≤ ((N : ℤ) : ℝ) := by positivity
      calc ((N : ℤ) : ℝ) * (D : ℝ) * (2 / (D : ℝ) - x)
          = ((N : ℤ) : ℝ) * ((D : ℝ) * (2 / (D : ℝ) - x)) := by ring
        _ ≤ ((N : ℤ) : ℝ) * 4 := mul_le_mul_of_nonneg_left h2 hN0
        _ ≤ (w : ℝ) := by rw [hNc]; linarith
    have hA := peak_right_lower v hv (N : ℤ) hM w hw0 (2 / (D : ℝ)) ((D : ℝ) - 2 * r) D
      (by omega) K 2 th z (by simp) hL0 hL1 hlam hfar hextm hwt hthl2.le
      (by linarith [hsz th hthl1])
    have hB' := peak_left_lower v hv (N : ℤ) hM w hw0 (2 / (D : ℝ)) (2 * r) D
      (by omega) K 2 th z (by simp) hL0 hL1 (by linarith) hfar hextp hwt (by linarith)
      (by linarith [hsz (-th) (by linarith)])
    have hcase : τ ≤ ((w : ℝ) * (2 / (D : ℝ)) + ((D : ℝ) - 2 * r) * th) /
          ((w : ℝ) + ((D : ℝ) - 2 * r)) ∨
        τ ≤ ((w : ℝ) * (2 / (D : ℝ)) + (2 * (r : ℝ)) * (-th)) / ((w : ℝ) + 2 * r) := by
      by_contra hcon
      have hcon' := not_or.mp hcon
      obtain ⟨h1n, h2n⟩ := hcon'
      have h1 := not_le.mp h1n
      have h2 := not_le.mp h2n
      have h1' := (div_lt_iff₀ (by linarith : (0 : ℝ) < (w : ℝ) + ((D : ℝ) - 2 * r))).mp h1
      have h2' := (div_lt_iff₀ (by linarith : (0 : ℝ) < (w : ℝ) + 2 * r)).mp h2
      have hp1 := mul_lt_mul_of_pos_left h1' (by linarith : (0 : ℝ) < 2 * (r : ℝ))
      have hp2 := mul_lt_mul_of_pos_left h2' hlam
      have hsum : 2 * (r : ℝ) * ((w : ℝ) * (2 / (D : ℝ)) + ((D : ℝ) - 2 * r) * th) +
          ((D : ℝ) - 2 * r) * ((w : ℝ) * (2 / (D : ℝ)) + (2 * (r : ℝ)) * (-th)) = 2 * w := by
        linear_combination (w : ℝ) * hLD
      have hrhs : 2 * (r : ℝ) * (τ * ((w : ℝ) + ((D : ℝ) - 2 * r))) +
          ((D : ℝ) - 2 * r) * (τ * ((w : ℝ) + 2 * r)) =
          τ * ((D : ℝ) * w + 4 * r * ((D : ℝ) - 2 * r)) := by ring
      linarith [hp1, hp2, hsum, hrhs, hτe]
    rcases hcase with h | h
    · exact le_trans h hA
    · exact le_trans h hB'

/-- **Proposition G** (for every integer `w ≥ 4 N`; the lower bound is `L w h/(w h + 2)` of the notes). -/
theorem prop_G {k N r D w : ℕ} (hk : k + 2 = N) (hS : DSpec N r D) (hw : 4 * N ≤ w) :
    2 * (w : ℝ) / ((D : ℝ) * (w : ℝ) + 4 * (r : ℝ) * ((D : ℝ) - 2 * (r : ℝ))) ≤
        ML (wFam (k + 1) r w) ∧
      ML (wFam (k + 1) r w) ≤ 2 / (D : ℝ) := by
  have hr := hS.hr
  have hN2 := hS.hN
  have hN3 := hS.hN3
  have hB := isB_bFam hk hr hN2
  rw [ML_wFam_eq_snoc hk hr hN2]
  constructor
  · have := prop_G_core hS (bFam k r) hB (w : ℤ) (by omega) (by omega)
    exact_mod_cast this
  · exact (ML_snoc_le_self _ _).trans (ML_bFam hk hS).le

end Gap
end Sext6
end LRSpectrumFull
