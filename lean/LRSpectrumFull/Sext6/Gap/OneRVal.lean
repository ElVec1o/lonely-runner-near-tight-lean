import LRSpectrumFull.Sext6.Gap.OneRArc

/-!
# One-entry deletion `B = [N] \ {r}`, part 3: runners at the equality times, `vμ`, and the exact one-entry value  [2026-11-25]

Source: the accompanying notes on the one-entry deletion, Lemma D (slopes and `vμ`), Theorem V1.

* `runners_at_eq` : at every equality time `p` (`gap v p = 2/D`) the runners at `+2/D` all have speed `a`,
                    those at `-2/D` all have speed `b`, `{a,b} = {2r, D-2r}`, and both sides are occupied.
* `V1_holds`, `V2_holds` : the hypotheses (V1), (V2) of `Kstar_E` hold with `vμ = min (2r) (D - 2r)`.
* `vmu_eq`        : any `vμ` satisfying (V1) and (V2) equals `min (2r) (D - 2r)`.
* `one_entry_value` : `N = k + 2`, `D ∣ w`, `w ≥ 2 N^3`:
                      `ML (wFam (k+1) r w) = 2 w / (D (w + min (2r) (D - 2r)))`.
No `sorry`, no `axiom`.

Convention: `N` is the size of the ambient interval `[N]` (`DSpec N r D`, `IsB N r v`): the deletion of `r` leaves `N - 1` distinct speeds, and `k` is not linked to `N` in the `IsB` statements (repetitions and any order are allowed). `bFam k r` lists `[N] \ {r}` and has `k + 1 = N - 1` entries when `N = k + 2`; `wFam (k+1) r w` has `k + 2 = N` entries (compare `OE_low_unconditional`, where `wFam k r w` has `k + 1 = N` entries). Speeds are the moving runners; the runner at rest is not counted, so a vector of `N` speeds means `N + 1` runners and the Lonely Runner value is `1/(N+1)`.
Hypotheses: those of the individual statements (numerical bounds, structural conditions and, where named in the list above, window predicates such as `PrimeWin`, `CopWin`, `PrimeWindow7`, which later modules discharge for explicit ranges). The unproved predicates `DusartPi`, `LRCHyp`, `CopWinHyp` are not hypotheses of any statement in this module.
Axiom audit: covered by `Axioms19` (`#print axioms`; declarations not printed there are bricks of printed ones, so their axioms are bounded by the printed lines).
-/

namespace LRSpectrumFull
namespace Sext6
namespace Gap

theorem mul_plus_iff {x K n D : ℝ} (hD : D ≠ 0) :
    x * (K / D) = n + 2 / D ↔ x * K = n * D + 2 := by
  constructor
  · intro h
    field_simp at h
    linarith
  · intro h
    field_simp
    linarith

theorem mul_minus_iff {x K m D : ℝ} (hD : D ≠ 0) :
    x * (K / D) = m - 2 / D ↔ x * K = m * D - 2 := by
  constructor
  · intro h
    field_simp at h
    linarith
  · intro h
    field_simp
    linarith

/-- At `K/D`, a speed `x ∈ [1,N]` at `+2/D` is `2r`. -/
theorem plus_runner_eq {N r D : ℕ} (hS : DSpec N r D) (K : ℤ) (hK : (D : ℤ) ∣ (r : ℤ) * K - 1)
    (x n : ℤ) (hx1 : 1 ≤ x) (hxN : x ≤ N) (h : x * K = n * D + 2) : x = 2 * r := by
  have hD1 := hS.hD1
  have hN2 := hS.hN
  have hr := hS.hr
  obtain ⟨s, hs⟩ := hK
  have hkey : x - 2 * (r : ℤ) = (D : ℤ) * (n * r - s * x) := by
    linear_combination (r : ℤ) * h + (-x) * hs
  have hd : (D : ℤ) ∣ x - 2 * r := ⟨n * r - s * x, hkey⟩
  have := Int.eq_zero_of_abs_lt_dvd hd (abs_lt.mpr ⟨by omega, by omega⟩)
  omega

/-- At `K/D`, a speed `x ∈ [1,N]` at `-2/D` is `D - 2r`. -/
theorem minus_runner_eq {N r D : ℕ} (hS : DSpec N r D) (K : ℤ) (hK : (D : ℤ) ∣ (r : ℤ) * K - 1)
    (x m : ℤ) (hx1 : 1 ≤ x) (hxN : x ≤ N) (h : x * K = m * D - 2) : x = (D : ℤ) - 2 * r := by
  have hD1 := hS.hD1
  have hN2 := hS.hN
  have hr := hS.hr
  obtain ⟨s, hs⟩ := hK
  have hkey : x + 2 * (r : ℤ) = (D : ℤ) * (m * r - s * x) := by
    linear_combination (r : ℤ) * h + (-x) * hs
  have hd : (D : ℤ) ∣ x + 2 * r - D := ⟨m * r - s * x - 1, by linear_combination hkey⟩
  have := Int.eq_zero_of_abs_lt_dvd hd (abs_lt.mpr ⟨by omega, by omega⟩)
  omega

theorem plus_exists {N r D : ℕ} (hS : DSpec N r D) (K : ℤ) (hK : (D : ℤ) ∣ (r : ℤ) * K - 1)
    (x : ℤ) (hx : x = 2 * r) : ∃ n : ℤ, (x : ℝ) * ((K : ℝ) / D) = n + 2 / D := by
  have hD1 := hS.hD1
  have hDne : (D : ℝ) ≠ 0 := by exact_mod_cast (by omega : D ≠ 0)
  obtain ⟨s, hs⟩ := hK
  refine ⟨2 * s, (mul_plus_iff hDne).mpr ?_⟩
  have h : x * K = 2 * s * D + 2 := by
    rw [hx]
    linear_combination 2 * hs
  exact_mod_cast h

theorem minus_exists {N r D : ℕ} (hS : DSpec N r D) (K : ℤ) (hK : (D : ℤ) ∣ (r : ℤ) * K - 1)
    (x : ℤ) (hx : x = (D : ℤ) - 2 * r) : ∃ m : ℤ, (x : ℝ) * ((K : ℝ) / D) = m - 2 / D := by
  have hD1 := hS.hD1
  have hDne : (D : ℝ) ≠ 0 := by exact_mod_cast (by omega : D ≠ 0)
  obtain ⟨s, hs⟩ := hK
  refine ⟨K - 2 * s, (mul_minus_iff hDne).mpr ?_⟩
  have h : x * K = (K - 2 * s) * D - 2 := by
    rw [hx]
    linear_combination (-2 : ℤ) * hs
  exact_mod_cast h

/-- **Lemma D.**  Runners at an equality time. -/
theorem runners_at_eq {k N r D : ℕ} (hS : DSpec N r D) (v : Fin (k + 1) → ℤ) (hB : IsB N r v)
    (p : ℝ) (hp : gap v p = 2 / (D : ℝ)) :
    ∃ a b : ℤ, ((a = 2 * r ∧ b = (D : ℤ) - 2 * r) ∨ (a = (D : ℤ) - 2 * r ∧ b = 2 * r)) ∧
      (∀ i, ∀ n : ℤ, (v i : ℝ) * p = n + 2 / D → v i = a) ∧
      (∀ i, ∀ m : ℤ, (v i : ℝ) * p = m - 2 / D → v i = b) ∧
      (∃ i, ∃ n : ℤ, (v i : ℝ) * p = n + 2 / D) ∧
      (∃ j, ∃ m : ℤ, (v j : ℝ) * p = m - 2 / D) := by
  have hD1 := hS.hD1
  have hN2 := hS.hN
  have hr := hS.hr
  have hw := hS.le_window
  have hDne : (D : ℝ) ≠ 0 := by exact_mod_cast (by omega : D ≠ 0)
  obtain ⟨K, hK, hpK⟩ := eqtime_classify hS v hB p hp
  obtain ⟨i2, hi2⟩ := hB.cov (2 * r) (by omega) hN2 (by omega)
  obtain ⟨iX, hiX⟩ := hB.cov (D - 2 * r) (by omega) (by omega) (by omega)
  have hi2' : v i2 = 2 * (r : ℤ) := by rw [hi2]; omega
  have hiX' : v iX = (D : ℤ) - 2 * r := by rw [hiX]; omega
  rcases hpK with h | h
  · subst h
    refine ⟨2 * r, (D : ℤ) - 2 * r, Or.inl ⟨rfl, rfl⟩, ?_, ?_, ?_, ?_⟩
    · intro i n hn
      have h1 := (mul_plus_iff hDne).mp hn
      have h2 : v i * K = n * D + 2 := by exact_mod_cast h1
      obtain ⟨hx1, hxN, _⟩ := hB.sub i
      exact plus_runner_eq hS K hK (v i) n hx1 hxN h2
    · intro i m hm
      have h1 := (mul_minus_iff hDne).mp hm
      have h2 : v i * K = m * D - 2 := by exact_mod_cast h1
      obtain ⟨hx1, hxN, _⟩ := hB.sub i
      exact minus_runner_eq hS K hK (v i) m hx1 hxN h2
    · obtain ⟨n, hn⟩ := plus_exists hS K hK (v i2) hi2'
      exact ⟨i2, n, hn⟩
    · obtain ⟨m, hm⟩ := minus_exists hS K hK (v iX) hiX'
      exact ⟨iX, m, hm⟩
  · subst h
    refine ⟨(D : ℤ) - 2 * r, 2 * r, Or.inr ⟨rfl, rfl⟩, ?_, ?_, ?_, ?_⟩
    · intro i n hn
      have hm : (v i : ℝ) * ((K : ℝ) / D) = ((-n : ℤ) : ℝ) - 2 / D := by
        have e : (v i : ℝ) * ((K : ℝ) / D) = -((v i : ℝ) * (-((K : ℝ) / D))) := by ring
        rw [e, hn]
        push_cast
        ring
      have h1 := (mul_minus_iff hDne).mp hm
      have h2 : v i * K = (-n) * D - 2 := by exact_mod_cast h1
      obtain ⟨hx1, hxN, _⟩ := hB.sub i
      exact minus_runner_eq hS K hK (v i) (-n) hx1 hxN h2
    · intro i m hm
      have hm' : (v i : ℝ) * ((K : ℝ) / D) = ((-m : ℤ) : ℝ) + 2 / D := by
        have e : (v i : ℝ) * ((K : ℝ) / D) = -((v i : ℝ) * (-((K : ℝ) / D))) := by ring
        rw [e, hm]
        push_cast
        ring
      have h1 := (mul_plus_iff hDne).mp hm'
      have h2 : v i * K = (-m) * D + 2 := by exact_mod_cast h1
      obtain ⟨hx1, hxN, _⟩ := hB.sub i
      exact plus_runner_eq hS K hK (v i) (-m) hx1 hxN h2
    · obtain ⟨m0, hm0⟩ := minus_exists hS K hK (v iX) hiX'
      refine ⟨iX, -m0, ?_⟩
      have e : (v iX : ℝ) * (-((K : ℝ) / D)) = -((v iX : ℝ) * ((K : ℝ) / D)) := by ring
      rw [e, hm0]
      push_cast
      ring
    · obtain ⟨n0, hn0⟩ := plus_exists hS K hK (v i2) hi2'
      refine ⟨i2, -n0, ?_⟩
      have e : (v i2 : ℝ) * (-((K : ℝ) / D)) = -((v i2 : ℝ) * ((K : ℝ) / D)) := by ring
      rw [e, hn0]
      push_cast
      ring

/-- (V1) with `vμ = min (2r) (D - 2r)`. -/
theorem V1_holds {k N r D : ℕ} (hS : DSpec N r D) (v : Fin (k + 1) → ℤ) (hB : IsB N r v)
    (p : ℝ) (hp : gap v p = 2 / (D : ℝ)) :
    (∃ i : Fin (k + 1), ∃ n : ℤ, ((min (2 * r) (D - 2 * r) : ℕ) : ℝ) ≤ (v i : ℝ) ∧
        (v i : ℝ) * p = n + 2 / D) ∧
    (∃ j : Fin (k + 1), ∃ m : ℤ, ((min (2 * r) (D - 2 * r) : ℕ) : ℝ) ≤ (v j : ℝ) ∧
        (v j : ℝ) * p = m - 2 / D) := by
  obtain ⟨a, b, hab, hplus, hminus, ⟨ip, np, hnp⟩, ⟨jm, mm, hmm⟩⟩ := runners_at_eq hS v hB p hp
  have ha := hplus ip np hnp
  have hb := hminus jm mm hmm
  have hD1 := hS.hD1
  have hN2 := hS.hN
  refine ⟨⟨ip, np, ?_, hnp⟩, ⟨jm, mm, ?_, hmm⟩⟩
  · have : ((min (2 * r) (D - 2 * r) : ℕ) : ℤ) ≤ v ip := by
      rw [ha]
      rcases le_total (2 * r) (D - 2 * r) with h2 | h2
      · rw [min_eq_left h2]; omega
      · rw [min_eq_right h2]; omega
    exact_mod_cast this
  · have : ((min (2 * r) (D - 2 * r) : ℕ) : ℤ) ≤ v jm := by
      rw [hb]
      rcases le_total (2 * r) (D - 2 * r) with h2 | h2
      · rw [min_eq_left h2]; omega
      · rw [min_eq_right h2]; omega
    exact_mod_cast this

/-- (V2) with `vμ = min (2r) (D - 2r)`. -/
theorem V2_holds {k N r D : ℕ} (hS : DSpec N r D) (v : Fin (k + 1) → ℤ) (hB : IsB N r v) :
    ∃ t0 : ℝ, gap v t0 = 2 / (D : ℝ) ∧
      ((∀ i (m : ℤ), (v i : ℝ) * t0 = m - 2 / D →
          (v i : ℝ) ≤ ((min (2 * r) (D - 2 * r) : ℕ) : ℝ)) ∨
       (∀ i (n : ℤ), (v i : ℝ) * t0 = n + 2 / D →
          (v i : ℝ) ≤ ((min (2 * r) (D - 2 * r) : ℕ) : ℝ))) := by
  obtain ⟨K, hK⟩ := exists_inv_r hS
  have ht0 := gap_eq_at_inv hS v hB K hK
  refine ⟨(K : ℝ) / D, ht0, ?_⟩
  obtain ⟨a, b, hab, hplus, hminus, _, _⟩ := runners_at_eq hS v hB _ ht0
  have hD1 := hS.hD1
  have hN2 := hS.hN
  rcases le_total b a with h | h
  · left
    intro i m hm
    have hvi := hminus i m hm
    have : v i ≤ ((min (2 * r) (D - 2 * r) : ℕ) : ℤ) := by
      rw [hvi]
      rcases le_total (2 * r) (D - 2 * r) with h2 | h2
      · rw [min_eq_left h2]; omega
      · rw [min_eq_right h2]; omega
    exact_mod_cast this
  · right
    intro i n hn
    have hvi := hplus i n hn
    have : v i ≤ ((min (2 * r) (D - 2 * r) : ℕ) : ℤ) := by
      rw [hvi]
      rcases le_total (2 * r) (D - 2 * r) with h2 | h2
      · rw [min_eq_left h2]; omega
      · rw [min_eq_right h2]; omega
    exact_mod_cast this

/-- **Lemma D (uniqueness of `vμ`)**: any `vμ` with (V1) and (V2) is `min (2r) (D - 2r)`. -/
theorem vmu_eq {k N r D : ℕ} (hS : DSpec N r D) (v : Fin (k + 1) → ℤ) (hB : IsB N r v)
    (L : ℝ) (hL : L = 2 / (D : ℝ)) (vμ : ℕ)
    (hV1 : ∀ p, gap v p = L →
      (∃ i : Fin (k + 1), ∃ n : ℤ, (vμ : ℝ) ≤ (v i : ℝ) ∧ (v i : ℝ) * p = n + L) ∧
      (∃ j : Fin (k + 1), ∃ m : ℤ, (vμ : ℝ) ≤ (v j : ℝ) ∧ (v j : ℝ) * p = m - L))
    (t0 : ℝ) (ht0 : gap v t0 = L)
    (hext : (∀ i (m : ℤ), (v i : ℝ) * t0 = m - L → (v i : ℝ) ≤ vμ) ∨
            (∀ i (n : ℤ), (v i : ℝ) * t0 = n + L → (v i : ℝ) ≤ vμ)) :
    vμ = min (2 * r) (D - 2 * r) := by
  subst hL
  obtain ⟨a, b, hab, hplus, hminus, ⟨ip, np, hnp⟩, ⟨jm, mm, hmm⟩⟩ := runners_at_eq hS v hB t0 ht0
  obtain ⟨⟨i, n, hvi, hn⟩, ⟨j, m, hvj, hm⟩⟩ := hV1 t0 ht0
  have ha := hplus i n hn
  have hb := hminus j m hm
  have hva : (vμ : ℤ) ≤ a := by rw [← ha]; exact_mod_cast hvi
  have hvb : (vμ : ℤ) ≤ b := by rw [← hb]; exact_mod_cast hvj
  have hD1 := hS.hD1
  have hN2 := hS.hN
  have hlast : (b ≤ (vμ : ℤ)) ∨ (a ≤ (vμ : ℤ)) := by
    rcases hext with h | h
    · left
      have h1 := h jm mm hmm
      have hjb : v jm = b := hminus jm mm hmm
      rw [← hjb]
      exact_mod_cast h1
    · right
      have h1 := h ip np hnp
      have hia : v ip = a := hplus ip np hnp
      rw [← hia]
      exact_mod_cast h1
  rcases le_total (2 * r) (D - 2 * r) with h2 | h2
  · rw [min_eq_left h2]
    omega
  · rw [min_eq_right h2]
    omega

/-! ### The deleted vector and the exact value -/

def bNat (r i : ℕ) : ℕ := if i + 1 < r then i + 1 else i + 2

/-- The speed vector `[N] \ {r}` on `N - 1 = k + 1` entries (`N = k + 2`): index `i` carries `i + 1` below
`r` and `i + 2` from `r` on. -/
def bFam (k r : ℕ) : Fin (k + 1) → ℤ := fun i => ((bNat r (i : ℕ) : ℕ) : ℤ)

theorem bNat_facts {k N r : ℕ} (hk : k + 2 = N) (hr : 1 ≤ r) (hrN : r ≤ N) (i : ℕ)
    (hi : i < k + 1) : 1 ≤ bNat r i ∧ bNat r i ≤ N ∧ bNat r i ≠ r := by
  unfold bNat
  split_ifs <;> omega

theorem isB_bFam {k N r : ℕ} (hk : k + 2 = N) (hr : 1 ≤ r) (hrN : 2 * r ≤ N) :
    IsB N r (bFam k r) := by
  refine ⟨fun i => ?_, fun x hx1 hxN hxr => ?_⟩
  · obtain ⟨h1, h2, h3⟩ := bNat_facts hk hr (by omega) (i : ℕ) i.isLt
    show 1 ≤ ((bNat r (i : ℕ) : ℕ) : ℤ) ∧ ((bNat r (i : ℕ) : ℕ) : ℤ) ≤ (N : ℤ) ∧
      ((bNat r (i : ℕ) : ℕ) : ℤ) ≠ (r : ℤ)
    exact ⟨by exact_mod_cast h1, by exact_mod_cast h2, by exact_mod_cast h3⟩
  · by_cases hxr' : x < r
    · refine ⟨⟨x - 1, by omega⟩, ?_⟩
      show ((bNat r (x - 1) : ℕ) : ℤ) = (x : ℤ)
      have : bNat r (x - 1) = x := by
        unfold bNat
        split_ifs <;> omega
      rw [this]
    · refine ⟨⟨x - 2, by omega⟩, ?_⟩
      show ((bNat r (x - 2) : ℕ) : ℤ) = (x : ℤ)
      have : bNat r (x - 2) = x := by
        unfold bNat
        split_ifs <;> omega
      rw [this]

theorem ML_bFam {k N r D : ℕ} (hk : k + 2 = N) (hS : DSpec N r D) :
    ML (bFam k r) = 2 / (D : ℝ) :=
  ML_eq_two_div hS _ (isB_bFam hk hS.hr hS.hN)

/-- **Exact one-entry value** (Theorem V1 of the accompanying notes on the one-entry deletion, with the threshold `2 N^3` of `Kstar_E`).
`N = k + 2`, `D` the least integer `≥ N + 1 + r` coprime to `r` (`2 r ≤ N`), `D ∣ w`, `w ≥ 2 N^3`:
`ML ([N] with r replaced by w) = 2 w / (D (w + min (2r) (D - 2r)))`. -/
theorem one_entry_value {k N r D w : ℕ} (hk : k + 2 = N) (hS : DSpec N r D) (hDw : D ∣ w)
    (hw : 2 * N ^ 3 ≤ w) :
    ML (wFam (k + 1) r w) =
      2 * (w : ℝ) / ((D : ℝ) * ((w : ℝ) + ((min (2 * r) (D - 2 * r) : ℕ) : ℝ))) := by
  have hr := hS.hr
  have hN2 := hS.hN
  have hN3 := hS.hN3
  have hD1 := hS.hD1
  have hB := isB_bFam hk hr hN2
  have hDpos : (0 : ℝ) < D := by exact_mod_cast (by omega : 0 < D)
  have hML : ML (bFam k r) = 2 / (D : ℝ) := ML_eq_two_div hS _ hB
  have hL0 : 0 < ML (bFam k r) := by rw [hML]; exact div_pos (by norm_num) hDpos
  have hL1 : ML (bFam k r) < 1 / 2 := by
    rw [hML, div_lt_div_iff₀ hDpos (by norm_num)]
    have : (4 : ℝ) < D := by exact_mod_cast (by omega : 4 < D)
    linarith
  obtain ⟨vμ, hpos, hV1, ⟨t0, ht0, hext⟩, hmain⟩ :=
    Kstar_E (bFam k r) (fun i => by have := (hB.sub i).1; omega) (N : ℤ)
      (fun i => (hB.sub i).2.1) hL0 hL1
  have hvm : vμ = min (2 * r) (D - 2 * r) :=
    vmu_eq hS (bFam k r) hB (ML (bFam k r)) hML vμ hV1 t0 ht0 hext
  have hNpos : 0 < N := by omega
  have hwpos : 0 < w := by
    have h1 : 0 < N ^ 3 := pow_pos hNpos 3
    omega
  have hW : (0 : ℝ) < w := by exact_mod_cast hwpos
  obtain ⟨s, hs⟩ := hDw
  have hwR : ((w : ℤ) : ℝ) = (D : ℝ) * (s : ℝ) := by exact_mod_cast hs
  have hDw' : ∀ p, gap (bFam k r) p = ML (bFam k r) → ∃ z : ℤ, ((w : ℤ) : ℝ) * p = z := by
    intro p hp
    rw [hML] at hp
    obtain ⟨K, hK, hpK⟩ := eqtime_classify hS _ hB p hp
    have hDne : (D : ℝ) ≠ 0 := hDpos.ne'
    have e1 : ((w : ℤ) : ℝ) * ((K : ℝ) / D) = (s : ℝ) * K := by
      rw [hwR]
      calc (D : ℝ) * s * (K / D) = s * K * ((D : ℝ) / D) := by ring
        _ = s * K := by rw [div_self hDne, mul_one]
    rcases hpK with h | h
    · refine ⟨(s : ℤ) * K, ?_⟩
      rw [h, e1]
      norm_cast
    · refine ⟨-((s : ℤ) * K), ?_⟩
      have e2 : ((w : ℤ) : ℝ) * (-((K : ℝ) / D)) = -(((w : ℤ) : ℝ) * ((K : ℝ) / D)) := by ring
      rw [h, e2, e1]
      norm_cast
  have key := hmain (w : ℤ) (by exact_mod_cast hw) hDw'
  have hcong : ML (wFam (k + 1) r w) = ML (Fin.snoc (bFam k r) (w : ℤ) : Fin (k + 2) → ℤ) := by
    apply ML_congr_range (l := k + 1)
    · intro i
      by_cases hi : (i : ℕ) + 1 = r
      · exact ⟨Fin.last (k + 1),
          (wFam_at_r (k := k + 1) (r := r) (w := w) i hi).trans
            (snoc_last_eq (bFam k r) (w : ℤ)).symm⟩
      · have hxN : (i : ℕ) + 1 ≤ N := by have := i.isLt; omega
        obtain ⟨j, hj⟩ := hB.cov ((i : ℕ) + 1) (by omega) hxN hi
        exact ⟨Fin.castSucc j,
          (wFam_ne_r (k := k + 1) (r := r) (w := w) i hi).trans
            (hj.symm.trans (snoc_castSucc_eq (bFam k r) (w : ℤ) j).symm)⟩
    · intro j
      induction j using Fin.lastCases with
      | last =>
        have hr1 : r - 1 < k + 1 + 1 := by omega
        exact ⟨⟨r - 1, hr1⟩, (snoc_last_eq (bFam k r) (w : ℤ)).trans
          (wFam_at_r (k := k + 1) (r := r) (w := w) ⟨r - 1, hr1⟩
            (by show r - 1 + 1 = r; omega)).symm⟩
      | cast j' =>
        obtain ⟨hf1, hf2, hf3⟩ := bNat_facts hk hr (by omega) (j' : ℕ) j'.isLt
        obtain ⟨i, hi⟩ := wFam_retained (k := k + 1) (N := N) (w := w) (by omega) hf1 hf2 hf3
        exact ⟨i, (snoc_castSucc_eq (bFam k r) (w : ℤ) j').trans hi.symm⟩
  rw [hcong, key, hML, hvm]
  have hwR2 : ((w : ℤ) : ℝ) = (w : ℝ) := by norm_cast
  rw [hwR2]
  generalize (w : ℝ) + ((min (2 * r) (D - 2 * r) : ℕ) : ℝ) = S
  ring

/-- The same, with `D = dFam N r` and `3 ≤ N`, `1 ≤ r`, `2 r ≤ N`. -/
theorem one_entry_value_dFam {k N r w : ℕ} (hk : k + 2 = N) (hN3 : 3 ≤ N) (hr : 1 ≤ r)
    (hrN : 2 * r ≤ N) (hDw : dFam N r ∣ w) (hw : 2 * N ^ 3 ≤ w) :
    ML (wFam (k + 1) r w) =
      2 * (w : ℝ) / ((dFam N r : ℝ) *
        ((w : ℝ) + ((min (2 * r) (dFam N r - 2 * r) : ℕ) : ℝ))) :=
  one_entry_value hk (spec_dFam hr hrN hN3) hDw hw

end Gap
end Sext6
end LRSpectrumFull
