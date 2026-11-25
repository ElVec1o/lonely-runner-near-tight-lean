import LRSpectrumFull.Sext6.Gap.OneRBase
import Mathlib.NumberTheory.DiophantineApproximation.Basic

/-!
# One-entry deletion `B = [N] \ {r}`, part 2: the arc lemma, the upper bound, the equality times  [2026-11-25]

Source: the accompanying notes on the one-entry deletion, Lemma A (arc), Lemma B2 (upper bound),
Lemma C (equality times).

Let `D` be the least integer `≥ N+1+r` coprime to `r`, `1 ≤ r`, `2 r ≤ N`, `3 ≤ N` (`DSpec N r D`).
* `core_arc`        : if every speed `x ∈ [1,N] \ {r}` has `τ ≤ ‖x p‖` with `τ > 1/(N+1)`, then `τ ≤ 2/D`;
                      and `τ = 2/D` forces `p = ± K/D` with `D ∣ r K - 1`.
* `gap_le_two_div`  : `gap v p ≤ 2/D` for every `v` containing `[1,N] \ {r}`.
* `ML_eq_two_div`   : `ML v = 2/D` when the speed set of `v` is exactly `[1,N] \ {r}`.
* `eqtime_classify` : the equality times (`gap v p = 2/D`) are `p = ± K/D`, `r K ≡ 1 (mod D)`.
* `gap_eq_at_inv`   : conversely `gap v (K/D) = 2/D` for every such `K`.
No `sorry`, no `axiom`.

Convention: `N` is the size of the ambient interval `[N]` (`DSpec N r D`, `IsB N r v`): the deletion of `r` leaves `N - 1` distinct speeds, and `k` is not linked to `N` in the `IsB` statements (repetitions and any order are allowed). `bFam k r` lists `[N] \ {r}` and has `k + 1 = N - 1` entries when `N = k + 2`; `wFam (k+1) r w` has `k + 2 = N` entries (compare `OE_low_unconditional`, where `wFam k r w` has `k + 1 = N` entries). Speeds are the moving runners; the runner at rest is not counted, so a vector of `N` speeds means `N + 1` runners and the Lonely Runner value is `1/(N+1)`.
Hypotheses: those of the individual statements (numerical bounds, structural conditions and, where named in the list above, window predicates such as `PrimeWin`, `CopWin`, `PrimeWindow7`, which later modules discharge for explicit ranges). The unproved predicates `DusartPi`, `LRCHyp`, `CopWinHyp` are not hypotheses of any statement in this module.
Axiom audit: covered by `Axioms19` (`#print axioms`; declarations not printed there are bricks of printed ones, so their axioms are bounded by the printed lines).
-/

namespace LRSpectrumFull
namespace Sext6
namespace Gap

/-- The arc of `p` at `r p = c + η` is a unit class: otherwise a smaller multiplier `r/g` traps `p`. -/
theorem unit_of_arc {N r : ℕ} (hr : 1 ≤ r) (hrN : r ≤ N) (τ p η : ℝ) (c : ℤ)
    (hτ : 1 / ((N : ℝ) + 1) < τ) (hrt : (r : ℝ) * p = c + η) (hη0 : 0 ≤ η)
    (hη1 : η ≤ 1 / ((N : ℝ) + 1))
    (hx : ∀ x : ℕ, 1 ≤ x → x ≤ N → x ≠ r → τ ≤ nearestIntDist ((x : ℝ) * p)) :
    IsCoprime c (r : ℤ) := by
  rw [Int.isCoprime_iff_gcd_eq_one]
  by_contra hg
  have hd1 : ((Int.gcd c (r : ℤ) : ℕ) : ℤ) ∣ (r : ℤ) := Int.gcd_dvd_right c r
  have hd2 : ((Int.gcd c (r : ℤ) : ℕ) : ℤ) ∣ c := Int.gcd_dvd_left c r
  generalize Int.gcd c (r : ℤ) = g at hg hd1 hd2
  obtain ⟨y, hy⟩ := hd1
  obtain ⟨c', hc'⟩ := hd2
  have hg0 : 0 < g := by
    rcases Nat.eq_zero_or_pos g with h0 | h0
    · rw [h0] at hy
      simp at hy
      omega
    · exact h0
  have hg2 : 2 ≤ g := by omega
  have hg2' : (2 : ℤ) ≤ g := by exact_mod_cast hg2
  have hrz : (1 : ℤ) ≤ r := by exact_mod_cast hr
  have hy1 : 1 ≤ y := by
    by_contra hyc
    have h0 : y ≤ 0 := by omega
    have : (g : ℤ) * y ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (by positivity) h0
    linarith
  have hy2 : y < r := by
    have : 2 * y ≤ (g : ℤ) * y := mul_le_mul_of_nonneg_right hg2' (by omega)
    linarith
  have hyr : (y : ℤ) < r := hy2
  obtain ⟨xn, hxn⟩ : ∃ xn : ℕ, (xn : ℤ) = y := ⟨y.toNat, Int.toNat_of_nonneg (by omega)⟩
  have hxnR : (xn : ℝ) = (y : ℝ) := by exact_mod_cast hxn
  have hrR : (r : ℝ) = (g : ℝ) * (y : ℝ) := by
    have := congrArg (fun z : ℤ => (z : ℝ)) hy
    push_cast at this
    exact this
  have hcR : (c : ℝ) = (g : ℝ) * (c' : ℝ) := by
    have := congrArg (fun z : ℤ => (z : ℝ)) hc'
    push_cast at this
    exact this
  have hgR : (2 : ℝ) ≤ g := by exact_mod_cast hg2
  have hw : (g : ℝ) * ((y : ℝ) * p - c') = η := by
    have := hrt
    rw [hrR, hcR] at this
    linarith
  have hw0 : 0 ≤ (y : ℝ) * p - c' := by
    by_contra hcon
    have : (g : ℝ) * ((y : ℝ) * p - c') < 0 :=
      mul_neg_of_pos_of_neg (by linarith) (not_le.mp hcon)
    linarith
  have hw1 : (y : ℝ) * p - c' ≤ η := by
    have : 0 ≤ ((g : ℝ) - 1) * ((y : ℝ) * p - c') := mul_nonneg (by linarith) hw0
    nlinarith
  have h1 := hx xn (by omega) (by omega) (by omega)
  rw [hxnR] at h1
  have h2 := nearestIntDist_le_dist ((y : ℝ) * p) c'
  rw [abs_of_nonneg hw0] at h2
  linarith

/-- **Lemma A + Lemma B2 on one arc** (`η ≥ 0`).  `r p = c + η`, `0 ≤ η ≤ 1/(N+1)`. -/
theorem arc_pos {N r D : ℕ} (hS : DSpec N r D) (τ p η : ℝ) (c : ℤ)
    (hτ : 1 / ((N : ℝ) + 1) < τ) (hrt : (r : ℝ) * p = c + η) (hη0 : 0 ≤ η)
    (hη1 : η ≤ 1 / ((N : ℝ) + 1))
    (hx : ∀ x : ℕ, 1 ≤ x → x ≤ N → x ≠ r → τ ≤ nearestIntDist ((x : ℝ) * p)) :
    τ ≤ 2 / (D : ℝ) ∧
      (τ = 2 / (D : ℝ) → ∃ K : ℤ, (D : ℤ) ∣ (r : ℤ) * K - 1 ∧ p = (K : ℝ) / D) := by
  have hr := hS.hr
  have hN2 := hS.hN
  have hN3 := hS.hN3
  have hD1 := hS.hD1
  have hNR : (0 : ℝ) < (N : ℝ) + 1 := by positivity
  have hη2 : η * ((N : ℝ) + 1) ≤ 1 := (le_div_iff₀ hNR).mp hη1
  have hτpos : 0 < τ := lt_trans (by positivity) hτ
  have hcop := unit_of_arc hr (by omega) τ p η c hτ hrt hη0 hη1 hx
  obtain ⟨X, hX1, hX2, k, hk⟩ := exists_block r ((N : ℤ) + 1 - r) (by omega) c hcop
  obtain ⟨xn, hxn⟩ : ∃ xn : ℕ, (xn : ℤ) = X := ⟨X.toNat, Int.toNat_of_nonneg (by omega)⟩
  have hxN : xn ≤ N := by omega
  have hxr : xn ≠ r := by omega
  have hx1 : 1 ≤ xn := by omega
  have hcopx : Nat.Coprime xn r := by
    have : IsCoprime X (r : ℤ) := ⟨-c, k, by linarith⟩
    rw [← hxn] at this
    exact Nat.isCoprime_iff_coprime.mp this
  have hDle : D ≤ xn + 2 * r :=
    hS.hmin (xn + 2 * r) (by omega) ((Nat.coprime_add_mul_right_left xn r 2).mpr hcopx)
  have hxnR : (xn : ℝ) = (X : ℝ) := by exact_mod_cast hxn
  have hXR : (X : ℝ) ≤ N := by rw [← hxnR]; exact_mod_cast hxN
  have hDX : (D : ℝ) ≤ (X : ℝ) + 2 * r := by rw [← hxnR]; exact_mod_cast hDle
  -- the speed 2r
  have h2r := hx (2 * r) (by omega) hN2 (by omega)
  have h2r' := nearestIntDist_le_dist (((2 * r : ℕ) : ℝ) * p) (2 * c)
  have e2 : ((2 * r : ℕ) : ℝ) * p - ((2 * c : ℤ) : ℝ) = 2 * η := by
    push_cast
    linear_combination 2 * hrt
  rw [e2, abs_of_nonneg (by linarith)] at h2r'
  have hτη : τ ≤ 2 * η := le_trans h2r h2r'
  -- the speed X
  have hxv := hx xn hx1 hxN hxr
  rw [hxnR] at hxv
  have hkR : (c : ℝ) * X + 1 = r * k := by exact_mod_cast hk
  have hw : (r : ℝ) * ((X : ℝ) * p - k) = X * η - 1 := by
    linear_combination (X : ℝ) * hrt + hkR
  have hXη : (X : ℝ) * η ≤ 1 := by
    have h1 : (X : ℝ) * η ≤ N * η := mul_le_mul_of_nonneg_right hXR hη0
    nlinarith
  have hrpos : (0 : ℝ) < r := by exact_mod_cast (by omega : 0 < r)
  have hw0 : (X : ℝ) * p - k ≤ 0 := by
    by_contra hcon
    have := mul_pos hrpos (not_le.mp hcon)
    linarith
  have h1 : τ ≤ -((X : ℝ) * p - k) := by
    have := le_trans hxv (nearestIntDist_le_dist ((X : ℝ) * p) k)
    rwa [abs_of_nonpos hw0] at this
  have hX : (r : ℝ) * τ ≤ 1 - X * η := by
    have := mul_le_mul_of_nonneg_left h1 hrpos.le
    linarith
  have hDpos : (0 : ℝ) < D := by exact_mod_cast (by omega : 0 < D)
  have hDne : (D : ℝ) ≠ 0 := hDpos.ne'
  have hA0 : 0 < (D : ℝ) - 2 * r := by
    have h3 : 2 * r < D := by omega
    have h4 : ((2 * r : ℕ) : ℝ) < D := by exact_mod_cast h3
    push_cast at h4
    linarith
  have ha : 0 ≤ ((D : ℝ) - 2 * r) * (2 * η - τ) := mul_nonneg hA0.le (by linarith)
  have hb : 0 ≤ ((X : ℝ) - ((D : ℝ) - 2 * r)) * η := mul_nonneg (by linarith) hη0
  refine ⟨?_, fun heq => ?_⟩
  · rw [le_div_iff₀ hDpos]
    linarith [ha, hb, hX]
  · have hτD : τ * D = 2 := by
      rw [heq]
      field_simp
    have hs1 : ((D : ℝ) - 2 * r) * (2 * η - τ) = 0 :=
      le_antisymm (by linarith [ha, hb, hX, hτD]) ha
    have hs2 : ((X : ℝ) - ((D : ℝ) - 2 * r)) * η = 0 :=
      le_antisymm (by linarith [ha, hb, hX, hτD]) hb
    have hη_eq : 2 * η - τ = 0 := by
      rcases mul_eq_zero.mp hs1 with h | h
      · linarith
      · exact h
    have hηpos : 0 < η := by linarith
    have hX_eq : (X : ℝ) = (D : ℝ) - 2 * r := by
      rcases mul_eq_zero.mp hs2 with h | h
      · linarith
      · linarith
    have hηD : η * D = 1 := by
      have h5 : η = τ / 2 := by linarith
      rw [h5]
      linarith [hτD]
    have hDXR : (D : ℝ) = X + 2 * r := by linarith
    have hDXz : (D : ℤ) = X + 2 * r := by exact_mod_cast hDXR
    refine ⟨k + 2 * c, ⟨c, ?_⟩, ?_⟩
    · linear_combination (-1 : ℤ) * hk + (-c) * hDXz
    · have hr0 : (r : ℝ) ≠ 0 := hrpos.ne'
      have h0 : (r : ℝ) * (p * D - ((k + 2 * c : ℤ) : ℝ)) = 0 := by
        push_cast
        linear_combination (D : ℝ) * hrt + hηD + hkR + (c : ℝ) * hDXR
      have h6 : p * D - ((k + 2 * c : ℤ) : ℝ) = 0 := by
        rcases mul_eq_zero.mp h0 with h | h
        · exact absurd h hr0
        · exact h
      rw [eq_div_iff hDne]
      linarith

/-- The trap radius `1/(N+1)` is below the top value `2/D`. -/
theorem one_div_lt_two_div {N r D : ℕ} (hS : DSpec N r D) :
    1 / ((N : ℝ) + 1) < 2 / (D : ℝ) := by
  have h1 := hS.le_two_N
  have hD1 := hS.hD1
  have hDpos : (0 : ℝ) < D := by exact_mod_cast (by omega : 0 < D)
  have hNR : (0 : ℝ) < (N : ℝ) + 1 := by positivity
  rw [div_lt_div_iff₀ hNR hDpos]
  have : (D : ℝ) ≤ 2 * N := by exact_mod_cast h1
  linarith

/-- **Core lemma** (Dirichlet + arc). -/
theorem core_arc {N r D : ℕ} (hS : DSpec N r D) (τ p : ℝ) (hτ : 1 / ((N : ℝ) + 1) < τ)
    (hx : ∀ x : ℕ, 1 ≤ x → x ≤ N → x ≠ r → τ ≤ nearestIntDist ((x : ℝ) * p)) :
    τ ≤ 2 / (D : ℝ) ∧
      (τ = 2 / (D : ℝ) →
        ∃ K : ℤ, (D : ℤ) ∣ (r : ℤ) * K - 1 ∧ (p = (K : ℝ) / D ∨ p = -((K : ℝ) / D))) := by
  have hr := hS.hr
  have hN2 := hS.hN
  have hN3 := hS.hN3
  obtain ⟨j, q, hq0, hqN, hqd⟩ := Real.exists_int_int_abs_mul_sub_le p (n := N) (by omega)
  obtain ⟨qn, hqn⟩ : ∃ qn : ℕ, (qn : ℤ) = q := ⟨q.toNat, Int.toNat_of_nonneg (by omega)⟩
  have hqnR : (qn : ℝ) = (q : ℝ) := by exact_mod_cast hqn
  have hqnN : qn ≤ N := by
    have : (qn : ℤ) ≤ N := by rw [hqn]; exact_mod_cast hqN
    exact_mod_cast this
  have hqr : qn = r := by
    by_contra hne
    have h3 := hx qn (by omega) hqnN hne
    rw [hqnR] at h3
    have h4 := nearestIntDist_le_dist ((q : ℝ) * p) j
    linarith
  have hqr' : (q : ℝ) = r := by rw [← hqnR]; exact_mod_cast hqr
  rw [hqr'] at hqd
  obtain ⟨hl, hu⟩ := abs_le.mp hqd
  rcases le_or_gt 0 ((r : ℝ) * p - j) with hη | hη
  · obtain ⟨h1, h2⟩ := arc_pos hS τ p ((r : ℝ) * p - j) j hτ (by ring) hη hu hx
    refine ⟨h1, fun he => ?_⟩
    obtain ⟨K, hK, hp⟩ := h2 he
    exact ⟨K, hK, Or.inl hp⟩
  · have hx' : ∀ x : ℕ, 1 ≤ x → x ≤ N → x ≠ r → τ ≤ nearestIntDist ((x : ℝ) * (-p)) := by
      intro x hx1 hxN hxr
      rw [show (x : ℝ) * (-p) = -((x : ℝ) * p) by ring, nearestIntDist_neg]
      exact hx x hx1 hxN hxr
    obtain ⟨h1, h2⟩ := arc_pos hS τ (-p) (-((r : ℝ) * p - j)) (-j) hτ
      (by push_cast; ring) (by linarith) (by linarith) hx'
    refine ⟨h1, fun he => ?_⟩
    obtain ⟨K, hK, hp⟩ := h2 he
    exact ⟨K, hK, Or.inr (by linarith)⟩

/-! ### Assembly for a speed vector -/

theorem gap_le_two_div {k N r D : ℕ} (hS : DSpec N r D) (v : Fin (k + 1) → ℤ) (hB : IsB N r v)
    (p : ℝ) : gap v p ≤ 2 / (D : ℝ) := by
  by_contra hcon
  have hcon' := not_le.mp hcon
  have hτ : 1 / ((N : ℝ) + 1) < gap v p := lt_trans (one_div_lt_two_div hS) hcon'
  have hx : ∀ x : ℕ, 1 ≤ x → x ≤ N → x ≠ r → gap v p ≤ nearestIntDist ((x : ℝ) * p) := by
    intro x hx1 hxN hxr
    obtain ⟨i, hi⟩ := hB.cov x hx1 hxN hxr
    have h1 := gap_le v p i
    have h2 : ((v i : ℤ) : ℝ) = (x : ℝ) := by exact_mod_cast hi
    rw [h2] at h1
    exact h1
  have := (core_arc hS (gap v p) p hτ hx).1
  linarith

theorem ML_le_two_div {k N r D : ℕ} (hS : DSpec N r D) (v : Fin (k + 1) → ℤ) (hB : IsB N r v) :
    ML v ≤ 2 / (D : ℝ) := by
  unfold ML
  apply csSup_le (Set.range_nonempty _)
  rintro y ⟨t, rfl⟩
  exact gap_le_two_div hS v hB t

/-- **Theorem P(b)** (Liu, `s = 1`): `ML ([N] \ {r}) = 2/D`. -/
theorem ML_eq_two_div {k N r D : ℕ} (hS : DSpec N r D) (v : Fin (k + 1) → ℤ) (hB : IsB N r v) :
    ML v = 2 / (D : ℝ) :=
  le_antisymm (ML_le_two_div hS v hB) (ML_ge_delB hS v hB.sub)

/-- **Theorem P(c)**: the equality times are `± K/D` with `r K ≡ 1 (mod D)`. -/
theorem eqtime_classify {k N r D : ℕ} (hS : DSpec N r D) (v : Fin (k + 1) → ℤ) (hB : IsB N r v)
    (p : ℝ) (hp : gap v p = 2 / (D : ℝ)) :
    ∃ K : ℤ, (D : ℤ) ∣ (r : ℤ) * K - 1 ∧ (p = (K : ℝ) / D ∨ p = -((K : ℝ) / D)) := by
  have hτ : 1 / ((N : ℝ) + 1) < gap v p := by rw [hp]; exact one_div_lt_two_div hS
  have hx : ∀ x : ℕ, 1 ≤ x → x ≤ N → x ≠ r → gap v p ≤ nearestIntDist ((x : ℝ) * p) := by
    intro x hx1 hxN hxr
    obtain ⟨i, hi⟩ := hB.cov x hx1 hxN hxr
    have h1 := gap_le v p i
    have h2 : ((v i : ℤ) : ℝ) = (x : ℝ) := by exact_mod_cast hi
    rw [h2] at h1
    exact h1
  exact (core_arc hS (gap v p) p hτ hx).2 hp

/-- Conversely `K/D` is an equality time whenever `D ∣ r K - 1`. -/
theorem gap_eq_at_inv {k N r D : ℕ} (hS : DSpec N r D) (v : Fin (k + 1) → ℤ) (hB : IsB N r v)
    (K : ℤ) (hK : (D : ℤ) ∣ (r : ℤ) * K - 1) : gap v ((K : ℝ) / D) = 2 / (D : ℝ) :=
  le_antisymm (gap_le_two_div hS v hB _) (gap_ge_at_inv hS v hB.sub K hK)

end Gap
end Sext6
end LRSpectrumFull
