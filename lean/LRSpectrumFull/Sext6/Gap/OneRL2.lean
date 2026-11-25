import LRSpectrumFull.Sext6.Gap.OneRVal

/-!
# One-entry deletion `B = [N] \ {r}`, part 4: the local maxima of `gap`, the bound `L2`  [2026-11-25]

Source: the accompanying notes on the one-entry deletion (Plan 3), Lemma E (local maxima above `1/(N+1)`; `L2`).

Let `D` be the least integer `≥ N+1+r` coprime to `r` (`DSpec N r D`), `D1` the least integer `> D` coprime to `r`.
* `arc_local_max`    : on an arc `r p = c + η`, `0 ≤ η ≤ 1/(N+1)`, a point `p` with `gap v p = μ > 1/(N+1)` that has a runner
                       at `+μ` and a runner at `-μ` has `μ = 2/D'` with `D' ∈ [N+1+r, N+2r]` coprime to `r`
                       (this is the arc profile `min (2η, (1 - Xη)/r)` at its crossing; the profile itself is not needed:
                       the two active runners are forced to be `2r` and the top element `X` of the class `-c⁻¹`).
* `local_max_classify` : every local maximum of `gap v` (speed set exactly `[N] \ {r}`) of value `> 1/(N+1)` has value `2/D'`
                       with `D' ∈ [N+1+r, N+2r]` coprime to `r`.
* `L2_delB`          : every local-maximum value of `gap v` below `ML v = 2/D` is at most `2/D1` if `D1 ≤ N + 2r`,
                       and at most `1/(N+1)` otherwise.
* `ML_wFam_eq_snoc`  : `ML` of `[N]` with `r` replaced by `w` is `ML (Fin.snoc (bFam k r) w)`.
* `ML_snoc_le_self`  : adding an entry never raises `ML`.
Direction proved: "every local maximum value `μ < ML` satisfies `μ ≤ 2/D1` or `μ ≤ 1/(N+1)`" and the exact form
"every local-maximum value above `1/(N+1)` is `2/D'`, `D'` in the window, coprime to `r`". The converse ("each such `2/D'`
is attained as a local maximum") is not formalised here.
No `sorry`, no `axiom`.

Convention: `N` is the size of the ambient interval `[N]` (`DSpec N r D`, `IsB N r v`): the deletion of `r` leaves `N - 1` distinct speeds, and `k` is not linked to `N` in the `IsB` statements (repetitions and any order are allowed). `bFam k r` lists `[N] \ {r}` and has `k + 1 = N - 1` entries when `N = k + 2`; `wFam (k+1) r w` has `k + 2 = N` entries. Speeds are the moving runners; the runner at rest is not counted, so a vector of `N` speeds means `N + 1` runners and the Lonely Runner value is `1/(N+1)`.
Hypotheses: those of the individual statements. The unproved predicates `DusartPi`, `LRCHyp`, `CopWinHyp` are not hypotheses of any statement in this module.
Axiom audit: covered by `Axioms21`.
-/

namespace LRSpectrumFull
namespace Sext6
namespace Gap

/-- Data of one arc (`η ≥ 0`): `c` is a unit mod `r`, `μ ≤ 2η`, `0 < η`, `r μ < 1`, and the top element `X ≥ N+1-r`
of the class `-c⁻¹` mod `r` gives `r μ ≤ 1 - X η`. -/
theorem arc_data {k N r D : ℕ} (hS : DSpec N r D) (v : Fin (k + 1) → ℤ) (hB : IsB N r v)
    (p μ η : ℝ) (c : ℤ) (hgap : gap v p = μ) (hμ : 1 / ((N : ℝ) + 1) < μ)
    (hrt : (r : ℝ) * p = c + η) (hη0 : 0 ≤ η) (hη1 : η ≤ 1 / ((N : ℝ) + 1)) :
    IsCoprime c (r : ℤ) ∧ μ ≤ 2 * η ∧ 0 < η ∧ (r : ℝ) * μ < 1 ∧
      ∃ X : ℤ, (N : ℤ) + 1 - r ≤ X ∧ X ≤ N ∧ (r : ℝ) * μ ≤ 1 - X * η := by
  have hr := hS.hr
  have hN2 := hS.hN
  have hN3 := hS.hN3
  have hNR : (0 : ℝ) < (N : ℝ) + 1 := by positivity
  have hη2 : η * ((N : ℝ) + 1) ≤ 1 := (le_div_iff₀ hNR).mp hη1
  have hμ0 : 0 < μ := lt_trans (by positivity) hμ
  have hx : ∀ x : ℕ, 1 ≤ x → x ≤ N → x ≠ r → μ ≤ nearestIntDist ((x : ℝ) * p) := by
    intro x hx1 hxN hxr
    obtain ⟨i', hi'⟩ := hB.cov x hx1 hxN hxr
    have h1 := gap_le v p i'
    have h2 : ((v i' : ℤ) : ℝ) = (x : ℝ) := by exact_mod_cast hi'
    rw [h2, hgap] at h1
    exact h1
  have hcop := unit_of_arc hr (by omega) μ p η c hμ hrt hη0 hη1 hx
  obtain ⟨X, hX1, hX2, kk, hkk⟩ := exists_block r ((N : ℤ) + 1 - r) (by omega) c hcop
  obtain ⟨xn, hxn⟩ : ∃ xn : ℕ, (xn : ℤ) = X := ⟨X.toNat, Int.toNat_of_nonneg (by omega)⟩
  have hxN : xn ≤ N := by omega
  have hxr : xn ≠ r := by omega
  have hx1 : 1 ≤ xn := by omega
  have hxnR : (xn : ℝ) = (X : ℝ) := by exact_mod_cast hxn
  have hXR : (X : ℝ) ≤ N := by rw [← hxnR]; exact_mod_cast hxN
  have hXpos : (0 : ℝ) < X := by
    have h1 : (1 : ℝ) ≤ (xn : ℝ) := by exact_mod_cast hx1
    rw [hxnR] at h1
    linarith
  -- the speed 2r
  have h2r := hx (2 * r) (by omega) hN2 (by omega)
  have h2r' := nearestIntDist_le_dist (((2 * r : ℕ) : ℝ) * p) (2 * c)
  have e2 : ((2 * r : ℕ) : ℝ) * p - ((2 * c : ℤ) : ℝ) = 2 * η := by
    push_cast
    linear_combination 2 * hrt
  rw [e2, abs_of_nonneg (by linarith)] at h2r'
  have hμη : μ ≤ 2 * η := le_trans h2r h2r'
  have hηpos : 0 < η := by linarith
  -- the speed X
  have hxv := hx xn hx1 hxN hxr
  rw [hxnR] at hxv
  have hkR : (c : ℝ) * X + 1 = r * kk := by exact_mod_cast hkk
  have hw : (r : ℝ) * ((X : ℝ) * p - kk) = X * η - 1 := by
    linear_combination (X : ℝ) * hrt + hkR
  have hXη : (X : ℝ) * η ≤ 1 := by
    have h1 : (X : ℝ) * η ≤ N * η := mul_le_mul_of_nonneg_right hXR hη0
    linarith
  have hrpos : (0 : ℝ) < r := by exact_mod_cast (by omega : 0 < r)
  have hw0 : (X : ℝ) * p - kk ≤ 0 := by
    by_contra hcon
    have := mul_pos hrpos (not_le.mp hcon)
    linarith
  have h1 : μ ≤ -((X : ℝ) * p - kk) := by
    have := le_trans hxv (nearestIntDist_le_dist ((X : ℝ) * p) kk)
    rwa [abs_of_nonpos hw0] at this
  have hXμ : (r : ℝ) * μ ≤ 1 - X * η := by
    have := mul_le_mul_of_nonneg_left h1 hrpos.le
    linarith
  have hXηpos : 0 < (X : ℝ) * η := mul_pos hXpos hηpos
  exact ⟨hcop, hμη, hηpos, by linarith, X, hX1, by omega, hXμ⟩

/-- The runner at `+μ` is the speed `2r`: `μ = 2η`. -/
theorem plus_arc {N r : ℕ} (hr : 1 ≤ r) (p μ η : ℝ) (c a n : ℤ) (hcop : IsCoprime c (r : ℤ))
    (hrt : (r : ℝ) * p = c + η) (hi : (a : ℝ) * p = n + μ) (ha1 : 1 ≤ a) (haN : a ≤ N)
    (har : a ≠ r) (hη2 : η * ((N : ℝ) + 1) ≤ 1) (hηpos : 0 < η) (hμη : μ ≤ 2 * η)
    (hrμ1 : (r : ℝ) * μ < 1) (hμ0 : 0 < μ) : μ = 2 * η := by
  have hrpos : (0 : ℝ) < r := by exact_mod_cast (by omega : 0 < r)
  have hrμ0 : 0 < (r : ℝ) * μ := mul_pos hrpos hμ0
  obtain ⟨I, hIdef⟩ : ∃ I : ℤ, I = r * n - a * c := ⟨_, rfl⟩
  have hI : (I : ℝ) = (a : ℝ) * η - r * μ := by
    rw [hIdef]
    push_cast
    linear_combination (a : ℝ) * hrt - (r : ℝ) * hi
  have haR1 : (1 : ℝ) ≤ a := by exact_mod_cast ha1
  have haRN : (a : ℝ) ≤ N := by exact_mod_cast haN
  have haη : (a : ℝ) * η < 1 := by
    have := mul_le_mul_of_nonneg_right haRN hηpos.le
    linarith
  have haη0 : 0 < (a : ℝ) * η := mul_pos (by linarith) hηpos
  have hI0 : I = 0 := by
    have h1' : (I : ℝ) < 1 := by rw [hI]; linarith
    have h2' : (-1 : ℝ) < I := by rw [hI]; linarith
    have h1'' : I < 1 := by exact_mod_cast h1'
    have h2'' : -1 < I := by exact_mod_cast h2'
    omega
  have haημ : (a : ℝ) * η = r * μ := by
    have e : (I : ℝ) = 0 := by simp [hI0]
    linarith [hI, e]
  have hrdvd : (r : ℤ) ∣ a := by
    apply IsCoprime.dvd_of_dvd_mul_right hcop.symm
    exact ⟨n, by rw [hI0] at hIdef; linarith⟩
  obtain ⟨j', hj'⟩ := hrdvd
  have hj1 : 2 ≤ j' := by
    by_contra hcon
    have hcon' : j' < 2 := not_le.mp hcon
    rcases (show j' ≤ 0 ∨ j' = 1 by omega) with h0 | h1
    · have : (r : ℤ) * j' ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (by omega) h0
      omega
    · rw [h1] at hj'
      omega
  have haR : (a : ℝ) = (r : ℝ) * (j' : ℝ) := by exact_mod_cast hj'
  have hμj : μ = (j' : ℝ) * η := by
    have h0 : (r : ℝ) * (μ - (j' : ℝ) * η) = 0 := by
      rw [haR] at haημ
      linear_combination (-1 : ℝ) * haημ
    rcases mul_eq_zero.mp h0 with h | h
    · exact absurd h hrpos.ne'
    · linarith
  have hj2R : (j' : ℝ) ≤ 2 := by
    by_contra hcon
    have hcon' := not_le.mp hcon
    have := mul_pos (sub_pos.mpr hcon') hηpos
    linarith
  have hj2 : j' = 2 := by
    have : j' ≤ 2 := by exact_mod_cast hj2R
    omega
  have hj2R' : (j' : ℝ) = 2 := by exact_mod_cast hj2
  rw [hμj, hj2R']

/-- The runner at `-μ`: `r m - b c = 1` and `b η + r μ = 1`. -/
theorem minus_arc {N r : ℕ} (hr : 1 ≤ r) (p μ η : ℝ) (c b m : ℤ)
    (hrt : (r : ℝ) * p = c + η) (hj : (b : ℝ) * p = m - μ) (hb1 : 1 ≤ b) (hbN : b ≤ N)
    (hη2 : η * ((N : ℝ) + 1) ≤ 1) (hηpos : 0 < η) (hrμ1 : (r : ℝ) * μ < 1) (hμ0 : 0 < μ) :
    (r : ℤ) * m - b * c = 1 ∧ (b : ℝ) * η + r * μ = 1 := by
  have hrpos : (0 : ℝ) < r := by exact_mod_cast (by omega : 0 < r)
  have hrμ0 : 0 < (r : ℝ) * μ := mul_pos hrpos hμ0
  obtain ⟨J, hJdef⟩ : ∃ J : ℤ, J = r * m - b * c := ⟨_, rfl⟩
  have hJ : (J : ℝ) = (b : ℝ) * η + r * μ := by
    rw [hJdef]
    push_cast
    linear_combination (b : ℝ) * hrt - (r : ℝ) * hj
  have hbR1 : (1 : ℝ) ≤ b := by exact_mod_cast hb1
  have hbRN : (b : ℝ) ≤ N := by exact_mod_cast hbN
  have hbη : (b : ℝ) * η < 1 := by
    have := mul_le_mul_of_nonneg_right hbRN hηpos.le
    linarith
  have hbη0 : 0 < (b : ℝ) * η := mul_pos (by linarith) hηpos
  have hJ1 : J = 1 := by
    have h1' : (J : ℝ) < 2 := by rw [hJ]; linarith
    have h2' : (0 : ℝ) < J := by rw [hJ]; linarith
    have h1'' : J < 2 := by exact_mod_cast h1'
    have h2'' : 0 < J := by exact_mod_cast h2'
    omega
  have e : (J : ℝ) = 1 := by simp [hJ1]
  refine ⟨by rw [← hJdef]; exact hJ1, by linarith [hJ, e]⟩

/-- On one arc `η ≥ 0`: the active runners at a high point are `2r` and the top element of the class `-c⁻¹`. -/
theorem arc_local_max {k N r D : ℕ} (hS : DSpec N r D) (v : Fin (k + 1) → ℤ) (hB : IsB N r v)
    (p μ η : ℝ) (c : ℤ) (hgap : gap v p = μ) (hμ : 1 / ((N : ℝ) + 1) < μ)
    (hrt : (r : ℝ) * p = c + η) (hη0 : 0 ≤ η) (hη1 : η ≤ 1 / ((N : ℝ) + 1))
    (i j : Fin (k + 1)) (n m : ℤ)
    (hi : (v i : ℝ) * p = n + μ) (hj : (v j : ℝ) * p = m - μ) :
    ∃ D' : ℕ, N + 1 + r ≤ D' ∧ D' ≤ N + 2 * r ∧ Nat.Coprime D' r ∧ μ = 2 / (D' : ℝ) := by
  have hr := hS.hr
  have hN2 := hS.hN
  have hN3 := hS.hN3
  have hNR : (0 : ℝ) < (N : ℝ) + 1 := by positivity
  have hη2 : η * ((N : ℝ) + 1) ≤ 1 := (le_div_iff₀ hNR).mp hη1
  have hμ0 : 0 < μ := lt_trans (by positivity) hμ
  obtain ⟨hcop, hμη, hηpos, hrμ1, X, hX1, hXN, hXμ⟩ :=
    arc_data hS v hB p μ η c hgap hμ hrt hη0 hη1
  have hrpos : (0 : ℝ) < r := by exact_mod_cast (by omega : 0 < r)
  obtain ⟨ha1, haN, har⟩ := hB.sub i
  obtain ⟨a, ha_eq⟩ : ∃ a : ℤ, v i = a := ⟨_, rfl⟩
  rw [ha_eq] at hi ha1 haN har
  have hμ2η : μ = 2 * η :=
    plus_arc hr p μ η c a n hcop hrt hi ha1 haN har hη2 hηpos hμη hrμ1 hμ0
  obtain ⟨hb1, hbN, hbr⟩ := hB.sub j
  obtain ⟨b, hb_eq⟩ : ∃ b : ℤ, v j = b := ⟨_, rfl⟩
  rw [hb_eq] at hj hb1 hbN hbr
  obtain ⟨hJe, hb1R⟩ := minus_arc hr p μ η c b m hrt hj hb1 hbN hη2 hηpos hrμ1 hμ0
  have hXb : (X : ℝ) ≤ b := by
    by_contra hcon
    have hcon' := not_le.mp hcon
    have := mul_pos (sub_pos.mpr hcon') hηpos
    linarith
  have hXb' : X ≤ b := by exact_mod_cast hXb
  have hbR1 : (1 : ℝ) ≤ b := by exact_mod_cast hb1
  obtain ⟨bn, hbn⟩ : ∃ bn : ℕ, (bn : ℤ) = b := ⟨b.toNat, Int.toNat_of_nonneg (by omega)⟩
  refine ⟨bn + 2 * r, by omega, by omega, ?_, ?_⟩
  · have hcp : IsCoprime (((bn + 2 * r : ℕ)) : ℤ) (r : ℤ) :=
      ⟨-c, m + 2 * c, by push_cast; rw [hbn]; linear_combination hJe⟩
    exact Nat.isCoprime_iff_coprime.mp hcp
  · have hbnR : (bn : ℝ) = (b : ℝ) := by exact_mod_cast hbn
    have hD'R : ((bn + 2 * r : ℕ) : ℝ) = (b : ℝ) + 2 * r := by
      push_cast
      rw [hbnR]
    rw [hD'R]
    have hpos : (0 : ℝ) < (b : ℝ) + 2 * r := by linarith
    rw [eq_div_iff hpos.ne']
    linear_combination (b : ℝ) * hμ2η + 2 * hb1R

/-- **Local maxima above `1/(N+1)` (Lemma E(i), the direction needed).**  Every local maximum of `gap v`, `v` with speed
set exactly `[N] \ {r}`, of value `> 1/(N+1)`, has value `2/D'` with `D' ∈ [N+1+r, N+2r]` coprime to `r`. -/
theorem local_max_classify {k N r D : ℕ} (hS : DSpec N r D) (v : Fin (k + 1) → ℤ) (hB : IsB N r v)
    (p : ℝ) (hp : IsLocalMax (gap v) p) (hμ : 1 / ((N : ℝ) + 1) < gap v p) :
    ∃ D' : ℕ, N + 1 + r ≤ D' ∧ D' ≤ N + 2 * r ∧ Nat.Coprime D' r ∧ gap v p = 2 / (D' : ℝ) := by
  have hr := hS.hr
  have hN2 := hS.hN
  have hN3 := hS.hN3
  have hD1 := hS.hD1
  have hv : ∀ i, 0 < v i := fun i => by have := (hB.sub i).1; omega
  have hM : ∀ i, v i ≤ (N : ℤ) := fun i => (hB.sub i).2.1
  have h0 : 0 < gap v p := lt_trans (by positivity) hμ
  have h1 : gap v p < 1 / 2 := by
    have h2 := gap_le_two_div hS v hB p
    have hD4 : (4 : ℝ) < D := by exact_mod_cast (by omega : 4 < D)
    have h3 : 2 / (D : ℝ) < 1 / 2 := by
      rw [div_lt_div_iff₀ (by positivity) (by norm_num)]
      linarith
    linarith
  obtain ⟨i, j, n, m, hi, hj, -⟩ := local_max_structure v hv (N : ℤ) hM p hp h0 h1
  have hx : ∀ x : ℕ, 1 ≤ x → x ≤ N → x ≠ r → gap v p ≤ nearestIntDist ((x : ℝ) * p) := by
    intro x hx1 hxN hxr
    obtain ⟨i', hi'⟩ := hB.cov x hx1 hxN hxr
    have h1' := gap_le v p i'
    have h2' : ((v i' : ℤ) : ℝ) = (x : ℝ) := by exact_mod_cast hi'
    rw [h2'] at h1'
    exact h1'
  obtain ⟨c, q, hq0, hqN, hqd⟩ := Real.exists_int_int_abs_mul_sub_le p (n := N) (by omega)
  obtain ⟨qn, hqn⟩ : ∃ qn : ℕ, (qn : ℤ) = q := ⟨q.toNat, Int.toNat_of_nonneg (by omega)⟩
  have hqnR : (qn : ℝ) = (q : ℝ) := by exact_mod_cast hqn
  have hqnN : qn ≤ N := by
    have : (qn : ℤ) ≤ N := by rw [hqn]; exact_mod_cast hqN
    exact_mod_cast this
  have hqr : qn = r := by
    by_contra hne
    have h3 := hx qn (by omega) hqnN hne
    rw [hqnR] at h3
    have h4 := nearestIntDist_le_dist ((q : ℝ) * p) c
    linarith
  have hqr' : (q : ℝ) = r := by rw [← hqnR]; exact_mod_cast hqr
  rw [hqr'] at hqd
  obtain ⟨hl, hu⟩ := abs_le.mp hqd
  rcases le_or_gt 0 ((r : ℝ) * p - c) with hη | hη
  · exact arc_local_max hS v hB p (gap v p) ((r : ℝ) * p - c) c rfl hμ (by ring) hη hu i j n m hi hj
  · have hi' : (v i : ℝ) * (-p) = ((-n : ℤ) : ℝ) - gap v p := by
      push_cast
      linear_combination (-1 : ℝ) * hi
    have hj' : (v j : ℝ) * (-p) = ((-m : ℤ) : ℝ) + gap v p := by
      push_cast
      linear_combination (-1 : ℝ) * hj
    exact arc_local_max hS v hB (-p) (gap v p) (-((r : ℝ) * p - c)) (-c) (by rw [gap_neg]) hμ
      (by push_cast; ring) (by linarith) (by linarith) j i (-m) (-n) hj' hi'

/-- A numerical comparison used below. -/
lemma two_div_le_of_le {a b : ℕ} (ha : 0 < a) (h : a ≤ b) : 2 / (b : ℝ) ≤ 2 / (a : ℝ) := by
  have hb : 0 < b := lt_of_lt_of_le ha h
  have haR : (0 : ℝ) < a := by exact_mod_cast ha
  have hbR : (0 : ℝ) < b := by exact_mod_cast hb
  have hab : (a : ℝ) ≤ b := by exact_mod_cast h
  rw [div_le_div_iff₀ hbR haR]
  linarith

/-- **The bound `L2` (Lemma E(ii), the direction needed).**  `D1` is the least integer `> D` coprime to `r`.
Every local-maximum value of `gap v` below `2/D = ML v` is at most `2/D1` if `D1 ≤ N + 2r`, and at most `1/(N+1)`
otherwise. -/
theorem L2_delB {k N r D D1 : ℕ} (hS : DSpec N r D) (hD1lt : D < D1)
    (hD1min : ∀ b : ℕ, D < b → Nat.Coprime b r → D1 ≤ b)
    (v : Fin (k + 1) → ℤ) (hB : IsB N r v) (p : ℝ)
    (hp : IsLocalMax (gap v) p) (hlt : gap v p < 2 / (D : ℝ)) :
    gap v p ≤ (if D1 ≤ N + 2 * r then 2 / (D1 : ℝ) else 1 / ((N : ℝ) + 1)) := by
  have hr := hS.hr
  have hN2 := hS.hN
  have hN3 := hS.hN3
  have hD1 := hS.hD1
  have hD1pos : (0 : ℝ) < D1 := by exact_mod_cast (by omega : 0 < D1)
  by_cases hle : gap v p ≤ 1 / ((N : ℝ) + 1)
  · split_ifs with h
    · refine le_trans hle ?_
      rw [div_le_div_iff₀ (by positivity) hD1pos]
      have h2 : D1 ≤ 2 * N + 2 := by omega
      have h3 : (D1 : ℝ) ≤ 2 * N + 2 := by exact_mod_cast h2
      linarith
    · exact hle
  · have hle' := not_le.mp hle
    obtain ⟨D', h1, h2, h3, h4⟩ := local_max_classify hS v hB p hp hle'
    have hDD : D < D' := by
      by_contra hcon
      have hcon := not_lt.mp hcon
      have h5 := two_div_le_of_le (by omega : 0 < D') hcon
      rw [h4] at hlt
      linarith
    have hD1D' := hD1min D' hDD h3
    split_ifs with h
    · rw [h4]
      exact two_div_le_of_le (by omega) hD1D'
    · exfalso
      omega

/-! ### The replaced vector and monotonicity -/

/-- `ML` of `[N]` with `r` replaced by `w` is `ML` of the deleted vector with `w` appended. -/
theorem ML_wFam_eq_snoc {k N r w : ℕ} (hk : k + 2 = N) (hr : 1 ≤ r) (hN2 : 2 * r ≤ N) :
    ML (wFam (k + 1) r w) = ML (Fin.snoc (bFam k r) (w : ℤ) : Fin (k + 2) → ℤ) := by
  have hB := isB_bFam hk hr hN2
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

/-- Adding an entry never raises `ML`. -/
theorem ML_snoc_le_self {k : ℕ} (v : Fin (k + 1) → ℤ) (z : ℤ) :
    ML (Fin.snoc v z : Fin (k + 2) → ℤ) ≤ ML v := by
  unfold ML
  apply csSup_le (Set.range_nonempty _)
  rintro y ⟨t, rfl⟩
  have h1 : gap (Fin.snoc v z : Fin (k + 2) → ℤ) t ≤ gap v t := by
    apply le_gap
    intro i
    have h := gap_le (Fin.snoc v z : Fin (k + 2) → ℤ) t (Fin.castSucc i)
    rw [snoc_castSucc_eq] at h
    exact h
  exact h1.trans (le_csSup (bddAbove_range_gap v) ⟨t, rfl⟩)

end Gap
end Sext6
end LRSpectrumFull
