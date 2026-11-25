import LRSpectrumFull.Sext6.Gap.KStarUpper
import LRSpectrumFull.Sext6.Gap.KStarLower

/-!
# Theorem K*, part 6: assembly (E), the value `vμ`, and the explicit threshold `w ≥ 2 M^3`  [2026-11-25]

Source: the accompanying notes on Theorem K*, sections 0, 4.

* `K_eq`       : (E) with explicit data: (U) + (L) give `ML (v, w) = w L / (w + vμ)` when `L2 ≤ K`.
* `exists_vmu` : the speed `vμ` of the accompanying notes exists: the minimum, over equality times and sides, of the fastest
                 runner at that side; stated through its two defining properties (V1) and (V2).
* `local_max_gap_bound` : Lemma 1(c) gap: every local-maximum value below `ML` is `≤ ML - 1/(2M-1)^2`.
* `Kstar_E`    : Lemma 6 + (E): for every `w ≥ 2 M^3` with `w p ∈ ℤ` at all equality times,
                 `ML (v, w) = w · ML v / (w + vμ)`.
No `sorry`, no `axiom`.

Convention: `v : Fin (k+1) → ℤ` has `k + 1` speeds and `(v, w) = Fin.snoc v w` has `k + 2`; for the base `[N]` one has `N = k + 1`. Speeds are the moving runners; the runner at rest is not counted, so a vector of `N` speeds means `N + 1` runners and the Lonely Runner value is `1/(N+1)`.
Hypotheses: those of the individual statements (numerical bounds, structural conditions and, where named in the list above, window predicates such as `PrimeWin`, `CopWin`, `PrimeWindow7`, which later modules discharge for explicit ranges). The unproved predicates `DusartPi`, `LRCHyp`, `CopWinHyp` are not hypotheses of any statement in this module.
Axiom audit: covered by `Axioms15` (also reached through the imports of `Axioms19`, `Axioms20`) (`#print axioms`; declarations not printed there are bricks of printed ones, so their axioms are bounded by the printed lines).
-/

namespace LRSpectrumFull
namespace Sext6
namespace Gap

/-! ### (E) with explicit data -/

theorem K_eq {k : ℕ} (v : Fin (k + 1) → ℤ) (hv : ∀ i, 0 < v i) (M : ℤ) (hM : ∀ i, v i ≤ M)
    (w : ℤ) (hw : 0 < w) (L vμ L2 : ℝ) (hLML : L = ML v) (hL0 : 0 < L) (hL1 : L < 1 / 2)
    (hvμ : 0 < vμ)
    (hV1 : ∀ p, gap v p = L →
      (∃ i : Fin (k + 1), ∃ n : ℤ, vμ ≤ (v i : ℝ) ∧ (v i : ℝ) * p = n + L) ∧
      (∃ j : Fin (k + 1), ∃ m : ℤ, vμ ≤ (v j : ℝ) ∧ (v j : ℝ) * p = m - L))
    (hL2 : ∀ p, IsLocalMax (gap v) p → gap v p < L → gap v p ≤ L2)
    (hDw : ∀ p, gap v p = L → ∃ z : ℤ, (w : ℝ) * p = z)
    (d : ℕ) (hd : 0 < d) (a l : ℤ) (hLl : L = (l : ℝ) / d) (hat0 : gap v ((a : ℝ) / d) = L)
    (hext : (∀ i (m : ℤ), (v i : ℝ) * ((a : ℝ) / d) = m - L → (v i : ℝ) ≤ vμ) ∨
            (∀ i (n : ℤ), (v i : ℝ) * ((a : ℝ) / d) = n + L → (v i : ℝ) ≤ vμ))
    (hsize : L * d * M ≤ (w : ℝ) + vμ)
    (hK : L2 ≤ (w : ℝ) * L / ((w : ℝ) + vμ)) :
    ML (Fin.snoc v w : Fin (k + 2) → ℤ) = (w : ℝ) * L / ((w : ℝ) + vμ) := by
  apply le_antisymm
  · have h := K_upper v hv w hw L vμ L2 hLML hL0 hL1.le hvμ hV1 hL2 hDw
    rw [max_eq_left hK] at h
    exact h
  · have hfar : ∀ i, L ≤ nearestIntDist ((v i : ℝ) * ((a : ℝ) / d)) := by
      intro i
      have h1 := gap_le v ((a : ℝ) / d) i
      rw [hat0] at h1
      exact h1
    have hwt0 := hDw _ hat0
    rcases hext with hm | hn
    · exact K_lower v hv M hM w hw L vμ d hd a l hLl hL0 hL1 hvμ hfar hm hwt0 hsize
    · exact K_lower_plus v hv M hM w hw L vμ d hd a l hLl hL0 hL1 hvμ hfar hn hwt0 hsize

/-! ### The speed `vμ` -/

/-- A runner sitting at `+L` (mod 1) at time `p`. -/
def PlusRun {k : ℕ} (v : Fin (k + 1) → ℤ) (L p : ℝ) (i : Fin (k + 1)) : Prop :=
  ∃ n : ℤ, (v i : ℝ) * p = n + L

/-- A runner sitting at `-L` (mod 1) at time `p`. -/
def MinusRun {k : ℕ} (v : Fin (k + 1) → ℤ) (L p : ℝ) (i : Fin (k + 1)) : Prop :=
  ∃ m : ℤ, (v i : ℝ) * p = m - L

/-- The set of attained "top speeds": the speed of the fastest runner at one side of an equality time. -/
def TopSet {k : ℕ} (v : Fin (k + 1) → ℤ) (L : ℝ) : Set ℕ :=
  {m | ∃ p, gap v p = L ∧
    ((∃ i, PlusRun v L p i ∧ (v i).toNat = m ∧ ∀ i', PlusRun v L p i' → v i' ≤ v i) ∨
     (∃ j, MinusRun v L p j ∧ (v j).toNat = m ∧ ∀ j', MinusRun v L p j' → v j' ≤ v j))}

lemma exists_top {k : ℕ} (v : Fin (k + 1) → ℤ) (P : Fin (k + 1) → Prop) (h : ∃ i, P i) :
    ∃ i, P i ∧ ∀ i', P i' → v i' ≤ v i := by
  classical
  obtain ⟨i0, hi0⟩ := h
  obtain ⟨x, hx, hmax⟩ := Finset.exists_max_image (Finset.univ.filter P) v
    ⟨i0, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi0⟩⟩
  exact ⟨x, (Finset.mem_filter.mp hx).2, fun i' hi' =>
    hmax i' (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi'⟩)⟩

/-- **The speed `vμ`** of the accompanying notes section 0 (the minimum, over equality times `t_j` and both sides, of the
fastest runner at that side), characterised by (V1) every equality time has a runner at `+L` and one at `-L`
of speed `≥ vμ`, and (V2) at some equality time all runners at one side have speed `≤ vμ`. -/
theorem exists_vmu {k : ℕ} (v : Fin (k + 1) → ℤ) (hv : ∀ i, 0 < v i) (M : ℤ)
    (hM : ∀ i, v i ≤ M) (hL0 : 0 < ML v) (hL1 : ML v < 1 / 2) :
    ∃ vμ : ℕ, 0 < vμ ∧
      (∀ p, gap v p = ML v →
        (∃ i : Fin (k + 1), ∃ n : ℤ, (vμ : ℝ) ≤ (v i : ℝ) ∧ (v i : ℝ) * p = n + ML v) ∧
        (∃ j : Fin (k + 1), ∃ m : ℤ, (vμ : ℝ) ≤ (v j : ℝ) ∧ (v j : ℝ) * p = m - ML v)) ∧
      ∃ t0, gap v t0 = ML v ∧
        ((∀ i (m : ℤ), (v i : ℝ) * t0 = m - ML v → (v i : ℝ) ≤ vμ) ∨
         (∀ i (n : ℤ), (v i : ℝ) * t0 = n + ML v → (v i : ℝ) ≤ vμ)) := by
  obtain ⟨p0, _, hp0⟩ := exists_gap_eq_ML v
  have hstruct : ∀ p, gap v p = ML v →
      (∃ i, PlusRun v (ML v) p i) ∧ (∃ j, MinusRun v (ML v) p j) := by
    intro p hp
    obtain ⟨i, j, n, m, hi, hj, -⟩ := local_max_structure v hv M hM p
      (isLocalMax_of_eq_ML v p hp) (by rw [hp]; exact hL0) (by rw [hp]; exact hL1)
    rw [hp] at hi hj
    exact ⟨⟨i, n, hi⟩, ⟨j, m, hj⟩⟩
  have hcast : ∀ i : Fin (k + 1), (((v i).toNat : ℕ) : ℤ) = v i :=
    fun i => Int.toNat_of_nonneg (hv i).le
  have hne : (TopSet v (ML v)).Nonempty := by
    obtain ⟨i, hi, htop⟩ := exists_top v (PlusRun v (ML v) p0) (hstruct p0 hp0).1
    exact ⟨(v i).toNat, p0, hp0, Or.inl ⟨i, hi, rfl, htop⟩⟩
  have hmem : sInf (TopSet v (ML v)) ∈ TopSet v (ML v) := Nat.sInf_mem hne
  refine ⟨sInf (TopSet v (ML v)), ?_, ?_, ?_⟩
  · obtain ⟨t0, ht0, hcase⟩ := hmem
    rcases hcase with ⟨i, _, hi, _⟩ | ⟨j, _, hj, _⟩
    · have := hv i
      omega
    · have := hv j
      omega
  · intro p hp
    obtain ⟨⟨i0, hi0⟩, ⟨j0, hj0⟩⟩ := hstruct p hp
    obtain ⟨i, hi, htop⟩ := exists_top v (PlusRun v (ML v) p) ⟨i0, hi0⟩
    obtain ⟨j, hj, htopj⟩ := exists_top v (MinusRun v (ML v) p) ⟨j0, hj0⟩
    have hmi : (v i).toNat ∈ TopSet v (ML v) := ⟨p, hp, Or.inl ⟨i, hi, rfl, htop⟩⟩
    have hmj : (v j).toNat ∈ TopSet v (ML v) := ⟨p, hp, Or.inr ⟨j, hj, rfl, htopj⟩⟩
    have h1 := Nat.sInf_le hmi
    have h2 := Nat.sInf_le hmj
    obtain ⟨n, hn⟩ := hi
    obtain ⟨m, hm⟩ := hj
    have h1' : ((sInf (TopSet v (ML v)) : ℕ) : ℤ) ≤ v i := by
      have := hcast i
      omega
    have h2' : ((sInf (TopSet v (ML v)) : ℕ) : ℤ) ≤ v j := by
      have := hcast j
      omega
    refine ⟨⟨i, n, ?_, hn⟩, ⟨j, m, ?_, hm⟩⟩
    · exact_mod_cast h1'
    · exact_mod_cast h2'
  · obtain ⟨t0, ht0, hcase⟩ := hmem
    refine ⟨t0, ht0, ?_⟩
    rcases hcase with ⟨i, hi, hei, htop⟩ | ⟨j, hj, hej, htop⟩
    · right
      intro i' n hn
      have h1 := htop i' ⟨n, hn⟩
      have h2 : v i' ≤ ((sInf (TopSet v (ML v)) : ℕ) : ℤ) := by
        have := hcast i
        omega
      exact_mod_cast h2
    · left
      intro j' m hm
      have h1 := htop j' ⟨m, hm⟩
      have h2 : v j' ≤ ((sInf (TopSet v (ML v)) : ℕ) : ℤ) := by
        have := hcast j
        omega
      exact_mod_cast h2

/-! ### Lemma 6: the explicit threshold -/

lemma sep_bound (b b' : ℤ) (d d' : ℕ) (M : ℤ) (hd : 0 < d) (hd' : 0 < d')
    (hdM : (d : ℤ) ≤ 2 * M - 1) (hd'M : (d' : ℤ) ≤ 2 * M - 1)
    (hlt : (b' : ℝ) / d' < (b : ℝ) / d) :
    1 / ((2 * (M : ℝ) - 1) ^ 2) ≤ (b : ℝ) / d - (b' : ℝ) / d' := by
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have hd'R : (0 : ℝ) < d' := by exact_mod_cast hd'
  have hdM' : (d : ℝ) ≤ 2 * M - 1 := by exact_mod_cast hdM
  have hd'M' : (d' : ℝ) ≤ 2 * M - 1 := by exact_mod_cast hd'M
  have h1 : (b' : ℝ) * d < b * d' := by
    rw [div_lt_div_iff₀ hd'R hdR] at hlt
    exact hlt
  have h2 : b' * (d : ℤ) < b * (d' : ℤ) := by exact_mod_cast h1
  have h3 : (1 : ℤ) ≤ b * (d' : ℤ) - b' * (d : ℤ) := by linarith
  have h4 : (1 : ℝ) ≤ (b : ℝ) * d' - b' * d := by exact_mod_cast h3
  have hpos : (0 : ℝ) < (d : ℝ) * d' := mul_pos hdR hd'R
  have hprod : (d : ℝ) * d' ≤ (2 * (M : ℝ) - 1) ^ 2 := by
    have := mul_le_mul hdM' hd'M' hd'R.le (by linarith)
    calc (d : ℝ) * d' ≤ (2 * (M : ℝ) - 1) * (2 * (M : ℝ) - 1) := this
      _ = (2 * (M : ℝ) - 1) ^ 2 := by ring
  have h5 : 1 / ((2 * (M : ℝ) - 1) ^ 2) ≤ 1 / ((d : ℝ) * d') :=
    one_div_le_one_div_of_le hpos hprod
  have h6 : 1 / ((d : ℝ) * d') ≤ (b : ℝ) / d - (b' : ℝ) / d' := by
    rw [div_le_iff₀ hpos]
    have e : ((b : ℝ) / d - (b' : ℝ) / d') * ((d : ℝ) * d') = b * d' - b' * d := by
      field_simp <;> ring
    linarith
  linarith

/-- Lemma 1(c) separation: every local-maximum value below `ML` is at most `ML - 1/(2M-1)^2`. -/
theorem local_max_gap_bound {k : ℕ} (v : Fin (k + 1) → ℤ) (hv : ∀ i, 0 < v i) (M : ℤ)
    (hM : ∀ i, v i ≤ M) (hL0 : 0 < ML v) (hL1 : ML v < 1 / 2)
    (p : ℝ) (hp : IsLocalMax (gap v) p) (hlt : gap v p < ML v) :
    gap v p ≤ ML v - 1 / ((2 * (M : ℝ) - 1) ^ 2) := by
  obtain ⟨p0, _, hp0⟩ := exists_gap_eq_ML v
  obtain ⟨a, d, hd, hdM, _, b, hb⟩ := equality_time_rational v hv M hM p0 hp0 hL0 hL1
  rcases (gap_nonneg v p).eq_or_lt with h0 | h0
  · have key := sep_bound b 0 d 1 M hd one_pos hdM (by omega)
      (by rw [← hb]; simpa using hL0)
    rw [← hb] at key
    simp only [Int.cast_zero, Nat.cast_one, div_one, sub_zero] at key
    rw [← h0]
    linarith
  · obtain ⟨a', d', hd', hd'M, _, b', hb'⟩ :=
      local_max_rational v hv M hM p hp h0 (lt_trans hlt hL1)
    have key := sep_bound b b' d d' M hd hd' hdM hd'M (by rw [← hb, ← hb']; exact hlt)
    rw [← hb, ← hb'] at key
    linarith

lemma size_bound (L vμ : ℝ) (hL0 : 0 ≤ L) (hL1 : L < 1 / 2) (hvμ : 0 ≤ vμ) (d : ℕ) (M w : ℤ)
    (hdM : (d : ℤ) ≤ 2 * M - 1) (hM1 : 1 ≤ M) (hw : 2 * M ^ 3 ≤ w) :
    L * d * M ≤ (w : ℝ) + vμ := by
  have hdR : (d : ℝ) ≤ 2 * M - 1 := by exact_mod_cast hdM
  have hMR : (1 : ℝ) ≤ M := by exact_mod_cast hM1
  have hwR : 2 * (M : ℝ) ^ 3 ≤ w := by exact_mod_cast hw
  have h1 : L * d ≤ (1 / 2) * (2 * M - 1) :=
    mul_le_mul hL1.le hdR (Nat.cast_nonneg d) (by norm_num)
  have h2 : L * d * M ≤ (1 / 2) * (2 * (M : ℝ) - 1) * M :=
    mul_le_mul_of_nonneg_right h1 (by linarith)
  have h3 : (M : ℝ) ^ 2 ≤ (M : ℝ) ^ 3 := by
    nlinarith [mul_nonneg (sq_nonneg (M : ℝ)) (sub_nonneg.mpr hMR)]
  have h4 : 0 ≤ (M : ℝ) ^ 3 := pow_nonneg (by linarith) 3
  nlinarith

lemma K_ge_L2 (L vμ : ℝ) (hL0 : 0 < L) (hL1 : L < 1 / 2) (hvμ : 0 < vμ) (M w : ℤ)
    (hvμM : vμ ≤ M) (hM1 : 1 ≤ M) (hw : 2 * M ^ 3 ≤ w) :
    L - 1 / ((2 * (M : ℝ) - 1) ^ 2) ≤ (w : ℝ) * L / ((w : ℝ) + vμ) := by
  have hMR : (1 : ℝ) ≤ M := by exact_mod_cast hM1
  have hwR : 2 * (M : ℝ) ^ 3 ≤ w := by exact_mod_cast hw
  have hpos2 : (0 : ℝ) < 2 * M - 1 := by linarith
  have hw0 : (0 : ℝ) < w := by
    have : (0 : ℝ) < (M : ℝ) ^ 3 := pow_pos (by linarith) 3
    linarith
  have hwv : (0 : ℝ) < (w : ℝ) + vμ := by linarith
  obtain ⟨q, hqdef⟩ : ∃ q : ℝ, q = 1 / ((2 * (M : ℝ) - 1) ^ 2) := ⟨_, rfl⟩
  have hq0 : 0 ≤ q := by rw [hqdef]; positivity
  have hq : q * (2 * (M : ℝ) - 1) ^ 2 = 1 := by
    rw [hqdef]
    exact one_div_mul_cancel (pow_ne_zero 2 hpos2.ne')
  rw [← hqdef, le_div_iff₀ hwv]
  have h1 : vμ * L ≤ (M : ℝ) * (1 / 2) := mul_le_mul hvμM hL1.le hL0.le (by linarith)
  have h2 : (2 * (M : ℝ) - 1) ^ 2 ≤ 4 * (M : ℝ) ^ 2 := by nlinarith
  have h3 : vμ * L * (2 * (M : ℝ) - 1) ^ 2 ≤ ((M : ℝ) * (1 / 2)) * (4 * (M : ℝ) ^ 2) :=
    mul_le_mul h1 h2 (sq_nonneg _) (by linarith)
  have h4 : vμ * L * (2 * (M : ℝ) - 1) ^ 2 ≤ (w : ℝ) + vμ := by linarith
  have h5 : q * (vμ * L * (2 * (M : ℝ) - 1) ^ 2) ≤ q * ((w : ℝ) + vμ) :=
    mul_le_mul_of_nonneg_left h4 hq0
  have h6 : q * (vμ * L * (2 * (M : ℝ) - 1) ^ 2) = vμ * L := by
    calc q * (vμ * L * (2 * (M : ℝ) - 1) ^ 2) = vμ * L * (q * (2 * (M : ℝ) - 1) ^ 2) := by ring
      _ = vμ * L := by rw [hq]; ring
  linarith

/-- **Theorem K\*(E) with the explicit threshold.**  Let `v` be positive integer speeds bounded by `M` with
`0 < ML v < 1/2`.  There is a positive integer `vμ` (characterised by (V1), (V2); it is the speed `vμ` of
the accompanying notes) such that for every integer `w ≥ 2 M^3` with `w p ∈ ℤ` at every equality time `p`
(this is `D ∣ w`), `ML (v, w) = w · ML v / (w + vμ)`. -/
theorem Kstar_E {k : ℕ} (v : Fin (k + 1) → ℤ) (hv : ∀ i, 0 < v i) (M : ℤ) (hM : ∀ i, v i ≤ M)
    (hL0 : 0 < ML v) (hL1 : ML v < 1 / 2) :
    ∃ vμ : ℕ, 0 < vμ ∧
      (∀ p, gap v p = ML v →
        (∃ i : Fin (k + 1), ∃ n : ℤ, (vμ : ℝ) ≤ (v i : ℝ) ∧ (v i : ℝ) * p = n + ML v) ∧
        (∃ j : Fin (k + 1), ∃ m : ℤ, (vμ : ℝ) ≤ (v j : ℝ) ∧ (v j : ℝ) * p = m - ML v)) ∧
      (∃ t0, gap v t0 = ML v ∧
        ((∀ i (m : ℤ), (v i : ℝ) * t0 = m - ML v → (v i : ℝ) ≤ vμ) ∨
         (∀ i (n : ℤ), (v i : ℝ) * t0 = n + ML v → (v i : ℝ) ≤ vμ))) ∧
      ∀ w : ℤ, 2 * M ^ 3 ≤ w → (∀ p, gap v p = ML v → ∃ z : ℤ, (w : ℝ) * p = z) →
        ML (Fin.snoc v w : Fin (k + 2) → ℤ) = (w : ℝ) * ML v / ((w : ℝ) + vμ) := by
  obtain ⟨vμ, hpos, hV1, t0, ht0, hext⟩ := exists_vmu v hv M hM hL0 hL1
  refine ⟨vμ, hpos, hV1, ⟨t0, ht0, hext⟩, ?_⟩
  intro w hw2 hDw
  have hM1 : 1 ≤ M := by
    have := hv 0
    have := hM 0
    omega
  have hMpos : 0 < M := by omega
  have hw : 0 < w := lt_of_lt_of_le (by positivity) hw2
  have hvμR : (0 : ℝ) < vμ := by exact_mod_cast hpos
  obtain ⟨a, d, hd, hdM, hpa, b, hb⟩ := equality_time_rational v hv M hM t0 ht0 hL0 hL1
  subst hpa
  have hvμM : (vμ : ℝ) ≤ M := by
    obtain ⟨⟨i, n, hi, _⟩, _⟩ := hV1 _ ht0
    have h1 : (v i : ℝ) ≤ M := by exact_mod_cast hM i
    linarith
  refine K_eq v hv M hM w hw (ML v) vμ (ML v - 1 / ((2 * (M : ℝ) - 1) ^ 2)) rfl hL0 hL1 hvμR hV1
    (fun p hp hlt => local_max_gap_bound v hv M hM hL0 hL1 p hp hlt) hDw d hd a b hb ht0 hext
    (size_bound (ML v) vμ hL0.le hL1 hvμR.le d M w hdM hM1 hw2)
    (K_ge_L2 (ML v) vμ hL0 hL1 hvμR M w hvμM hM1 hw2)

end Gap
end Sext6
end LRSpectrumFull
