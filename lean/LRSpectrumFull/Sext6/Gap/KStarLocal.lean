import LRSpectrumFull.NearestIntCont
import LRSpectrumFull.NearestIntLipschitz
import LRSpectrumFull.Sext6.Gap.KStarCap

/-!
# Theorem K* (feasibility probe), part 2: structure of local maxima (Lemma 1) and `L2([N]) ≤ 1/(N+2)`  [2026-11-25]

Source: the accompanying notes on Theorem K*, Lemma 1 (a)-(d) and Lemma L2b.

For `v : Fin (k+1) → ℤ` with all speeds positive and `≤ M`, and a local maximum `p` of `gap v` with value
`μ = gap v p ∈ (0, 1/2)`:
* `local_max_structure` : there are runners `i, j` with `v i · p ≡ +μ` and `v j · p ≡ -μ (mod 1)` and
  `v i + v j ≤ 2M - 1`;
* `local_max_rational`  : hence `p = a/d` and `μ = b/d` with `0 < d ≤ 2M - 1`;
* `equality_time_rational` : the same for a global maximiser (equality time);
* `L2_vInt_le` : for `[N] = {1..N}` (`N = k+1`) every local-maximum value `< ML` is `≤ 1/(N+2)`.
No `sorry`, no `axiom`.

Convention: `v : Fin (k+1) → ℤ` has `k + 1` speeds and `(v, w) = Fin.snoc v w` has `k + 2`; for the base `[N]` one has `N = k + 1`. Speeds are the moving runners; the runner at rest is not counted, so a vector of `N` speeds means `N + 1` runners and the Lonely Runner value is `1/(N+1)`.
Hypotheses: those of the individual statements (numerical bounds, structural conditions and, where named in the list above, window predicates such as `PrimeWin`, `CopWin`, `PrimeWindow7`, which later modules discharge for explicit ranges). The unproved predicates `DusartPi`, `LRCHyp`, `CopWinHyp` are not hypotheses of any statement in this module.
Axiom audit: covered by `Axioms14` (also reached through the imports of `Axioms15`, `Axioms19`, `Axioms20`) (`#print axioms`; declarations not printed there are bricks of printed ones, so their axioms are bounded by the printed lines).
-/

open Filter Topology

namespace LRSpectrumFull
namespace Sext6
namespace Gap

lemma nid_of_le_half {x : ℝ} (h0 : 0 ≤ x) (h1 : x ≤ 1 / 2) : nearestIntDist x = x := by
  have hx1 : x < 1 := by linarith
  have hf : Int.fract x = x := Int.fract_eq_self.mpr ⟨h0, hx1⟩
  simp only [nearestIntDist, hf]
  exact min_eq_left (by linarith)

/-- A runner sitting at `n - μ` and moved left by `u ≥ 0` is at distance `μ + u` (while `μ + u ≤ 1/2`). -/
lemma nid_minus {z μ u : ℝ} (n : ℤ) (hz : z = n - μ) (hμ : 0 ≤ μ) (hu : 0 ≤ u)
    (hsum : μ + u ≤ 1 / 2) : nearestIntDist (z - u) = μ + u := by
  have h : z - u = -(μ + u) + (n : ℝ) := by rw [hz]; ring
  rw [h, nearestIntDist_add_int, nearestIntDist_neg]
  exact nid_of_le_half (by linarith) hsum

lemma gap_neg {k : ℕ} (v : Fin (k + 1) → ℤ) (x : ℝ) : gap v (-x) = gap v x := by
  simp only [gap, mul_neg, nearestIntDist_neg]

/-- If `gap v` has a local maximum value `μ ∈ (0,1/2)` at `p`, some runner sits at `+μ` (mod 1) at `p`. -/
lemma exists_plus_runner {k : ℕ} (v : Fin (k + 1) → ℤ) (hv : ∀ i, 0 < v i) (p μ : ℝ)
    (hgap : gap v p = μ) (h0 : 0 < μ) (h1 : μ < 1 / 2)
    (hloc : ∀ᶠ x in 𝓝 p, gap v x ≤ μ) :
    ∃ i : Fin (k + 1), ∃ n : ℤ, (v i : ℝ) * p = n + μ := by
  by_contra hno
  have hno' : ∀ i : Fin (k + 1), ∀ n : ℤ, (v i : ℝ) * p ≠ n + μ := fun i n h => hno ⟨i, n, h⟩
  have hrun : ∀ i : Fin (k + 1), ∀ᶠ x in 𝓝[<] p, μ < nearestIntDist ((v i : ℝ) * x) := by
    intro i
    have hge : μ ≤ nearestIntDist ((v i : ℝ) * p) := by
      have := gap_le v p i
      rw [hgap] at this
      exact this
    rcases hge.lt_or_eq with hlt | heq
    · have hc : Continuous fun x : ℝ => nearestIntDist ((v i : ℝ) * x) :=
        continuous_nearestIntDist.comp (continuous_const.mul continuous_id)
      have h : ∀ᶠ x in 𝓝 p, μ < nearestIntDist ((v i : ℝ) * x) :=
        hc.continuousAt.eventually (lt_mem_nhds hlt)
      exact h.filter_mono nhdsWithin_le_nhds
    · obtain ⟨n, hn⟩ := nearestIntDist_eq_abs ((v i : ℝ) * p)
      have hn' : |(v i : ℝ) * p - n| = μ := hn.symm.trans heq.symm
      have hz : (v i : ℝ) * p = n - μ := by
        rcases abs_cases ((v i : ℝ) * p - n) with ⟨ha, hb⟩ | ⟨ha, hb⟩
        · exact absurd (by linarith : (v i : ℝ) * p = n + μ) (hno' i n)
        · linarith
      have hvi : (0 : ℝ) < (v i : ℝ) := by exact_mod_cast hv i
      have hδ : p - (1 / 2 - μ) / (v i : ℝ) < p := by
        have : 0 < (1 / 2 - μ) / (v i : ℝ) := div_pos (by linarith) hvi
        linarith
      filter_upwards [Ioo_mem_nhdsLT hδ] with x hx
      obtain ⟨hx1, hx2⟩ := hx
      have hpx : 0 < p - x := by linarith
      have hu0 : 0 < (v i : ℝ) * (p - x) := mul_pos hvi hpx
      have hu1 : (v i : ℝ) * (p - x) < 1 / 2 - μ := by
        have h2 : p - x < (1 / 2 - μ) / (v i : ℝ) := by linarith
        have h3 := (lt_div_iff₀ hvi).mp h2
        linarith
      have key := nid_minus (z := (v i : ℝ) * p) (μ := μ) (u := (v i : ℝ) * (p - x)) n hz h0.le
        hu0.le (by linarith)
      have e : (v i : ℝ) * x = (v i : ℝ) * p - (v i : ℝ) * (p - x) := by ring
      rw [e, key]
      linarith
  have hall : ∀ᶠ x in 𝓝[<] p, ∀ i : Fin (k + 1), μ < nearestIntDist ((v i : ℝ) * x) :=
    eventually_all.mpr hrun
  have hloc' : ∀ᶠ x in 𝓝[<] p, gap v x ≤ μ := hloc.filter_mono nhdsWithin_le_nhds
  obtain ⟨x, hx1, hx2⟩ := (hall.and hloc').exists
  have hlt : μ < gap v x := by
    unfold gap
    rw [Finset.lt_inf'_iff]
    intro i _
    exact hx1 i
  linarith

/-- Mirror image: some runner sits at `-μ` (mod 1) at `p`. -/
lemma exists_minus_runner {k : ℕ} (v : Fin (k + 1) → ℤ) (hv : ∀ i, 0 < v i) (p μ : ℝ)
    (hgap : gap v p = μ) (h0 : 0 < μ) (h1 : μ < 1 / 2)
    (hloc : ∀ᶠ x in 𝓝 p, gap v x ≤ μ) :
    ∃ j : Fin (k + 1), ∃ m : ℤ, (v j : ℝ) * p = m - μ := by
  have hten : Filter.Tendsto (fun x : ℝ => -x) (𝓝 (-p)) (𝓝 p) := by
    have h := (continuous_neg : Continuous (fun x : ℝ => -x)).tendsto (-p)
    rwa [neg_neg] at h
  have hloc' : ∀ᶠ x in 𝓝 (-p), gap v x ≤ μ := by
    have h := hten.eventually hloc
    exact h.mono fun x hx => by simpa [gap_neg] using hx
  obtain ⟨j, n, hj⟩ := exists_plus_runner v hv (-p) μ (by rw [gap_neg]; exact hgap) h0 h1 hloc'
  refine ⟨j, -n, ?_⟩
  push_cast
  linarith

/-- **Lemma 1(a)(b)(c), structure form.** At a local maximum `p` of `gap v` with value `μ ∈ (0,1/2)` there are
runners `i, j` with `v i p ≡ +μ`, `v j p ≡ -μ (mod 1)`, and `v i + v j ≤ 2M - 1`. -/
theorem local_max_structure {k : ℕ} (v : Fin (k + 1) → ℤ) (hv : ∀ i, 0 < v i) (M : ℤ)
    (hM : ∀ i, v i ≤ M) (p : ℝ) (hp : IsLocalMax (gap v) p)
    (h0 : 0 < gap v p) (h1 : gap v p < 1 / 2) :
    ∃ i j : Fin (k + 1), ∃ n m : ℤ, (v i : ℝ) * p = n + gap v p ∧ (v j : ℝ) * p = m - gap v p ∧
      v i + v j ≤ 2 * M - 1 := by
  have hloc : ∀ᶠ x in 𝓝 p, gap v x ≤ gap v p := hp
  obtain ⟨i, n, hi⟩ := exists_plus_runner v hv p _ rfl h0 h1 hloc
  obtain ⟨j, m, hj⟩ := exists_minus_runner v hv p _ rfl h0 h1 hloc
  refine ⟨i, j, n, m, hi, hj, ?_⟩
  have hne : v i ≠ v j := by
    intro heq
    have hij : (n : ℝ) + gap v p = m - gap v p := by rw [← hi, ← hj, heq]
    have h2 : (n : ℝ) < m := by linarith
    have h3 : (m : ℝ) < n + 1 := by linarith
    have h4 : n < m := by exact_mod_cast h2
    have h5 : m < n + 1 := by exact_mod_cast h3
    omega
  have := hM i
  have := hM j
  omega

/-- **Lemma 1(c), rational form.** `p = a/d` and `gap v p = b/d` with `0 < d ≤ 2M - 1`. -/
theorem local_max_rational {k : ℕ} (v : Fin (k + 1) → ℤ) (hv : ∀ i, 0 < v i) (M : ℤ)
    (hM : ∀ i, v i ≤ M) (p : ℝ) (hp : IsLocalMax (gap v) p)
    (h0 : 0 < gap v p) (h1 : gap v p < 1 / 2) :
    ∃ (a : ℤ) (d : ℕ), 0 < d ∧ (d : ℤ) ≤ 2 * M - 1 ∧ p = a / d ∧
      ∃ b : ℤ, gap v p = b / d := by
  obtain ⟨i, j, n, m, hi, hj, hsum⟩ := local_max_structure v hv M hM p hp h0 h1
  have hpos : 0 < v i + v j := by have := hv i; have := hv j; omega
  obtain ⟨d, hd⟩ : ∃ d : ℕ, (d : ℤ) = v i + v j := ⟨(v i + v j).toNat, Int.toNat_of_nonneg hpos.le⟩
  have hdR : (d : ℝ) = (v i : ℝ) + (v j : ℝ) := by exact_mod_cast hd
  have hd0 : 0 < d := by omega
  have hdne : (d : ℝ) ≠ 0 := by exact_mod_cast hd0.ne'
  have hpd : p * ((v i : ℝ) + (v j : ℝ)) = (n : ℝ) + m := by linear_combination hi + hj
  refine ⟨n + m, d, hd0, by omega, ?_, v i * (n + m) - n * (v i + v j), ?_⟩
  · rw [eq_div_iff hdne, hdR]
    push_cast
    exact hpd
  · rw [eq_div_iff hdne, hdR]
    push_cast
    linear_combination (-((v i : ℝ) + (v j : ℝ))) * hi + (v i : ℝ) * hpd

/-- A global maximiser of `gap v` (an equality time) is a local maximum. -/
theorem isLocalMax_of_eq_ML {k : ℕ} (v : Fin (k + 1) → ℤ) (p : ℝ) (h : gap v p = ML v) :
    IsLocalMax (gap v) p :=
  by
  unfold IsLocalMax IsMaxFilter
  refine Filter.Eventually.of_forall fun x => ?_
  have hx : gap v x ≤ ML v := le_csSup (bddAbove_range_gap v) ⟨x, rfl⟩
  rw [h]
  exact hx

/-- **Lemma 1(d).** An equality time `p` (`gap v p = ML v`, `0 < ML v < 1/2`) is `a/d` with `d ≤ 2M - 1`,
and `ML v = b/d`. -/
theorem equality_time_rational {k : ℕ} (v : Fin (k + 1) → ℤ) (hv : ∀ i, 0 < v i) (M : ℤ)
    (hM : ∀ i, v i ≤ M) (p : ℝ) (hp : gap v p = ML v) (h0 : 0 < ML v) (h1 : ML v < 1 / 2) :
    ∃ (a : ℤ) (d : ℕ), 0 < d ∧ (d : ℤ) ≤ 2 * M - 1 ∧ p = a / d ∧ ∃ b : ℤ, ML v = b / d := by
  have := local_max_rational v hv M hM p (isLocalMax_of_eq_ML v p hp) (by rw [hp]; exact h0)
    (by rw [hp]; exact h1)
  obtain ⟨a, d, hd, hdM, hpa, b, hb⟩ := this
  exact ⟨a, d, hd, hdM, hpa, b, hp.symm.trans hb⟩

/-! ### The base `[N] = {1, …, N}` with `N = k + 1` -/

/-- The speed vector `(1, 2, …, k+1)`. -/
def vInt (k : ℕ) : Fin (k + 1) → ℤ := fun i => ((i : ℕ) : ℤ) + 1

theorem vInt_pos (k : ℕ) : ∀ i, 0 < vInt k i := by
  intro i
  show 0 < ((i : ℕ) : ℤ) + 1
  positivity

theorem vInt_le (k : ℕ) : ∀ i, vInt k i ≤ (k : ℤ) + 1 := by
  intro i
  show ((i : ℕ) : ℤ) + 1 ≤ (k : ℤ) + 1
  have := i.isLt
  omega

/-- Dirichlet: `ML [N] ≤ 1/(N+1)` (here `N = k+1`). -/
theorem ML_vInt_le (k : ℕ) : ML (vInt k) ≤ 1 / ((k : ℝ) + 2) := by
  apply ML_le_of_cover
  intro t
  obtain ⟨j, q, hq0, hqN, hqd⟩ := Real.exists_int_int_abs_mul_sub_le t (n := k + 1) (by omega)
  lift q to ℕ using hq0.le
  have hq1 : q - 1 < k + 1 := by push_cast at hqN; omega
  refine ⟨⟨q - 1, hq1⟩, ?_⟩
  have hqq : vInt k ⟨q - 1, hq1⟩ = (q : ℤ) := by
    show (((q - 1 : ℕ) : ℤ) + 1 = (q : ℤ))
    have : 0 < q := by exact_mod_cast hq0
    omega
  rw [hqq]
  refine (nearestIntDist_le_dist _ j).trans ?_
  calc |((q : ℤ) : ℝ) * t - j| ≤ 1 / (((k + 1 : ℕ) : ℝ) + 1) := hqd
    _ = 1 / ((k : ℝ) + 2) := by
      have e : (((k + 1 : ℕ) : ℝ) + 1) = (k : ℝ) + 2 := by
        first | (push_cast; ring) | push_cast
      rw [e]

/-- **`L2([N]) ≤ 1/(N+2)`** (the accompanying notes Lemma L2b, five-line proof): every local-maximum value of `gap [N]`
that is below `ML [N]` is at most `1/(N+2)` (`N = k+1`, so `N + 2 = k + 3`). -/
theorem L2_vInt_le (k : ℕ) (p : ℝ) (hp : IsLocalMax (gap (vInt k)) p)
    (hlt : gap (vInt k) p < ML (vInt k)) : gap (vInt k) p ≤ 1 / ((k : ℝ) + 3) := by
  have hk3 : (0 : ℝ) < (k : ℝ) + 3 := by positivity
  rcases (gap_nonneg (vInt k) p).eq_or_lt with h0 | h0
  · rw [← h0]; positivity
  have hML := ML_vInt_le k
  have hk2 : (0 : ℝ) < (k : ℝ) + 2 := by positivity
  have hhalf : 1 / ((k : ℝ) + 2) ≤ 1 / 2 := by
    apply one_div_le_one_div_of_le (by norm_num)
    have : (0 : ℝ) ≤ k := Nat.cast_nonneg k
    linarith
  have hμ1 : gap (vInt k) p < 1 / ((k : ℝ) + 2) := lt_of_lt_of_le hlt hML
  obtain ⟨a, d, hd, hdM, hpa, b, hb⟩ :=
    local_max_rational (vInt k) (vInt_pos k) ((k : ℤ) + 1) (vInt_le k) p hp h0 (by linarith)
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  rw [hb] at hμ1 h0 ⊢
  have hb0 : 0 < b := by
    have : (0 : ℝ) < b := (div_pos_iff_of_pos_right hdR).mp h0
    exact_mod_cast this
  have hbd : (b : ℝ) * ((k : ℝ) + 2) < d := by
    rw [div_lt_div_iff₀ hdR hk2] at hμ1
    linarith
  have hbd' : b * ((k : ℤ) + 2) < d := by exact_mod_cast hbd
  have hb1 : b = 1 := by
    by_contra hne
    have h2 : 2 ≤ b := by omega
    have : (0 : ℤ) ≤ k := by positivity
    nlinarith [mul_nonneg (sub_nonneg.mpr h2) (by positivity : (0 : ℤ) ≤ (k : ℤ) + 2)]
  subst hb1
  have hd3 : (k : ℤ) + 3 ≤ d := by omega
  have hd3R : (k : ℝ) + 3 ≤ d := by exact_mod_cast hd3
  push_cast
  exact one_div_le_one_div_of_le hk3 hd3R

end Gap
end Sext6
end LRSpectrumFull
