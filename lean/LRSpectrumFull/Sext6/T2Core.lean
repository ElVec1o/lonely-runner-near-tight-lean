/-
# T2Core: coalescing, transfer, and the two-direction bound 

Central idea: two integer vectors `v` and `w` (with `w` a rounding of `t v`) span a plane; in that plane one
can pick a direction `u = α v + β w` in which two of the six speeds coalesce (same absolute value) and no
speed vanishes, so `LRC 5` bounds `ML u`; the rounding error moves the answer by at most half of it.

Statements (all with `LRC 5` as the only hypothesis where a hypothesis is needed):
* `coalesce`      : planar form of YGB Lemma 11.2 (pure integer geometry, signs of 2x2 determinants).
* `ML_transfer`   : `ML u - δ/2 <= ML v`   (YGB Lemma 11.3(b) for one vector).
* `LRC5_collision`: `LRC 5` gives `ML u >= 1/6` for six nonzero speeds with two equal absolute values.
* `two_dir`       : `ML v >= 1/6 - δ/2` when `w` is a `δ`-rounding of `t v` not parallel to `v`.
-/
import LRSpectrumFull.Sext6.Height
import LRSpectrumFull.Sext6.Dilation

namespace LRSpectrumFull
namespace Sext6

/-! ### nearest-integer distance helpers -/

theorem nid_eq_abs_round (x : ℝ) : nearestIntDist x = |x - ((round x : ℤ) : ℝ)| := by
  unfold nearestIntDist
  exact (abs_sub_round_eq_min x).symm

theorem nid_add_le (x y : ℝ) : nearestIntDist (x + y) ≤ nearestIntDist x + |y| := by
  rw [nid_eq_abs_round x]
  calc nearestIntDist (x + y) ≤ |x + y - ((round x : ℤ) : ℝ)| := nearestIntDist_le_dist _ _
    _ = |(x - ((round x : ℤ) : ℝ)) + y| := by congr 1; ring
    _ ≤ |x - ((round x : ℤ) : ℝ)| + |y| := abs_add_le _ _

theorem nid_abs_int (z : ℤ) (t : ℝ) :
    nearestIntDist (((|z| : ℤ) : ℝ) * t) = nearestIntDist ((z : ℝ) * t) := by
  rcases abs_choice z with h | h
  · rw [h]
  · rw [h]
    have : (((-z : ℤ) : ℝ) * t) = -((z : ℝ) * t) := by push_cast; ring
    rw [this, nearestIntDist_neg]

/-! ### transfer -/

theorem ML_transfer {k : ℕ} (v w : Fin (k + 1) → ℤ) (α β : ℤ) (t δ : ℝ)
    (he : ∀ i, |(w i : ℝ) - t * v i| ≤ δ) :
    ML (fun i => α * v i + β * w i) - δ / 2 ≤ ML v := by
  have hδ : 0 ≤ δ := le_trans (abs_nonneg _) (he 0)
  have hge : ∀ ts : ℝ, gap (fun i => α * v i + β * w i) ts - δ / 2 ≤ ML v := by
    intro ts
    obtain ⟨c, hc⟩ : ∃ c : ℤ, c = round (ts * β) := ⟨_, rfl⟩
    have hb' : |ts * β - c| ≤ 1 / 2 := by rw [hc]; exact abs_sub_round _
    obtain ⟨s, hs⟩ : ∃ s : ℝ, s = ts * α + (ts * β - c) * t := ⟨_, rfl⟩
    have key : ∀ i, gap (fun i => α * v i + β * w i) ts - δ / 2 ≤ nearestIntDist ((v i : ℝ) * s) := by
      intro i
      have h1 := gap_le (fun i => α * v i + β * w i) ts i
      have hrep : (((α * v i + β * w i : ℤ) : ℝ) * ts) =
          ((v i : ℝ) * s + (ts * β - c) * ((w i : ℝ) - t * v i)) + ((c * w i : ℤ) : ℝ) := by
        rw [hs]; push_cast; ring
      have h2 : nearestIntDist (((α * v i + β * w i : ℤ) : ℝ) * ts) ≤
          nearestIntDist ((v i : ℝ) * s) + δ / 2 := by
        rw [hrep, nearestIntDist_add_int]
        refine (nid_add_le _ _).trans ?_
        have h3 : |(ts * β - c) * ((w i : ℝ) - t * v i)| ≤ δ / 2 := by
          rw [abs_mul]
          calc |ts * β - c| * |(w i : ℝ) - t * v i| ≤ (1 / 2) * δ :=
                mul_le_mul hb' (he i) (abs_nonneg _) (by norm_num)
            _ = δ / 2 := by ring
        linarith
      simp only at h1
      linarith
    have : gap (fun i => α * v i + β * w i) ts - δ / 2 ≤ gap v s := le_gap v s _ key
    exact this.trans (le_csSup (bddAbove_range_gap v) ⟨s, rfl⟩)
  have : ML (fun i => α * v i + β * w i) ≤ ML v + δ / 2 :=
    csSup_le (Set.range_nonempty _) (by rintro y ⟨ts, rfl⟩; linarith [hge ts])
  linarith

/-! ### planar coalescing -/

/-- `(x, y)` lies in the half-plane `{y > 0} ∪ {y = 0, x > 0}`. -/
def InH (x y : ℤ) : Prop := 0 < y ∨ (y = 0 ∧ 0 < x)

theorem det_trans {x1 y1 x2 y2 x3 y3 : ℤ} (h1 : InH x1 y1) (h2 : InH x2 y2) (h3 : InH x3 y3)
    (a : 0 ≤ x1 * y2 - y1 * x2) (b : 0 ≤ x2 * y3 - y2 * x3) : 0 ≤ x1 * y3 - y1 * x3 := by
  rcases h2 with h2 | ⟨h2, h2'⟩
  · have hy1 : 0 ≤ y1 := by rcases h1 with h | ⟨h, _⟩ <;> omega
    have hy3 : 0 ≤ y3 := by rcases h3 with h | ⟨h, _⟩ <;> omega
    have hid : y2 * (x1 * y3 - y1 * x3) = y3 * (x1 * y2 - y1 * x2) + y1 * (x2 * y3 - y2 * x3) := by ring
    have hp : 0 ≤ y2 * (x1 * y3 - y1 * x3) := by
      rw [hid]; exact add_nonneg (mul_nonneg hy3 a) (mul_nonneg hy1 b)
    by_contra hc
    have := mul_neg_of_pos_of_neg h2 (not_le.1 hc)
    linarith
  · subst h2
    have hy1 : y1 = 0 := by
      rcases h1 with h | ⟨h, _⟩
      · exfalso; nlinarith [mul_pos h h2']
      · exact h
    have hx1 : 0 < x1 := by
      rcases h1 with h | ⟨_, h⟩
      · omega
      · exact h
    have hy3 : 0 ≤ y3 := by rcases h3 with h | ⟨h, _⟩ <;> omega
    subst hy1
    have : x1 * y3 - 0 * x3 = x1 * y3 := by ring
    rw [this]; exact mul_nonneg hx1.le hy3

theorem exists_min_rel {ι : Type*} [DecidableEq ι] (R : ι → ι → Prop)
    (htot : ∀ i j, R i j ∨ R j i) (htr : ∀ i j l, R i j → R j l → R i l)
    (s : Finset ι) : s.Nonempty → ∃ a ∈ s, ∀ k ∈ s, R a k := by
  induction s using Finset.induction_on with
  | empty => intro h; exact absurd h (by simp)
  | insert a s ha ih =>
    intro _
    by_cases hse : s.Nonempty
    · obtain ⟨b, hb, hbk⟩ := ih hse
      rcases htot a b with h | h
      · refine ⟨a, Finset.mem_insert_self _ _, fun k hk => ?_⟩
        rcases Finset.mem_insert.1 hk with rfl | hk
        · exact (htot _ _).elim id id
        · exact htr _ _ _ h (hbk k hk)
      · refine ⟨b, Finset.mem_insert_of_mem hb, fun k hk => ?_⟩
        rcases Finset.mem_insert.1 hk with rfl | hk
        · exact h
        · exact hbk k hk
    · have hse' : s = ∅ := Finset.not_nonempty_iff_eq_empty.1 hse
      subst hse'
      refine ⟨a, Finset.mem_insert_self _ _, fun k hk => ?_⟩
      have : k = a := by simpa using hk
      subst this
      exact (htot _ _).elim id id

theorem det_par {xa ya xi yi xj yj : ℤ} (ha : InH xa ya) (hi : xa * yi - ya * xi = 0)
    (hj : xa * yj - ya * xj = 0) : xi * yj - yi * xj = 0 := by
  by_contra hne
  have e1 : (xi * yj - yi * xj) * xa = 0 := by linear_combination xi * hj - xj * hi
  have e2 : (xi * yj - yi * xj) * ya = 0 := by linear_combination yi * hj - yj * hi
  have hxa : xa = 0 := (mul_eq_zero.1 e1).resolve_left hne
  have hya : ya = 0 := (mul_eq_zero.1 e2).resolve_left hne
  rcases ha with h | ⟨_, h⟩ <;> omega

theorem det_par2 {xa ya xb yb xk yk : ℤ} (hk : InH xk yk) (hab : xa * yb - ya * xb ≠ 0)
    (h1 : xa * yk - ya * xk = 0) (h2 : xb * yk - yb * xk = 0) : False := by
  have e1 : (xa * yb - ya * xb) * xk = 0 := by linear_combination xb * h1 - xa * h2
  have e2 : (xa * yb - ya * xb) * yk = 0 := by linear_combination yb * h1 - ya * h2
  have hx : xk = 0 := (mul_eq_zero.1 e1).resolve_left hab
  have hy : yk = 0 := (mul_eq_zero.1 e2).resolve_left hab
  rcases hk with h | ⟨_, h⟩ <;> omega

theorem coalesce_H {ι : Type*} [Fintype ι] [DecidableEq ι] (x y : ι → ℤ)
    (hH : ∀ k, InH (x k) (y k)) (hnp : ∃ i j, x i * y j - y i * x j ≠ 0) :
    ∃ (p q : ℤ) (a b : ι), a ≠ b ∧ (∀ k, p * y k - q * x k ≠ 0) ∧
      p * y a - q * x a = -(p * y b - q * x b) := by
  let R : ι → ι → Prop := fun i j => 0 ≤ x i * y j - y i * x j
  have htot : ∀ i j, R i j ∨ R j i := fun i j => by
    simp only [R]
    rcases le_total 0 (x i * y j - y i * x j) with h | h
    · exact Or.inl h
    · right; nlinarith
  have htr : ∀ i j l, R i j → R j l → R i l := fun i j l a b => det_trans (hH i) (hH j) (hH l) a b
  obtain ⟨i0, j0, hij0⟩ := hnp
  have hne : (Finset.univ : Finset ι).Nonempty := ⟨i0, Finset.mem_univ _⟩
  obtain ⟨a, -, ha⟩ := exists_min_rel R htot htr Finset.univ hne
  have hKne : (Finset.univ.filter (fun k => 0 < x a * y k - y a * x k)).Nonempty := by
    by_contra hK
    have hz : ∀ k, x a * y k - y a * x k = 0 := fun k => by
      by_contra hk
      exact hK ⟨k, Finset.mem_filter.2 ⟨Finset.mem_univ _, lt_of_le_of_ne (ha k (Finset.mem_univ _))
        (Ne.symm hk)⟩⟩
    exact hij0 (det_par (hH a) (hz i0) (hz j0))
  obtain ⟨b, hbK, hb⟩ := exists_min_rel R htot htr _ hKne
  have hab : 0 < x a * y b - y a * x b := (Finset.mem_filter.1 hbK).2
  refine ⟨x a + x b, y a + y b, a, b, ?_, ?_, ?_⟩
  · intro h; subst h; nlinarith [hab]
  · intro k
    by_cases hk : 0 < x a * y k - y a * x k
    · have hbk : 0 ≤ x b * y k - y b * x k := hb k (Finset.mem_filter.2 ⟨Finset.mem_univ _, hk⟩)
      intro h0
      nlinarith
    · have h0 : x a * y k - y a * x k = 0 := le_antisymm (not_lt.1 hk) (ha k (Finset.mem_univ _))
      intro hc
      have h1 : x b * y k - y b * x k = 0 := by nlinarith
      exact det_par2 (hH k) hab.ne' h0 h1
  · ring

/-- Coalescing for arbitrary integer rows `(v k, w k)` with `v k ≠ 0` not all parallel. -/
theorem coalesce {ι : Type*} [Fintype ι] [DecidableEq ι] (v w : ι → ℤ) (hv : ∀ k, v k ≠ 0)
    (hnp : ∃ i j, v i * w j - v j * w i ≠ 0) :
    ∃ (α β : ℤ) (a b : ι), a ≠ b ∧ (∀ k, α * v k + β * w k ≠ 0) ∧
      |α * v a + β * w a| = |α * v b + β * w b| := by
  classical
  let ε : ι → ℤ := fun k => if InH (v k) (w k) then 1 else -1
  have hε : ∀ k, ε k = 1 ∨ ε k = -1 := fun k => by
    simp only [ε]; split_ifs <;> simp
  have hH : ∀ k, InH (ε k * v k) (ε k * w k) := fun k => by
    have := hv k
    by_cases h : InH (v k) (w k)
    · simp only [ε, if_pos h]; simpa using h
    · simp only [ε, if_neg h]
      unfold InH at h ⊢
      omega
  have hnp' : ∃ i j, (ε i * v i) * (ε j * w j) - (ε i * w i) * (ε j * v j) ≠ 0 := by
    obtain ⟨i, j, h⟩ := hnp
    refine ⟨i, j, ?_⟩
    have : (ε i * v i) * (ε j * w j) - (ε i * w i) * (ε j * v j) = (ε i * ε j) * (v i * w j - v j * w i) := by
      ring
    rw [this]
    refine mul_ne_zero ?_ h
    rcases hε i with h1 | h1 <;> rcases hε j with h2 | h2 <;> rw [h1, h2] <;> norm_num
  obtain ⟨p, q, a, b, hab, hne, heq⟩ := coalesce_H (fun k => ε k * v k) (fun k => ε k * w k) hH hnp'
  refine ⟨-q, p, a, b, hab, fun k => ?_, ?_⟩
  · intro h0
    apply hne k
    have : p * (ε k * w k) - q * (ε k * v k) = ε k * (-q * v k + p * w k) := by ring
    rw [this, h0, mul_zero]
  · have habs : ∀ k, |ε k| = 1 := fun k => by rcases hε k with h | h <;> rw [h] <;> simp
    have e1 : ∀ k, p * (ε k * w k) - q * (ε k * v k) = ε k * (-q * v k + p * w k) := fun k => by ring
    rw [e1 a, e1 b] at heq
    have := congrArg abs heq
    rw [abs_mul, abs_neg, abs_mul, habs, habs, one_mul, one_mul] at this
    exact this

/-! ### from `LRC 5` to a collision -/

theorem ML_le_of_range {k k' : ℕ} (y : Fin (k' + 1) → ℤ) (u : Fin (k + 1) → ℤ)
    (h : ∀ i, ∃ j, |u i| = y j) : ML y ≤ ML u := by
  have hgap : ∀ t, gap y t ≤ gap u t := fun t => by
    refine le_gap u t _ (fun i => ?_)
    obtain ⟨j, hj⟩ := h i
    have h1 := gap_le y t j
    rw [← hj, nid_abs_int] at h1
    exact h1
  exact csSup_le (Set.range_nonempty _) (by
    rintro _ ⟨t, rfl⟩
    exact (hgap t).trans (le_csSup (bddAbove_range_gap u) ⟨t, rfl⟩))

theorem LRC5_collision (h5 : LRC 5) (u : Fin 6 → ℤ) (hne : ∀ k, u k ≠ 0) (a b : Fin 6) (hab : a ≠ b)
    (habs : |u a| = |u b|) : (1 : ℝ) / 6 ≤ ML u := by
  classical
  set S : Finset ℤ := Finset.univ.image (fun k => |u k|) with hS
  have hSpos : ∀ s ∈ S, 0 < s := by
    intro s hs
    obtain ⟨k, _, rfl⟩ := Finset.mem_image.1 hs
    exact abs_pos.2 (hne k)
  have hScard : S.card ≤ 5 := by
    have hle : S.card ≤ 6 := by
      have := Finset.card_image_le (s := (Finset.univ : Finset (Fin 6))) (f := fun k => |u k|)
      simpa using this
    have hne6 : S.card ≠ 6 := by
      intro h6
      have hinj : Set.InjOn (fun k => |u k|) (↑(Finset.univ : Finset (Fin 6))) := by
        rw [← Finset.card_image_iff]; simpa using h6
      exact hab (hinj (Finset.mem_coe.2 (Finset.mem_univ a)) (Finset.mem_coe.2 (Finset.mem_univ b)) habs)
    omega
  set M : ℤ := ∑ s ∈ S, s with hM
  have hM0 : 0 ≤ M := Finset.sum_nonneg (fun s hs => (hSpos s hs).le)
  have hsM : ∀ s ∈ S, s ≤ M := fun s hs =>
    Finset.single_le_sum (f := fun s : ℤ => s) (fun s hs => (hSpos s hs).le) hs
  set T : Finset ℤ := S ∪ Finset.Icc (M + 1) (M + 5) with hT
  have hTcard : 5 ≤ T.card := by
    have h1 : (Finset.Icc (M + 1) (M + 5)).card = 5 := by
      rw [Int.card_Icc]; omega
    calc 5 = (Finset.Icc (M + 1) (M + 5)).card := h1.symm
      _ ≤ T.card := Finset.card_le_card Finset.subset_union_right
  obtain ⟨U, hSU, hUT, hUcard⟩ := Finset.exists_subsuperset_card_eq
    (Finset.subset_union_left : S ⊆ T) hScard hTcard
  have hUpos : ∀ s ∈ U, 0 < s := by
    intro s hs
    rcases Finset.mem_union.1 (hUT hs) with h | h
    · exact hSpos s h
    · have := (Finset.mem_Icc.1 h).1; omega
  set y : Fin 5 → ℤ := fun i => U.orderEmbOfFin hUcard i with hy
  have hyinj : Function.Injective y := (U.orderEmbOfFin hUcard).injective
  have hypos : ∀ i, 0 < y i := fun i => hUpos _ (Finset.orderEmbOfFin_mem U hUcard i)
  have h6 := h5 4 rfl y hyinj hypos
  have hrange : ∀ i, ∃ j, |u i| = y j := by
    intro i
    have : |u i| ∈ Set.range (U.orderEmbOfFin hUcard) := by
      rw [Finset.range_orderEmbOfFin]
      exact hSU (Finset.mem_image.2 ⟨i, Finset.mem_univ _, rfl⟩)
    obtain ⟨j, hj⟩ := this
    exact ⟨j, hj.symm⟩
  have hle := ML_le_of_range y u hrange
  have : (1 : ℝ) / 6 ≤ ML y := by
    have := h6
    norm_num at this
    exact this
  linarith

/-- **Two-direction bound.**  If `w` is a `δ`-rounding of `t v` (coordinatewise) and `v`, `w` are not
parallel, then `ML v >= 1/6 - δ/2`, from `LRC 5`. -/
theorem two_dir (h5 : LRC 5) (v w : Fin 6 → ℤ) (hv : ∀ k, v k ≠ 0) (t δ : ℝ)
    (he : ∀ i, |(w i : ℝ) - t * v i| ≤ δ) (hnp : ∃ i j, v i * w j - v j * w i ≠ 0) :
    (1 : ℝ) / 6 - δ / 2 ≤ ML v := by
  obtain ⟨α, β, a, b, hab, hne, habs⟩ := coalesce v w hv hnp
  have h1 := LRC5_collision h5 (fun i => α * v i + β * w i) hne a b hab habs
  have h2 := ML_transfer v w α β t δ he
  linarith

end Sext6
end LRSpectrumFull

#print axioms LRSpectrumFull.Sext6.coalesce
#print axioms LRSpectrumFull.Sext6.ML_transfer
#print axioms LRSpectrumFull.Sext6.LRC5_collision
#print axioms LRSpectrumFull.Sext6.two_dir
