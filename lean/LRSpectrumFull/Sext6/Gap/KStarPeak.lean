import LRSpectrumFull.Sext6.Gap.KStarLocal
import LRSpectrumFull.Delta2Boundary

/-!
# Theorem K*, part 3: Lemma 2'' (the peak-free component lemma)  [2026-11-25]

Source: the accompanying notes on Theorem K*, Lemma 2 and the "peak-free form" of section 10.

Statement proved here (`peak_free`).  Let `v` be positive integer speeds, `L = ML v ≤ 1/2`, `vμ > 0`,
and assume

* (V1) at every equality time `p` (`gap v p = L`) there is a runner at `+L` and one at `-L`, both of speed
  `≥ vμ` (this is "`vμ ≤ min over equality times and sides of the fastest runner at that side`");
* (hL2) every local maximum of `gap v` with value `< L` has value `≤ L2`.

Then for every `c > 0` with `L2 ≤ c` and every time `t` with `c < gap v t` there is an equality time `p` with
`gap v t ≤ L - vμ |t - p|`.

Method (no connected components): `a` (resp. `b`) is the last (resp. first) time before (resp. after) `t` at which
`gap ≤ c`; on `[a,b]` the maximiser `p` is interior, a local maximum of value `> c ≥ L2`, hence an equality time;
on the segment between `p` and `t` no runner is at an integer, so every runner's distance is a tent and `gap` is
concave there; a concave function lies below the straight line leaving the peak, whose slope is that of the
runner of speed `≥ vμ` (`tangent_right`, `tangent_left`).  No `ConcaveOn` is used: concavity is proved as the
two-point inequality that the tangent step needs.
No `sorry`, no `axiom`.

Convention: `v : Fin (k+1) → ℤ` has `k + 1` speeds and `(v, w) = Fin.snoc v w` has `k + 2`; for the base `[N]` one has `N = k + 1`. Speeds are the moving runners; the runner at rest is not counted, so a vector of `N` speeds means `N + 1` runners and the Lonely Runner value is `1/(N+1)`.
Hypotheses: those of the individual statements (numerical bounds, structural conditions and, where named in the list above, window predicates such as `PrimeWin`, `CopWin`, `PrimeWindow7`, which later modules discharge for explicit ranges). The unproved predicates `DusartPi`, `LRCHyp`, `CopWinHyp` are not hypotheses of any statement in this module.
Axiom audit: covered by `Axioms15` (also reached through the imports of `Axioms19`, `Axioms20`) (`#print axioms`; declarations not printed there are bricks of printed ones, so their axioms are bounded by the printed lines).
-/

open Filter Topology

namespace LRSpectrumFull
namespace Sext6
namespace Gap

/-- On `(n, n+1)` the distance to the nearest integer is the tent `min (u-n) (n+1-u)`. -/
lemma nid_of_Ioo {u : ℝ} {n : ℤ} (h1 : (n : ℝ) < u) (h2 : u < n + 1) :
    nearestIntDist u = min (u - n) (n + 1 - u) := by
  have hf : ⌊u⌋ = n := Int.floor_eq_iff.mpr ⟨h1.le, h2⟩
  have hfr : Int.fract u = u - n := by rw [← Int.self_sub_floor, hf]
  unfold nearestIntDist
  rw [hfr, show (1 : ℝ) - (u - n) = n + 1 - u by ring]

lemma convex_pos {p q a b : ℝ} (hp : 0 < p) (hq : 0 < q) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hab : a + b = 1) : 0 < a * p + b * q := by
  rcases ha.eq_or_lt with h | h
  · have hb1 : b = 1 := by linarith
    rw [← h, hb1]
    linarith
  · have h1 := mul_pos h hp
    have h2 := mul_nonneg hb hq.le
    linarith

/-- Concavity of the tent distance on a segment containing no integer. -/
lemma nid_seg_concave {x y a b : ℝ} (hxy : x ≤ y)
    (hno : ∀ z : ℝ, x ≤ z → z ≤ y → ∀ m : ℤ, z ≠ m)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1) :
    a * nearestIntDist x + b * nearestIntDist y ≤ nearestIntDist (a * x + b * y) := by
  obtain ⟨n, hn1, hn2⟩ : ∃ n : ℤ, (n : ℝ) ≤ x ∧ x < n + 1 :=
    ⟨⌊x⌋, Int.floor_le x, Int.lt_floor_add_one x⟩
  have hxn : (n : ℝ) < x := by
    rcases hn1.lt_or_eq with h | h
    · exact h
    · exact absurd h.symm (hno x le_rfl hxy n)
  have hyn1 : y < n + 1 := by
    by_contra hcon
    push_neg at hcon
    exact hno ((n : ℝ) + 1) hn2.le hcon (n + 1) (by norm_num)
  have hyn : (n : ℝ) < y := lt_of_lt_of_le hxn hxy
  have hn' : a * (n : ℝ) + b * n = n := by rw [← add_mul, hab, one_mul]
  have hn'' : a * ((n : ℝ) + 1) + b * ((n : ℝ) + 1) = n + 1 := by rw [← add_mul, hab, one_mul]
  have hz1 : (n : ℝ) < a * x + b * y := by
    have := convex_pos (sub_pos.mpr hxn) (sub_pos.mpr hyn) ha hb hab
    linarith
  have hz2 : a * x + b * y < n + 1 := by
    have := convex_pos (sub_pos.mpr hn2) (sub_pos.mpr hyn1) ha hb hab
    linarith
  rw [nid_of_Ioo hxn hn2, nid_of_Ioo hyn hyn1, nid_of_Ioo hz1 hz2]
  apply le_min
  · have h1 := mul_le_mul_of_nonneg_left (min_le_left (x - n) (n + 1 - x)) ha
    have h2 := mul_le_mul_of_nonneg_left (min_le_left (y - n) (n + 1 - y)) hb
    linarith
  · have h1 := mul_le_mul_of_nonneg_left (min_le_right (x - n) (n + 1 - x)) ha
    have h2 := mul_le_mul_of_nonneg_left (min_le_right (y - n) (n + 1 - y)) hb
    linarith

/-- `gap v` is concave on a segment `[p,q]` on which it is positive (no runner is at an integer). -/
lemma gap_seg_concave {k : ℕ} (v : Fin (k + 1) → ℤ) (hv : ∀ i, 0 < v i) {p q : ℝ} (hpq : p ≤ q)
    (hpos : ∀ u, p ≤ u → u ≤ q → 0 < gap v u) {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hab : a + b = 1) :
    a * gap v p + b * gap v q ≤ gap v (a * p + b * q) := by
  apply le_gap v (a * p + b * q)
  intro i
  have hvi : (0 : ℝ) < (v i : ℝ) := by exact_mod_cast hv i
  have hvne : (v i : ℝ) ≠ 0 := hvi.ne'
  have hxy : (v i : ℝ) * p ≤ (v i : ℝ) * q := mul_le_mul_of_nonneg_left hpq hvi.le
  have hno : ∀ z : ℝ, (v i : ℝ) * p ≤ z → z ≤ (v i : ℝ) * q → ∀ m : ℤ, z ≠ m := by
    intro z hz1 hz2 m hzm
    have hu1 : p ≤ z / (v i : ℝ) := by rw [le_div_iff₀ hvi]; linarith
    have hu2 : z / (v i : ℝ) ≤ q := by rw [div_le_iff₀ hvi]; linarith
    have h0 := hpos _ hu1 hu2
    have h1 : gap v (z / (v i : ℝ)) ≤ nearestIntDist ((v i : ℝ) * (z / (v i : ℝ))) :=
      gap_le v _ i
    have hmul : (v i : ℝ) * (z / (v i : ℝ)) = z := by field_simp
    have h2 : nearestIntDist z = 0 := by rw [hzm]; exact nearestIntDist_intCast m
    rw [hmul, h2] at h1
    linarith
  have h := nid_seg_concave (a := a) (b := b) hxy hno ha hb hab
  have e : (v i : ℝ) * (a * p + b * q) = a * ((v i : ℝ) * p) + b * ((v i : ℝ) * q) := by ring
  rw [e]
  have g1 : gap v p ≤ nearestIntDist ((v i : ℝ) * p) := gap_le v p i
  have g2 : gap v q ≤ nearestIntDist ((v i : ℝ) * q) := gap_le v q i
  have h3 := mul_le_mul_of_nonneg_left g1 ha
  have h4 := mul_le_mul_of_nonneg_left g2 hb
  linarith

/-- A concave function lies under the line leaving the peak: right side. -/
lemma tangent_right {h : ℝ → ℝ} {p t L lam s : ℝ} (hpt : p < t)
    (hcon : ∀ a b : ℝ, 0 ≤ a → 0 ≤ b → a + b = 1 → a * h p + b * h t ≤ h (a * p + b * t))
    (hp : h p = L) (hs0 : 0 < s) (hs1 : s ≤ t - p) (hh : h (p + s) ≤ L - lam * s) :
    h t ≤ L - lam * (t - p) := by
  have htp : 0 < t - p := by linarith
  have htp' : t - p ≠ 0 := htp.ne'
  obtain ⟨b, hbdef⟩ : ∃ b : ℝ, b = s / (t - p) := ⟨_, rfl⟩
  have hbpos : 0 < b := by rw [hbdef]; exact div_pos hs0 htp
  have hbt : b * (t - p) = s := by rw [hbdef]; field_simp
  have hpt' : (1 - b) * p + b * t = p + s := by linear_combination hbt
  have hc := hcon (1 - b) b (by rw [hbdef, sub_nonneg, div_le_one htp]; exact hs1) hbpos.le
    (by ring)
  rw [hpt', hp] at hc
  have key : b * (L - lam * (t - p)) = b * L - lam * s := by rw [← hbt]; ring
  have h2 : b * h t ≤ b * (L - lam * (t - p)) := by rw [key]; linarith
  exact le_of_mul_le_mul_left h2 hbpos

/-- A concave function lies under the line leaving the peak: left side. -/
lemma tangent_left {h : ℝ → ℝ} {u p L lam s : ℝ} (hup : u < p)
    (hcon : ∀ a b : ℝ, 0 ≤ a → 0 ≤ b → a + b = 1 → a * h u + b * h p ≤ h (a * u + b * p))
    (hp : h p = L) (hs0 : 0 < s) (hs1 : s ≤ p - u) (hh : h (p - s) ≤ L - lam * s) :
    h u ≤ L - lam * (p - u) := by
  have hpu : 0 < p - u := by linarith
  have hpu' : p - u ≠ 0 := hpu.ne'
  obtain ⟨b, hbdef⟩ : ∃ b : ℝ, b = s / (p - u) := ⟨_, rfl⟩
  have hbpos : 0 < b := by rw [hbdef]; exact div_pos hs0 hpu
  have hbt : b * (p - u) = s := by rw [hbdef]; field_simp
  have hpt' : b * u + (1 - b) * p = p - s := by linear_combination (-1 : ℝ) * hbt
  have hc := hcon b (1 - b) hbpos.le (by rw [hbdef, sub_nonneg, div_le_one hpu]; exact hs1)
    (by ring)
  rw [hpt', hp] at hc
  have key : b * (L - lam * (p - u)) = b * L - lam * s := by rw [← hbt]; ring
  have h2 : b * h u ≤ b * (L - lam * (p - u)) := by rw [key]; linarith
  exact le_of_mul_le_mul_left h2 hbpos

/-- A runner sitting at `m - L` at time `p` is at distance `L - v s` at time `p + s`. -/
lemma runner_down {v p L s : ℝ} {m : ℤ} (hv0 : 0 ≤ v) (hL0 : 0 ≤ L) (hL : L ≤ 1 / 2)
    (hrun : v * p = m - L) (hs : 0 ≤ s) (hsL : v * s ≤ L) :
    nearestIntDist (v * (p + s)) = L - v * s := by
  have e : v * (p + s) = -(L - v * s) + (m : ℝ) := by linear_combination hrun
  rw [e, nearestIntDist_add_int, nearestIntDist_neg]
  have := mul_nonneg hv0 hs
  exact nid_of_le_half (by linarith) (by linarith)

/-- A runner sitting at `n + L` at time `p` is at distance `L - v s` at time `p - s`. -/
lemma runner_up {v p L s : ℝ} {n : ℤ} (hv0 : 0 ≤ v) (hL : L ≤ 1 / 2)
    (hrun : v * p = n + L) (hs : 0 ≤ s) (hsL : v * s ≤ L) :
    nearestIntDist (v * (p - s)) = L - v * s := by
  have e : v * (p - s) = (L - v * s) + (n : ℝ) := by linear_combination hrun
  rw [e, nearestIntDist_add_int]
  have := mul_nonneg hv0 hs
  exact nid_of_le_half (by linarith) (by linarith)

/-- The last time before `t` at which `f ≤ c`. -/
lemma exists_last_below {f : ℝ → ℝ} (hf : Continuous f) {c t : ℝ} (s0 : ℝ) (hs0 : s0 ≤ t)
    (hfs0 : f s0 ≤ c) (ht : c < f t) :
    ∃ a, a < t ∧ f a ≤ c ∧ ∀ u, a < u → u ≤ t → c < f u := by
  have hclosed : IsClosed (Set.Iic t ∩ {s : ℝ | f s ≤ c}) :=
    isClosed_Iic.inter (isClosed_le hf continuous_const)
  have hne : (Set.Iic t ∩ {s : ℝ | f s ≤ c}).Nonempty := ⟨s0, hs0, hfs0⟩
  have hbdd : BddAbove (Set.Iic t ∩ {s : ℝ | f s ≤ c}) := ⟨t, fun x hx => hx.1⟩
  have hmem := hclosed.csSup_mem hne hbdd
  have h1 : sSup (Set.Iic t ∩ {s : ℝ | f s ≤ c}) ≤ t := hmem.1
  have h2 : f (sSup (Set.Iic t ∩ {s : ℝ | f s ≤ c})) ≤ c := hmem.2
  refine ⟨sSup (Set.Iic t ∩ {s : ℝ | f s ≤ c}), ?_, h2, ?_⟩
  · rcases lt_or_eq_of_le h1 with h | h
    · exact h
    · exfalso
      rw [h] at h2
      linarith
  · intro u hu1 hut
    by_contra hcon
    push_neg at hcon
    have : u ≤ sSup (Set.Iic t ∩ {s : ℝ | f s ≤ c}) := le_csSup hbdd ⟨hut, hcon⟩
    linarith

/-- The first time after `t` at which `f ≤ c`. -/
lemma exists_first_above {f : ℝ → ℝ} (hf : Continuous f) {c t : ℝ} (s1 : ℝ) (hs1 : t ≤ s1)
    (hfs1 : f s1 ≤ c) (ht : c < f t) :
    ∃ b, t < b ∧ f b ≤ c ∧ ∀ u, t ≤ u → u < b → c < f u := by
  obtain ⟨a, hat, hfa, hall⟩ := exists_last_below (f := fun x => f (-x)) (hf.comp continuous_neg)
    (c := c) (t := -t) (-s1) (by linarith) (by simpa using hfs1) (by simpa using ht)
  refine ⟨-a, by linarith, by simpa using hfa, ?_⟩
  intro u hu1 hu2
  have := hall (-u) (by linarith) (by linarith)
  simpa using this

/-- `gap v` vanishes (is `≤ c` for `c ≥ 0`) at every integer time. -/
lemma gap_int_le {k : ℕ} (v : Fin (k + 1) → ℤ) {c : ℝ} (hc : 0 ≤ c) (n : ℤ) :
    gap v (n : ℝ) ≤ c := by
  have h1 := gap_le v (n : ℝ) 0
  rw [← Int.cast_mul (α := ℝ) (v 0) n, nearestIntDist_intCast] at h1
  linarith

/-- **Lemma 2'' (peak-free component lemma).** -/
theorem peak_free {k : ℕ} (v : Fin (k + 1) → ℤ) (hv : ∀ i, 0 < v i) (L vμ L2 c : ℝ)
    (hLML : L = ML v) (hL1 : L ≤ 1 / 2) (hvμ : 0 < vμ)
    (hV1 : ∀ p, gap v p = L →
      (∃ i : Fin (k + 1), ∃ n : ℤ, vμ ≤ (v i : ℝ) ∧ (v i : ℝ) * p = n + L) ∧
      (∃ j : Fin (k + 1), ∃ m : ℤ, vμ ≤ (v j : ℝ) ∧ (v j : ℝ) * p = m - L))
    (hL2 : ∀ p, IsLocalMax (gap v) p → gap v p < L → gap v p ≤ L2)
    (hc0 : 0 < c) (hcL2 : L2 ≤ c) (t : ℝ) (ht : c < gap v t) :
    ∃ p, gap v p = L ∧ gap v t ≤ L - vμ * |t - p| := by
  have hgL : ∀ u, gap v u ≤ L := by
    intro u
    rw [hLML]
    exact le_csSup (bddAbove_range_gap v) ⟨u, rfl⟩
  have hLpos : 0 < L := lt_of_lt_of_le (lt_trans hc0 ht) (hgL t)
  have hcont : Continuous (gap v) := gap_continuous v
  obtain ⟨a, hat, hfa, hlow⟩ :=
    exists_last_below hcont ((⌊t⌋ : ℤ) : ℝ) (Int.floor_le t) (gap_int_le v hc0.le _) ht
  obtain ⟨b, htb, hfb, hhigh⟩ :=
    exists_first_above hcont ((⌈t⌉ : ℤ) : ℝ) (Int.le_ceil t) (gap_int_le v hc0.le _) ht
  have hbig : ∀ u, a < u → u < b → c < gap v u := by
    intro u h1 h2
    rcases le_total u t with h | h
    · exact hlow u h1 h
    · exact hhigh u h h2
  obtain ⟨p, hpmem, hpmax⟩ := isCompact_Icc.exists_isMaxOn
    (Set.nonempty_Icc.mpr (by linarith : a ≤ b)) hcont.continuousOn
  have hpge : ∀ u, a ≤ u → u ≤ b → gap v u ≤ gap v p :=
    fun u h1 h2 => hpmax (Set.mem_Icc.mpr ⟨h1, h2⟩)
  have hgp : c < gap v p := lt_of_lt_of_le ht (hpge t hat.le htb.le)
  have hpa : a < p := lt_of_le_of_ne hpmem.1 (fun h => by rw [← h] at hgp; linarith)
  have hpb : p < b := lt_of_le_of_ne hpmem.2 (fun h => by rw [← h] at hfb; linarith)
  have hloc : IsLocalMax (gap v) p := IsMaxOn.isLocalMax hpmax (Icc_mem_nhds hpa hpb)
  have hgpL : gap v p = L := by
    by_contra hne
    have hlt : gap v p < L := lt_of_le_of_ne (hgL p) hne
    have := hL2 p hloc hlt
    linarith
  refine ⟨p, hgpL, ?_⟩
  have hpos : ∀ u1 u2, a < u1 → u2 < b → ∀ u, u1 ≤ u → u ≤ u2 → 0 < gap v u := by
    intro u1 u2 h1 h2 u hu1 hu2
    exact lt_trans hc0 (hbig u (by linarith) (by linarith))
  obtain ⟨⟨i, n, hvi, hin⟩, ⟨j, m, hvj, hjm⟩⟩ := hV1 p hgpL
  rcases lt_trichotomy p t with hpt | hpt | hpt
  · -- p < t : the decreasing runner `j`
    have hvj0 : (0 : ℝ) < (v j : ℝ) := lt_of_lt_of_le hvμ hvj
    obtain ⟨s, hs⟩ : ∃ s : ℝ, s = min (t - p) (L / (v j : ℝ)) := ⟨_, rfl⟩
    have hs0 : 0 < s := by rw [hs]; exact lt_min (by linarith) (div_pos hLpos hvj0)
    have hs1 : s ≤ t - p := by rw [hs]; exact min_le_left _ _
    have hs2 : s ≤ L / (v j : ℝ) := by rw [hs]; exact min_le_right _ _
    have hvs : (v j : ℝ) * s ≤ L := by
      rw [le_div_iff₀ hvj0] at hs2
      linarith
    have hrun := runner_down hvj0.le hLpos.le hL1 hjm hs0.le hvs
    have hh : gap v (p + s) ≤ L - (v j : ℝ) * s := by
      have h1 := gap_le v (p + s) j
      rw [hrun] at h1
      exact h1
    have hcon : ∀ a' b' : ℝ, 0 ≤ a' → 0 ≤ b' → a' + b' = 1 →
        a' * gap v p + b' * gap v t ≤ gap v (a' * p + b' * t) := by
      intro a' b' ha' hb' hab'
      exact gap_seg_concave v hv hpt.le (fun u h1 h2 => hpos p t hpa htb u h1 h2) ha' hb' hab'
    have htan := tangent_right (h := gap v) hpt hcon hgpL hs0 hs1 hh
    have h5 : vμ * (t - p) ≤ (v j : ℝ) * (t - p) := mul_le_mul_of_nonneg_right hvj (by linarith)
    rw [abs_of_pos (by linarith : (0 : ℝ) < t - p)]
    linarith
  · rw [← hpt]
    simp only [sub_self, abs_zero, mul_zero, sub_zero]
    exact hgL p
  · -- t < p : the increasing runner `i`
    have hvi0 : (0 : ℝ) < (v i : ℝ) := lt_of_lt_of_le hvμ hvi
    obtain ⟨s, hs⟩ : ∃ s : ℝ, s = min (p - t) (L / (v i : ℝ)) := ⟨_, rfl⟩
    have hs0 : 0 < s := by rw [hs]; exact lt_min (by linarith) (div_pos hLpos hvi0)
    have hs1 : s ≤ p - t := by rw [hs]; exact min_le_left _ _
    have hs2 : s ≤ L / (v i : ℝ) := by rw [hs]; exact min_le_right _ _
    have hvs : (v i : ℝ) * s ≤ L := by
      rw [le_div_iff₀ hvi0] at hs2
      linarith
    have hrun := runner_up hvi0.le hL1 hin hs0.le hvs
    have hh : gap v (p - s) ≤ L - (v i : ℝ) * s := by
      have h1 := gap_le v (p - s) i
      rw [hrun] at h1
      exact h1
    have hcon : ∀ a' b' : ℝ, 0 ≤ a' → 0 ≤ b' → a' + b' = 1 →
        a' * gap v t + b' * gap v p ≤ gap v (a' * t + b' * p) := by
      intro a' b' ha' hb' hab'
      exact gap_seg_concave v hv hpt.le (fun u h1 h2 => hpos t p hat hpb u h1 h2) ha' hb' hab'
    have htan := tangent_left (h := gap v) hpt hcon hgpL hs0 hs1 hh
    have h5 : vμ * (p - t) ≤ (v i : ℝ) * (p - t) := mul_le_mul_of_nonneg_right hvi (by linarith)
    rw [abs_of_neg (by linarith : t - p < 0)]
    linarith

end Gap
end Sext6
end LRSpectrumFull
