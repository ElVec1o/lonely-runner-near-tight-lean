import LRSpectrumFull.Sext6.Gap.KStarMain
import LRSpectrumFull.Sext6.Gap.InsCap

/-!
# Theorem INS, part 3: the peak lemma `peak_gen` and the upper bound (U)  [2026-11-25]

Source: the accompanying notes on single-speed insertion, sections 2.1, 2.3.

* `PeakData v p mu rho lam` : `p` is a local maximum of `gap v` of height `mu ∈ (0, 1/2]`, `rho` (resp. `lam`)
  is the largest speed of a runner at `+mu` (resp. `-mu`) at `p`.
* `peak_gen` : for every time `t` with `c < gap v t` (`c ≥ 0`) there is a peak `p` (`PeakData`) with
  `gap v t ≤ mu - lam (t - p)` (`p ≤ t`) and `gap v t ≤ mu - rho (p - t)` (`t ≤ p`).  No equality-time step.
* `ML_snoc_le_Hform` : (U).  If `Hform mu th rho lam w ≤ c` for every `PeakData` peak with `c < mu` and every
  representation `w p = th + z`, `|th| ≤ 1/2`, then `ML (v, w) ≤ c`.  No size, divisibility or primitivity
  condition on `w`; the peak set enters only through this hypothesis (it is not defined as a `Finset`).
No `sorry`, no `axiom`.

Convention: `v : Fin (k+1) → ℤ` has `k + 1` speeds; `V = (v, w) = Fin.snoc v w` (integer `w`) has `N = k + 2` speeds (moving runners), i.e. `N + 1` runners counting the one at rest. The Lonely Runner value of `V` is `1/(N+1) = 1/(k+3)`; the threshold of D1, D2 is `1/N`.
Hypotheses: those of the individual statements (numerical bounds, structural conditions and, where named in the list above, window predicates such as `PrimeWin`, `CopWin`, `PrimeWindow7`, which later modules discharge for explicit ranges). The unproved predicates `DusartPi`, `LRCHyp`, `CopWinHyp` are not hypotheses of any statement in this module.
Axiom audit: covered by `Axioms20` (`#print axioms`; declarations not printed there are bricks of printed ones, so their axioms are bounded by the printed lines).
-/

open Filter Topology

namespace LRSpectrumFull
namespace Sext6
namespace Gap

def PeakData {k : ℕ} (v : Fin (k + 1) → ℤ) (p mu rho lam : ℝ) : Prop :=
  IsLocalMax (gap v) p ∧ gap v p = mu ∧ 0 < mu ∧ mu ≤ 1 / 2 ∧
  (∃ i : Fin (k + 1), (v i : ℝ) = rho ∧ PlusRun v mu p i ∧ ∀ i', PlusRun v mu p i' → v i' ≤ v i) ∧
  (∃ j : Fin (k + 1), (v j : ℝ) = lam ∧ MinusRun v mu p j ∧ ∀ j', MinusRun v mu p j' → v j' ≤ v j)

theorem PeakData.isLocalMax {k : ℕ} {v : Fin (k + 1) → ℤ} {p mu rho lam : ℝ}
    (h : PeakData v p mu rho lam) : IsLocalMax (gap v) p := by
  obtain ⟨h1, -⟩ := h
  exact h1

theorem PeakData.gap_eq {k : ℕ} {v : Fin (k + 1) → ℤ} {p mu rho lam : ℝ}
    (h : PeakData v p mu rho lam) : gap v p = mu := by
  obtain ⟨-, h2, -⟩ := h
  exact h2

theorem PeakData.pos {k : ℕ} {v : Fin (k + 1) → ℤ} {p mu rho lam : ℝ}
    (h : PeakData v p mu rho lam) : 0 < mu := by
  obtain ⟨-, -, h3, -⟩ := h
  exact h3

theorem PeakData.le_half {k : ℕ} {v : Fin (k + 1) → ℤ} {p mu rho lam : ℝ}
    (h : PeakData v p mu rho lam) : mu ≤ 1 / 2 := by
  obtain ⟨-, -, -, h4, -⟩ := h
  exact h4

/-- When `gap v p = 1/2`, every runner is at `+1/2` and at `-1/2` (mod 1). -/
lemma half_runner {k : ℕ} (v : Fin (k + 1) → ℤ) (p : ℝ) (hp : gap v p = 1 / 2)
    (i : Fin (k + 1)) : PlusRun v (1 / 2) p i ∧ MinusRun v (1 / 2) p i := by
  have h1 : nearestIntDist ((v i : ℝ) * p) = 1 / 2 := by
    apply le_antisymm (nearestIntDist_le_half _)
    have := gap_le v p i
    rw [hp] at this
    exact this
  obtain ⟨n, hn⟩ := nearestIntDist_eq_abs ((v i : ℝ) * p)
  rw [h1] at hn
  rcases abs_cases ((v i : ℝ) * p - n) with ⟨ha, _⟩ | ⟨ha, _⟩
  · refine ⟨⟨n, ?_⟩, ⟨n + 1, ?_⟩⟩
    · linarith
    · push_cast; linarith
  · refine ⟨⟨n - 1, ?_⟩, ⟨n, ?_⟩⟩
    · push_cast; linarith
    · linarith

/-- At a local maximum of positive height, runners sit at `+mu` and at `-mu`. -/
lemma runners_exist {k : ℕ} (v : Fin (k + 1) → ℤ) (hv : ∀ i, 0 < v i) (p : ℝ)
    (hp : IsLocalMax (gap v) p) (h0 : 0 < gap v p) :
    (∃ i, PlusRun v (gap v p) p i) ∧ (∃ j, MinusRun v (gap v p) p j) := by
  rcases (gap_le_half v p).lt_or_eq with h1 | h1
  · have hloc : ∀ᶠ x in 𝓝 p, gap v x ≤ gap v p := hp
    obtain ⟨i, n, hi⟩ := exists_plus_runner v hv p _ rfl h0 h1 hloc
    obtain ⟨j, m, hj⟩ := exists_minus_runner v hv p _ rfl h0 h1 hloc
    exact ⟨⟨i, n, hi⟩, ⟨j, m, hj⟩⟩
  · rw [h1]
    exact ⟨⟨0, (half_runner v p h1 0).1⟩, ⟨0, (half_runner v p h1 0).2⟩⟩

/-- **The peak lemma** (generalising `peak_free`: no equality-time step). -/
theorem peak_gen {k : ℕ} (v : Fin (k + 1) → ℤ) (hv : ∀ i, 0 < v i) (c : ℝ) (hc0 : 0 ≤ c)
    (t : ℝ) (ht : c < gap v t) :
    ∃ p mu rho lam : ℝ, PeakData v p mu rho lam ∧ gap v t ≤ mu ∧ c < mu ∧
      (p ≤ t → gap v t ≤ mu - lam * (t - p)) ∧ (t ≤ p → gap v t ≤ mu - rho * (p - t)) := by
  have hcont : Continuous (gap v) := gap_continuous v
  obtain ⟨a, hat, hfa, hlow⟩ :=
    exists_last_below hcont ((⌊t⌋ : ℤ) : ℝ) (Int.floor_le t) (gap_int_le v hc0 _) ht
  obtain ⟨b, htb, hfb, hhigh⟩ :=
    exists_first_above hcont ((⌈t⌉ : ℤ) : ℝ) (Int.le_ceil t) (gap_int_le v hc0 _) ht
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
  obtain ⟨mu, hmu⟩ : ∃ mu : ℝ, mu = gap v p := ⟨_, rfl⟩
  have hmu0 : 0 < mu := by rw [hmu]; exact lt_of_le_of_lt hc0 hgp
  have hmuh : mu ≤ 1 / 2 := by rw [hmu]; exact gap_le_half v p
  obtain ⟨hP, hM⟩ := runners_exist v hv p hloc (by rw [← hmu]; exact hmu0)
  rw [← hmu] at hP hM
  obtain ⟨i, hi, hitop⟩ := exists_top v (PlusRun v mu p) hP
  obtain ⟨j, hj, hjtop⟩ := exists_top v (MinusRun v mu p) hM
  have hpeak : PeakData v p mu (v i : ℝ) (v j : ℝ) :=
    ⟨hloc, hmu.symm, hmu0, hmuh, ⟨i, rfl, hi, hitop⟩, ⟨j, rfl, hj, hjtop⟩⟩
  have hgtp : gap v t ≤ mu := by rw [hmu]; exact hpge t hat.le htb.le
  have hcmu : c < mu := by rw [hmu]; exact hgp
  refine ⟨p, mu, (v i : ℝ), (v j : ℝ), hpeak, hgtp, hcmu, ?_, ?_⟩
  · intro hpt'
    rcases hpt'.lt_or_eq with hpt | hpt
    · -- p < t : the decreasing runner `j`
      obtain ⟨m, hjm⟩ := hj
      have hvj0 : (0 : ℝ) < (v j : ℝ) := by exact_mod_cast hv j
      obtain ⟨s, hs⟩ : ∃ s : ℝ, s = min (t - p) (mu / (v j : ℝ)) := ⟨_, rfl⟩
      have hs0 : 0 < s := by rw [hs]; exact lt_min (by linarith) (div_pos hmu0 hvj0)
      have hs1 : s ≤ t - p := by rw [hs]; exact min_le_left _ _
      have hs2 : s ≤ mu / (v j : ℝ) := by rw [hs]; exact min_le_right _ _
      have hvs : (v j : ℝ) * s ≤ mu := by
        rw [le_div_iff₀ hvj0] at hs2
        linarith
      have hrun := runner_down hvj0.le hmu0.le hmuh hjm hs0.le hvs
      have hh : gap v (p + s) ≤ mu - (v j : ℝ) * s := by
        have h1 := gap_le v (p + s) j
        rw [hrun] at h1
        exact h1
      have hpos : ∀ u, p ≤ u → u ≤ t → 0 < gap v u := by
        intro u h1 h2
        exact lt_of_le_of_lt hc0 (hbig u (by linarith) (by linarith))
      have hcon : ∀ a' b' : ℝ, 0 ≤ a' → 0 ≤ b' → a' + b' = 1 →
          a' * gap v p + b' * gap v t ≤ gap v (a' * p + b' * t) := by
        intro a' b' ha' hb' hab'
        exact gap_seg_concave v hv hpt.le hpos ha' hb' hab'
      exact tangent_right (h := gap v) hpt hcon hmu.symm hs0 hs1 hh
    · have h0 : t - p = 0 := by linarith
      rw [h0, mul_zero, sub_zero]
      exact hgtp
  · intro hpt'
    rcases hpt'.lt_or_eq with hpt | hpt
    · -- t < p : the increasing runner `i`
      obtain ⟨n, hin⟩ := hi
      have hvi0 : (0 : ℝ) < (v i : ℝ) := by exact_mod_cast hv i
      obtain ⟨s, hs⟩ : ∃ s : ℝ, s = min (p - t) (mu / (v i : ℝ)) := ⟨_, rfl⟩
      have hs0 : 0 < s := by rw [hs]; exact lt_min (by linarith) (div_pos hmu0 hvi0)
      have hs1 : s ≤ p - t := by rw [hs]; exact min_le_left _ _
      have hs2 : s ≤ mu / (v i : ℝ) := by rw [hs]; exact min_le_right _ _
      have hvs : (v i : ℝ) * s ≤ mu := by
        rw [le_div_iff₀ hvi0] at hs2
        linarith
      have hrun := runner_up hvi0.le hmuh hin hs0.le hvs
      have hh : gap v (p - s) ≤ mu - (v i : ℝ) * s := by
        have h1 := gap_le v (p - s) i
        rw [hrun] at h1
        exact h1
      have hpos : ∀ u, t ≤ u → u ≤ p → 0 < gap v u := by
        intro u h1 h2
        exact lt_of_le_of_lt hc0 (hbig u (by linarith) (by linarith))
      have hcon : ∀ a' b' : ℝ, 0 ≤ a' → 0 ≤ b' → a' + b' = 1 →
          a' * gap v t + b' * gap v p ≤ gap v (a' * t + b' * p) := by
        intro a' b' ha' hb' hab'
        exact gap_seg_concave v hv hpt.le hpos ha' hb' hab'
      exact tangent_left (h := gap v) hpt hcon hmu.symm hs0 hs1 hh
    · have h0 : p - t = 0 := by linarith
      rw [h0, mul_zero, sub_zero]
      exact hgtp

/-- **(U).**  `ML (v, w) ≤ c` as soon as every peak higher than `c` has `H_p(w) ≤ c`. -/
theorem ML_snoc_le_Hform {k : ℕ} (v : Fin (k + 1) → ℤ) (hv : ∀ i, 0 < v i) (w : ℤ) (hw : 0 < w)
    (c : ℝ) (hc0 : 0 ≤ c)
    (hH : ∀ p mu rho lam : ℝ, PeakData v p mu rho lam → c < mu →
      ∀ (th : ℝ) (z : ℤ), (w : ℝ) * p = th + z → |th| ≤ 1 / 2 →
        Hform mu th rho lam (w : ℝ) ≤ c) :
    ML (Fin.snoc v w : Fin (k + 2) → ℤ) ≤ c := by
  apply ML_le_of_cover
  intro t
  by_contra hcon
  have hcon' : ∀ i : Fin (k + 2), c < nearestIntDist (((Fin.snoc v w : Fin (k + 2) → ℤ) i : ℝ) * t) := by
    intro i
    exact not_le.mp (fun h => hcon ⟨i, h⟩)
  have hg : c < gap v t := by
    unfold gap
    rw [Finset.lt_inf'_iff]
    intro i _
    have h := hcon' (Fin.castSucc i)
    simpa [Fin.snoc_castSucc] using h
  have hwt : c < nearestIntDist ((w : ℝ) * t) := by
    have h := hcon' (Fin.last (k + 1))
    simpa [Fin.snoc_last] using h
  obtain ⟨p, mu, rho, lam, hpeak, -, hcmu, hR, hL⟩ := peak_gen v hv c hc0 t hg
  have hw' : (0 : ℝ) < (w : ℝ) := by exact_mod_cast hw
  have hmu0 : 0 < mu := hpeak.pos
  have hmuh : mu ≤ 1 / 2 := hpeak.le_half
  have hrho : 0 < rho := by
    obtain ⟨_, _, _, _, ⟨i, hri, _, _⟩, _⟩ := hpeak
    rw [← hri]; exact_mod_cast hv i
  have hlam : 0 < lam := by
    obtain ⟨_, _, _, _, _, ⟨j, hlj, _, _⟩⟩ := hpeak
    rw [← hlj]; exact_mod_cast hv j
  obtain ⟨z, hz⟩ : ∃ z : ℤ, z = round ((w : ℝ) * p) := ⟨_, rfl⟩
  have hth : |(w : ℝ) * p - z| ≤ 1 / 2 := by rw [hz]; exact abs_sub_round _
  have hH' := hH p mu rho lam hpeak hcmu ((w : ℝ) * p - z) z (by ring) hth
  have hcap := Hcap mu ((w : ℝ) * p - z) rho lam (w : ℝ) t p (gap v t) z hmu0 hmuh hrho hlam hw'
    (by ring) hR hL
  have hlt : c < min (gap v t) (nearestIntDist ((w : ℝ) * t)) := lt_min hg hwt
  linarith

end Gap
end Sext6
end LRSpectrumFull
