import LRSpectrumFull.Sext6.Gap.TwoELower

/-!
# Two-entry sandwich, part 2: the upper bound (Dirichlet puts every high point on an arc)  [2026-11-25]

Hypotheses: `N/2 < r1, r2 ≤ N` (`N < 2 r_i`, `r_i ≤ N`), `gcd(r1,r2) > 1` (`¬ Nat.Coprime r1 r2`),
`v` contains every retained speed `x ∈ [1,N] \ {r1,r2}` and both inserted speeds `w1, w2`.
`w_j > N` and `A ∤ w_j` are NOT needed for the upper bound.

* `two_core`          : at an arc point `t = (c+η)/r`, `η ∈ [0,1/(N+1)]`, if every speed of `v` is at distance `> cc`
                        from an integer, then `E` (an upper bound of all arc values) satisfies `E > cc`.
* `two_entry_upper`   : if `E` bounds every arc value, then `ML v ≤ max (1/(N+1)) E`.
No `sorry`, no `axiom`.

Convention: `N` is the size of the ambient interval `[1,N]`; the speed vector `v : Fin (k+1) → ℤ` is a finite family (repetitions allowed). Speeds are the moving runners; the runner at rest is not counted, so a vector of `N` speeds means `N + 1` runners and the Lonely Runner value is `1/(N+1)`.
Axiom audit: covered by `Axioms23`.
-/

namespace LRSpectrumFull
namespace Sext6
namespace Gap

theorem two_core {N r r1 r2 w1 w2 : ℕ} (hN : 2 ≤ N) (h1 : N < 2 * r1) (h2 : N < 2 * r2)
    (hrr : r = r1 ∨ r = r2) (hrN : r ≤ N)
    (hG : ∀ x : ℕ, (x = r1 ∨ x = r2) → x ≠ r → ¬ Nat.Coprime x r)
    (cc : ℝ) (hcc : 1 / ((N : ℝ) + 1) ≤ cc) (E : ℝ)
    (hE : ∀ y ∈ ArcSet N r1 r2 w1 w2, y ≤ E) (hcE : E ≤ cc)
    (t : ℝ) (c : ℤ) (η : ℝ) (hrt : (r : ℝ) * t = c + η) (hη0 : 0 ≤ η)
    (hη1 : η ≤ 1 / ((N : ℝ) + 1))
    (hx : ∀ x : ℕ, 1 ≤ x → x ≤ N → x ≠ r1 → x ≠ r2 → cc < nearestIntDist ((x : ℝ) * t))
    (hn1 : cc < nearestIntDist ((w1 : ℝ) * t)) (hn2 : cc < nearestIntDist ((w2 : ℝ) * t)) :
    False := by
  have hrlt : N < 2 * r := by rcases hrr with h | h <;> omega
  have hrr2 : 2 ≤ r := by omega
  have hNR : (0 : ℝ) < (N : ℝ) + 1 := by positivity
  have hη2 : η * ((N : ℝ) + 1) ≤ 1 := (le_div_iff₀ hNR).mp hη1
  obtain ⟨R, hR⟩ : ∃ R : Finset ℕ, R = {r1, r2} := ⟨_, rfl⟩
  have hmemR : ∀ x : ℕ, x ∈ R ↔ (x = r1 ∨ x = r2) := by
    intro x; rw [hR]; simp
  have hRlt : ∀ r' ∈ R, N < 2 * r' := by
    intro r' hr'
    rcases (hmemR r').mp hr' with h | h <;> rw [h] <;> assumption
  have hS : Spec N r 2 (betaFam N r) := spec_betaFam hN hrlt hrN (le_refl 2)
  have hx' : ∀ x : ℕ, 1 ≤ x → x ≤ N → x ∉ R → cc < nearestIntDist ((x : ℝ) * t) := by
    intro x hx1 hxN hxR
    apply hx x hx1 hxN
    · intro h; exact hxR ((hmemR x).mpr (Or.inl h))
    · intro h; exact hxR ((hmemR x).mpr (Or.inr h))
  have hcop := munit_of_trap R hRlt hS cc hcc t c η hrt hη0 hη1 hx'
  obtain ⟨X, hX1, hX2, hXd⟩ := exists_block r ((N : ℤ) + 1 - r) (by omega) c hcop
  obtain ⟨k, hk⟩ := hXd
  have hXpos : (1 : ℤ) ≤ X := by
    have : (r : ℤ) ≤ N := by exact_mod_cast hrN
    omega
  obtain ⟨xn, hxn⟩ : ∃ xn : ℕ, (xn : ℤ) = X := ⟨X.toNat, Int.toNat_of_nonneg (by omega)⟩
  have hxnR : (xn : ℝ) = (X : ℝ) := by exact_mod_cast hxn
  have hxN : xn ≤ N := by omega
  have hxr : xn ≠ r := by
    intro hxr
    have hXr : X = r := by rw [← hxn, hxr]
    rw [hXr] at hk
    have hd : (r : ℤ) ∣ 1 := ⟨k - c, by linarith⟩
    have := Int.le_of_dvd (by norm_num) hd
    omega
  have hcopx : Nat.Coprime xn r := by
    have : IsCoprime X (r : ℤ) := ⟨-c, k, by linarith⟩
    rw [← hxn] at this
    exact Nat.isCoprime_iff_coprime.mp this
  have hxn1 : xn ≠ r1 := fun h => hG xn (Or.inl h) hxr hcopx
  have hxn2 : xn ≠ r2 := fun h => hG xn (Or.inr h) hxr hcopx
  have hkR : (c : ℝ) * X + 1 = r * k := by exact_mod_cast hk
  have hw : (r : ℝ) * ((X : ℝ) * t - k) = X * η - 1 := by
    linear_combination (X : ℝ) * hrt + hkR
  have hXR : (X : ℝ) ≤ N := by rw [← hxnR]; exact_mod_cast hxN
  have hXη : (X : ℝ) * η ≤ 1 := by
    have h3 : (X : ℝ) * η ≤ N * η := mul_le_mul_of_nonneg_right hXR hη0
    nlinarith
  have hrpos : (0 : ℝ) < r := by exact_mod_cast (by omega : 0 < r)
  have hw0 : (X : ℝ) * t - k ≤ 0 := by
    by_contra hcon
    have := mul_pos hrpos (not_le.mp hcon)
    linarith
  have hxv := hx xn (by omega) hxN hxn1 hxn2
  rw [hxnR] at hxv
  have h3 : cc < -((X : ℝ) * t - k) := by
    have := lt_of_lt_of_le hxv (nearestIntDist_le_dist ((X : ℝ) * t) k)
    rwa [abs_of_nonpos hw0] at this
  have h4 : cc * r < 1 - X * η := by
    have := mul_lt_mul_of_pos_left h3 hrpos
    linarith
  have htent : cc < (1 - (X : ℝ) * η) / r := (lt_div_iff₀ hrpos).mpr h4
  have hr0 : (r : ℝ) ≠ 0 := hrpos.ne'
  have ht : t = ((c : ℝ) + η) / r := by
    rw [eq_div_iff hr0]; linarith
  have hs1 : cc < nearestIntDist ((w1 : ℝ) * (((c : ℝ) + η) / r)) := by rw [← ht]; exact hn1
  have hs2 : cc < nearestIntDist ((w2 : ℝ) * (((c : ℝ) + η) / r)) := by rw [← ht]; exact hn2
  have hmem : arcVal r w1 w2 c X η ∈ ArcSet N r1 r2 w1 w2 :=
    by
      simp only [ArcSet, Set.mem_setOf_eq]
      exact ⟨r, hrr, c, X, η, hcop, ⟨hX1, by omega, ⟨k, hk⟩⟩, hη0, hη1, rfl⟩
  have hlt : cc < arcVal r w1 w2 c X η := by
    unfold arcVal
    exact lt_min htent (lt_min hs1 hs2)
  have := hE _ hmem
  linarith

/-- Upper bound: if `E` bounds every arc value then `ML v ≤ max (1/(N+1)) E`. -/
theorem two_entry_upper {k N r1 r2 w1 w2 : ℕ} (hN : 2 ≤ N)
    (h1 : N < 2 * r1) (h1' : r1 ≤ N) (h2 : N < 2 * r2) (h2' : r2 ≤ N)
    (hg : ¬ Nat.Coprime r1 r2)
    (v : Fin (k + 1) → ℤ)
    (hret : ∀ x : ℕ, 1 ≤ x → x ≤ N → x ≠ r1 → x ≠ r2 → ∃ i, v i = (x : ℤ))
    (hw1 : ∃ i, v i = (w1 : ℤ)) (hw2 : ∃ i, v i = (w2 : ℤ))
    (E : ℝ) (hE : ∀ y ∈ ArcSet N r1 r2 w1 w2, y ≤ E) :
    ML v ≤ max (1 / ((N : ℝ) + 1)) E := by
  apply ML_le_of_cover
  intro t
  by_contra hcon
  push Not at hcon
  have hcc : 1 / ((N : ℝ) + 1) ≤ max (1 / ((N : ℝ) + 1)) E := le_max_left _ _
  have hcE : E ≤ max (1 / ((N : ℝ) + 1)) E := le_max_right _ _
  have hx : ∀ x : ℕ, 1 ≤ x → x ≤ N → x ≠ r1 → x ≠ r2 →
      max (1 / ((N : ℝ) + 1)) E < nearestIntDist ((x : ℝ) * t) := by
    intro x hx1 hxN hxa hxb
    obtain ⟨i, hi⟩ := hret x hx1 hxN hxa hxb
    have := hcon i
    have e : ((v i : ℤ) : ℝ) = (x : ℝ) := by rw [hi]; norm_cast
    rwa [e] at this
  have hn1 : max (1 / ((N : ℝ) + 1)) E < nearestIntDist ((w1 : ℝ) * t) := by
    obtain ⟨i, hi⟩ := hw1
    have := hcon i
    have e : ((v i : ℤ) : ℝ) = (w1 : ℝ) := by rw [hi]; norm_cast
    rwa [e] at this
  have hn2 : max (1 / ((N : ℝ) + 1)) E < nearestIntDist ((w2 : ℝ) * t) := by
    obtain ⟨i, hi⟩ := hw2
    have := hcon i
    have e : ((v i : ℤ) : ℝ) = (w2 : ℝ) := by rw [hi]; norm_cast
    rwa [e] at this
  obtain ⟨j, q, hq0, hqN, hqd⟩ := Real.exists_int_int_abs_mul_sub_le t (n := N) (by omega)
  obtain ⟨qn, hqn⟩ : ∃ qn : ℕ, (qn : ℤ) = q := ⟨q.toNat, Int.toNat_of_nonneg (by omega)⟩
  have hqnR : (qn : ℝ) = (q : ℝ) := by exact_mod_cast hqn
  have hqnN : qn ≤ N := by
    have : (qn : ℤ) ≤ N := by rw [hqn]; exact_mod_cast hqN
    exact_mod_cast this
  have hq12 : qn = r1 ∨ qn = r2 := by
    by_contra hne
    push Not at hne
    have h3 := hx qn (by omega) hqnN hne.1 hne.2
    rw [hqnR] at h3
    have h4 := nearestIntDist_le_dist ((q : ℝ) * t) j
    linarith
  have hqNle : qn ≤ N := hqnN
  have hqlt : N < 2 * qn := by rcases hq12 with h | h <;> omega
  have hGq : ∀ x : ℕ, (x = r1 ∨ x = r2) → x ≠ qn → ¬ Nat.Coprime x qn := by
    intro x hx' hxq hco
    rcases hq12 with h | h <;> rcases hx' with h' | h'
    · exact hxq (h'.trans h.symm)
    · rw [h', h] at hco
      exact hg hco.symm
    · rw [h', h] at hco
      exact hg hco
    · exact hxq (h'.trans h.symm)
  have hq' : (q : ℝ) = qn := hqnR.symm
  rw [hq'] at hqd
  obtain ⟨hl, hu⟩ := abs_le.mp hqd
  rcases le_or_gt 0 ((qn : ℝ) * t - j) with hη | hη
  · exact two_core hN h1 h2 hq12 hqNle hGq _ hcc E hE hcE t j ((qn : ℝ) * t - j) (by ring) hη hu
      hx hn1 hn2
  · refine two_core hN h1 h2 hq12 hqNle hGq _ hcc E hE hcE (-t) (-j) (-((qn : ℝ) * t - j))
      (by push_cast; ring) (by linarith) (by linarith) ?_ ?_ ?_
    · intro x hx1 hxN hxa hxb
      have := hx x hx1 hxN hxa hxb
      rwa [show (x : ℝ) * (-t) = -((x : ℝ) * t) by ring, nearestIntDist_neg]
    · rwa [show (w1 : ℝ) * (-t) = -((w1 : ℝ) * t) by ring, nearestIntDist_neg]
    · rwa [show (w2 : ℝ) * (-t) = -((w2 : ℝ) * t) by ring, nearestIntDist_neg]

end Gap
end Sext6
end LRSpectrumFull
