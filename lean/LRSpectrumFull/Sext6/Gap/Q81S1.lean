import LRSpectrumFull.Sext6.Gap.Q81Core

/-!
# Q8.1, Theorem C for `N = 5..9`, both multipliers large: the analytic toolbox  [2026-11-25]

Source: the accompanying notes on Zhang's Question 8.1 section 3 (Lemma 3), made uniform in the multipliers.
`N = k + 1`, `N < 2 r1`, `r1 < r2 ≤ N`, `gcd(r1, r2) = 1`, `V = v2Fam k r1 r2 m1 m2`.

* `good_eta_piece`  : on any interval `(y1, y1 + ℓ]` the set where `‖x0 - α η‖ < τ` is not everything,
  as soon as `(α ℓ + 2 τ + 1)(2 τ/α) < ℓ`.
* `nid_nat_div`     : integer certificate for `1/N ≤ ‖n/D‖`.
* `classR2_core`, `classR1_core` : the time `t = (c + η)/r2` (resp. `/r1`): retained speeds are far for every
  admissible `η`; what is left is `‖m2 η‖` and `‖m1/r2 - (m1 r1/r2) η‖` (resp. the roles of `m1, m2`, `r1, r2` swapped).
* `chk2_sound`, `chk1_sound` : explicit rational `η = p/q`, checked by integer arithmetic.
* `R1_sound`  : the counting regime, as one integer inequality (`caseII_ML` with general multipliers).
* `S2_sound`, `S1_sound` : the piece regime (one multiplier small, the other arbitrary large).
No `sorry`, no `axiom`.

Convention: `N = k + 1` is the number of speeds of the vector `v : Fin (k+1) → ℤ`. Speeds are the moving runners; the runner at rest is not counted, so a vector of `N` speeds means `N + 1` runners and the Lonely Runner value is `1/(N+1)`.
Hypotheses: those of the individual statements (numerical bounds, structural conditions and, where named in the list above, window predicates such as `PrimeWin`, `CopWin`, `PrimeWindow7`, which later modules discharge for explicit ranges). The unproved predicates `DusartPi`, `LRCHyp`, `CopWinHyp` are not hypotheses of any statement in this module.
Axiom audit: covered by `Axioms22` (`#print axioms`; declarations not printed there are bricks of printed ones, so their axioms are bounded by the printed lines).
-/

namespace LRSpectrumFull
namespace Sext6
namespace Gap

open MeasureTheory

/-- On `(y1, y1 + ℓ]` some `η` has `τ ≤ ‖x0 - α η‖` once `(α ℓ + 2 τ + 1)(2 τ/α) < ℓ`. -/
theorem good_eta_piece {τ y1 ℓ α x0 : ℝ} (hτ0 : 0 < τ) (hℓ : 0 < ℓ) (hα : 0 < α)
    (hfin : (α * ℓ + 2 * τ + 1) * (2 * τ / α) < ℓ) :
    ∃ η : ℝ, y1 < η ∧ η ≤ y1 + ℓ ∧ τ ≤ nearestIntDist (x0 - α * η) := by
  by_contra hcon
  push Not at hcon
  have hsub : Set.Ioc (0 : ℝ) ℓ ⊆
      {x : ℝ | x ∈ Set.Ioc 0 ℓ ∧ nearestIntDist ((x0 - α * y1) - α * x) < τ} := by
    intro x hx
    refine ⟨hx, ?_⟩
    have h := hcon (y1 + x) (by linarith [hx.1]) (by linarith [hx.2])
    have e : x0 - α * (y1 + x) = (x0 - α * y1) - α * x := by ring
    rwa [e] at h
  have h2 := bad_set_two_vol (E := ℓ) (α := α) (x0 := x0 - α * y1) hτ0 hℓ hα
  have hvol := (measure_mono hsub).trans h2
  rw [Real.volume_Ioc, sub_zero] at hvol
  have hb2 : 0 ≤ (α * ℓ + 2 * τ + 1) * (2 * τ / α) := by positivity
  have := (ENNReal.ofReal_le_ofReal_iff hb2).mp hvol
  linarith

/-- Integer certificate: `1/N ≤ ‖n/D‖` from `D ≤ N (n mod D)` and `D ≤ N (D - n mod D)`. -/
theorem nid_nat_div {N : ℕ} (n D : ℕ) (hD : 0 < D) (hN : 2 ≤ N)
    (h1 : D ≤ N * (n % D)) (h2 : D ≤ N * (D - n % D)) :
    1 / (N : ℝ) ≤ nearestIntDist ((n : ℝ) / D) := by
  have hDpos : (0 : ℝ) < D := by exact_mod_cast hD
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hmod : n % D < D := Nat.mod_lt n hD
  obtain ⟨r, q, hr, hn⟩ : ∃ r q : ℕ, r = n % D ∧ n = r + D * q :=
    ⟨n % D, n / D, rfl, (Nat.mod_add_div n D).symm⟩
  rw [← hr] at h1 h2 hmod
  have e : (n : ℝ) / D = (r : ℝ) / D + ((q : ℤ) : ℝ) := by
    rw [hn]
    push_cast
    field_simp
  rw [e, nearestIntDist_add_int]
  apply nid_ge_inv hN
  · rw [div_le_div_iff₀ hNpos hDpos]
    have : (D : ℝ) ≤ N * r := by exact_mod_cast h1
    linarith
  · have h2' : (D : ℝ) ≤ N * ((D : ℝ) - r) := by
      have := (Nat.cast_sub hmod.le : ((D - r : ℕ) : ℝ) = (D : ℝ) - r)
      have h2c : (D : ℝ) ≤ N * ((D - r : ℕ) : ℝ) := by exact_mod_cast h2
      rw [this] at h2c
      exact h2c
    rw [div_le_iff₀ hDpos]
    have h3 : (D : ℝ) / N ≤ (D : ℝ) - r := by
      rw [div_le_iff₀ hNpos]
      linarith
    have h4 : (1 - 1 / (N : ℝ)) * D = D - D / N := by
      field_simp
    linarith

theorem cls2_setup {r1 r2 : ℕ} (hcop : Nat.Coprime r1 r2) :
    ∃ c k' : ℤ, (r1 : ℤ) * c + 1 = (r2 : ℤ) * k' ∧ IsCoprime (r2 : ℤ) c := by
  obtain ⟨u, w, huw⟩ : IsCoprime (r1 : ℤ) (r2 : ℤ) := Nat.isCoprime_iff_coprime.mpr hcop
  exact ⟨-u, w, by linear_combination (-1 : ℤ) * huw, ⟨w, -(r1 : ℤ), by linear_combination huw⟩⟩

theorem cls1_setup {r1 r2 u : ℕ} (hcop : Nat.Coprime r1 r2) (hu : r2 = r1 + u) :
    ∃ c k' k'' : ℤ, (u : ℤ) * c + 1 = (r1 : ℤ) * k' ∧ (r2 : ℤ) * c + 1 = (r1 : ℤ) * k'' ∧
      IsCoprime (r1 : ℤ) c := by
  obtain ⟨p, q, hpq⟩ : IsCoprime (r1 : ℤ) (r2 : ℤ) := Nat.isCoprime_iff_coprime.mpr hcop
  have huZ : (u : ℤ) = (r2 : ℤ) - r1 := by rw [hu]; push_cast; ring
  refine ⟨-q, p + q, p, ?_, ?_, ⟨p, -(r2 : ℤ), by linear_combination hpq⟩⟩
  · rw [huZ]; linear_combination (-1 : ℤ) * hpq
  · linear_combination (-1 : ℤ) * hpq

/-- The time `t = (c + η)/r2`: what remains are the two inserted speeds. -/
theorem classR2_core {k N r1 r2 m1 m2 : ℕ} (hk : k + 1 = N) (hr1 : N < 2 * r1) (h12 : r1 < r2)
    (h2N : r2 ≤ N) (hcop : Nat.Coprime r1 r2) (η : ℝ) (hη0 : 0 ≤ η)
    (hηN : (N : ℝ) * η ≤ 2 - (r2 : ℝ) / N)
    (hA : 1 / (N : ℝ) ≤ nearestIntDist ((m2 : ℝ) * η))
    (hB : 1 / (N : ℝ) ≤ nearestIntDist ((m1 : ℝ) / r2 - ((m1 : ℝ) * r1 / r2) * η)) :
    1 / (N : ℝ) ≤ ML (v2Fam k r1 r2 m1 m2) := by
  obtain ⟨c, k', hc, hcopc⟩ := cls2_setup hcop
  refine ML_v2Fam_ge hk (1 / (N : ℝ)) (((c : ℝ) + η) / (r2 : ℝ)) ?_ ?_ ?_
  · intro x hx1 hxN hxr1 hxr2
    exact retained_big hr1 h12 h2N c k' hc hcopc η hη0 hηN x hx1 hxN hxr1 hxr2
  · rw [nid_mul_blocker m1 r1 r2 c k' η (by omega) hc]
    exact hB
  · rw [nid_mul_mod m2 r2 c η (by omega)]
    exact hA

/-- The time `t = (c + η)/r1` (blockers `r2 - r1` and `r2`): the roles of `(r1, m1)` and `(r2, m2)`. -/
theorem classR1_core {k N r1 r2 m1 m2 : ℕ} (hk : k + 1 = N) (hr1 : N < 2 * r1) (h12 : r1 < r2)
    (h2N : r2 ≤ N) (hcop : Nat.Coprime r1 r2) (η : ℝ) (hη0 : 0 ≤ η)
    (hηN : (N : ℝ) * η ≤ 2 - (r1 : ℝ) / N)
    (hu : ((r2 - r1 : ℕ) : ℝ) * η ≤ 1 - (r1 : ℝ) / N)
    (hA : 1 / (N : ℝ) ≤ nearestIntDist ((m1 : ℝ) * η))
    (hB : 1 / (N : ℝ) ≤ nearestIntDist ((m2 : ℝ) / r1 - ((m2 : ℝ) * r2 / r1) * η)) :
    1 / (N : ℝ) ≤ ML (v2Fam k r1 r2 m1 m2) := by
  obtain ⟨u, hu0⟩ : ∃ u : ℕ, r2 = r1 + u := ⟨r2 - r1, by omega⟩
  have hu1 : 1 ≤ u := by omega
  have hur : r2 - r1 = u := by omega
  rw [hur] at hu
  obtain ⟨c, k', k'', hcu, hcr2, hcopc⟩ := cls1_setup hcop hu0
  refine ML_v2Fam_ge hk (1 / (N : ℝ)) (((c : ℝ) + η) / (r1 : ℝ)) ?_ ?_ ?_
  · intro x hx1 hxN hxr1 hxr2
    exact retained_small hr1 hu0 hu1 h2N c k' hcu hcopc η hη0 hηN hu x hx1 hxN hxr1 hxr2
  · rw [nid_mul_mod m1 r1 c η (by omega)]
    exact hA
  · rw [nid_mul_blocker m2 r2 r1 c k'' η (by omega) hcr2]
    exact hB

/-! ### Explicit rational `η = p/q` -/

/-- Integer certificate for the time `η = p/q` in the class of `r2`. -/
def chk2P (N r1 r2 m1 m2 p q : ℕ) : Prop :=
  N * N * p ≤ (2 * N - r2) * q ∧ r1 * p ≤ q ∧ 0 < q ∧
    q ≤ N * ((m2 * p) % q) ∧ q ≤ N * (q - (m2 * p) % q) ∧
    q * r2 ≤ N * ((m1 * (q - r1 * p)) % (q * r2)) ∧
    q * r2 ≤ N * (q * r2 - (m1 * (q - r1 * p)) % (q * r2))

instance (N r1 r2 m1 m2 p q : ℕ) : Decidable (chk2P N r1 r2 m1 m2 p q) := by
  unfold chk2P; infer_instance

/-- Integer certificate for the time `η = p/q` in the class of `r1`. -/
def chk1P (N r1 r2 m1 m2 p q : ℕ) : Prop :=
  N * N * p ≤ (2 * N - r1) * q ∧ N * (r2 - r1) * p ≤ (N - r1) * q ∧ r2 * p ≤ q ∧ 0 < q ∧
    q ≤ N * ((m1 * p) % q) ∧ q ≤ N * (q - (m1 * p) % q) ∧
    q * r1 ≤ N * ((m2 * (q - r2 * p)) % (q * r1)) ∧
    q * r1 ≤ N * (q * r1 - (m2 * (q - r2 * p)) % (q * r1))

instance (N r1 r2 m1 m2 p q : ℕ) : Decidable (chk1P N r1 r2 m1 m2 p q) := by
  unfold chk1P; infer_instance

theorem chk2_sound {k N r1 r2 m1 m2 p q : ℕ} (hk : k + 1 = N) (hr1 : N < 2 * r1) (h12 : r1 < r2)
    (h2N : r2 ≤ N) (hcop : Nat.Coprime r1 r2) (h : chk2P N r1 r2 m1 m2 p q) :
    1 / (N : ℝ) ≤ ML (v2Fam k r1 r2 m1 m2) := by
  obtain ⟨hE, hpq, hq, hA1, hA2, hB1, hB2⟩ := h
  have hN2 : 2 ≤ N := by omega
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hqpos : (0 : ℝ) < q := by exact_mod_cast hq
  have hr2pos : (0 : ℝ) < r2 := by exact_mod_cast (by omega : 0 < r2)
  refine classR2_core hk hr1 h12 h2N hcop ((p : ℝ) / q) (by positivity) ?_ ?_ ?_
  · have hEc : (N : ℝ) * N * p ≤ (2 * N - r2) * q := by
      have h1 : ((N * N * p : ℕ) : ℝ) ≤ (((2 * N - r2) * q : ℕ) : ℝ) := by exact_mod_cast hE
      have hs : ((2 * N - r2 : ℕ) : ℝ) = 2 * (N : ℝ) - r2 := by
        rw [Nat.cast_sub (by omega)]; push_cast; ring
      push_cast [hs] at h1
      linarith
    have e1 : (N : ℝ) * ((p : ℝ) / q) = ((N : ℝ) * p) / q := by ring
    have e2 : (2 : ℝ) - (r2 : ℝ) / N = (2 * N - r2) / N := by field_simp
    rw [e1, e2, div_le_div_iff₀ hqpos hNpos]
    linarith
  · have e : (m2 : ℝ) * ((p : ℝ) / q) = ((m2 * p : ℕ) : ℝ) / q := by push_cast; ring
    rw [e]
    exact nid_nat_div (m2 * p) q hq hN2 hA1 hA2
  · have hs : ((q - r1 * p : ℕ) : ℝ) = (q : ℝ) - r1 * p := by
      rw [Nat.cast_sub hpq]; push_cast; ring
    have e : (m1 : ℝ) / r2 - ((m1 : ℝ) * r1 / r2) * ((p : ℝ) / q) =
        ((m1 * (q - r1 * p) : ℕ) : ℝ) / ((q * r2 : ℕ) : ℝ) := by
      simp only [Nat.cast_mul, hs]
      field_simp
      try ring
    rw [e]
    have := nid_nat_div (N := N) (m1 * (q - r1 * p)) (q * r2) (Nat.mul_pos hq (by omega)) hN2 hB1 hB2
    exact this

theorem chk1_sound {k N r1 r2 m1 m2 p q : ℕ} (hk : k + 1 = N) (hr1 : N < 2 * r1) (h12 : r1 < r2)
    (h2N : r2 ≤ N) (hcop : Nat.Coprime r1 r2) (h : chk1P N r1 r2 m1 m2 p q) :
    1 / (N : ℝ) ≤ ML (v2Fam k r1 r2 m1 m2) := by
  obtain ⟨hE, hU, hpq, hq, hA1, hA2, hB1, hB2⟩ := h
  have hN2 : 2 ≤ N := by omega
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hqpos : (0 : ℝ) < q := by exact_mod_cast hq
  have hr1pos : (0 : ℝ) < r1 := by exact_mod_cast (by omega : 0 < r1)
  refine classR1_core hk hr1 h12 h2N hcop ((p : ℝ) / q) (by positivity) ?_ ?_ ?_ ?_
  · have hEc : (N : ℝ) * N * p ≤ (2 * N - r1) * q := by
      have h1 : ((N * N * p : ℕ) : ℝ) ≤ (((2 * N - r1) * q : ℕ) : ℝ) := by exact_mod_cast hE
      have hs : ((2 * N - r1 : ℕ) : ℝ) = 2 * (N : ℝ) - r1 := by
        rw [Nat.cast_sub (by omega)]; push_cast; ring
      push_cast [hs] at h1
      linarith
    have e1 : (N : ℝ) * ((p : ℝ) / q) = ((N : ℝ) * p) / q := by ring
    have e2 : (2 : ℝ) - (r1 : ℝ) / N = (2 * N - r1) / N := by field_simp
    rw [e1, e2, div_le_div_iff₀ hqpos hNpos]
    linarith
  · have hUc : (N : ℝ) * ((r2 : ℝ) - r1) * p ≤ ((N : ℝ) - r1) * q := by
      have h1 : ((N * (r2 - r1) * p : ℕ) : ℝ) ≤ (((N - r1) * q : ℕ) : ℝ) := by exact_mod_cast hU
      have hs : ((r2 - r1 : ℕ) : ℝ) = (r2 : ℝ) - r1 := by
        rw [Nat.cast_sub (by omega)]
      have hs2 : ((N - r1 : ℕ) : ℝ) = (N : ℝ) - r1 := by
        rw [Nat.cast_sub (by omega)]
      push_cast [hs, hs2] at h1
      linarith
    have hs : ((r2 - r1 : ℕ) : ℝ) = (r2 : ℝ) - r1 := by rw [Nat.cast_sub (by omega)]
    rw [hs]
    have e1 : ((r2 : ℝ) - r1) * ((p : ℝ) / q) = (((r2 : ℝ) - r1) * p) / q := by ring
    have e2 : (1 : ℝ) - (r1 : ℝ) / N = ((N : ℝ) - r1) / N := by field_simp
    rw [e1, e2, div_le_div_iff₀ hqpos hNpos]
    nlinarith
  · have e : (m1 : ℝ) * ((p : ℝ) / q) = ((m1 * p : ℕ) : ℝ) / q := by push_cast; ring
    rw [e]
    exact nid_nat_div (m1 * p) q hq hN2 hA1 hA2
  · have hs : ((q - r2 * p : ℕ) : ℝ) = (q : ℝ) - r2 * p := by
      rw [Nat.cast_sub hpq]; push_cast; ring
    have e : (m2 : ℝ) / r1 - ((m2 : ℝ) * r2 / r1) * ((p : ℝ) / q) =
        ((m2 * (q - r2 * p) : ℕ) : ℝ) / ((q * r1 : ℕ) : ℝ) := by
      simp only [Nat.cast_mul, hs]
      field_simp
      try ring
    rw [e]
    exact nid_nat_div (N := N) (m2 * (q - r2 * p)) (q * r1) (Nat.mul_pos hq (by omega)) hN2 hB1 hB2

/-! ### The counting regime as one integer inequality -/

/-- Counting regime: `N (N+2)(m1 r1 + 2 r2 m2) < (2N - r2)(N - 4) m1 m2 r1`. -/
def R1P (N r1 r2 m1 m2 : ℕ) : Prop :=
  N * (N + 2) * (m1 * r1 + 2 * r2 * m2) < (2 * N - r2) * (N - 4) * m1 * m2 * r1

instance (N r1 r2 m1 m2 : ℕ) : Decidable (R1P N r1 r2 m1 m2) := by
  unfold R1P; infer_instance

theorem R1_sound {k N r1 r2 m1 m2 : ℕ} (hk : k + 1 = N) (hr1 : N < 2 * r1) (h12 : r1 < r2)
    (h2N : r2 ≤ N) (hcop : Nat.Coprime r1 r2) (hm1 : 1 ≤ m1) (hm2 : 1 ≤ m2)
    (hI : R1P N r1 r2 m1 m2) : 1 / (N : ℝ) ≤ ML (v2Fam k r1 r2 m1 m2) := by
  have hN2 : 2 ≤ N := by omega
  have hN4 : 4 < N := by
    by_contra hcon
    have h4 : N - 4 = 0 := by omega
    unfold R1P at hI
    rw [h4] at hI
    simp at hI
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hr1pos : (0 : ℝ) < r1 := by exact_mod_cast (by omega : 0 < r1)
  have hr2pos : (0 : ℝ) < r2 := by exact_mod_cast (by omega : 0 < r2)
  have hm1R : (1 : ℝ) ≤ m1 := by exact_mod_cast hm1
  have hm2R : (1 : ℝ) ≤ m2 := by exact_mod_cast hm2
  have hm1pos : (0 : ℝ) < m1 := by linarith
  have hm2pos : (0 : ℝ) < m2 := by linarith
  obtain ⟨E, hE⟩ : ∃ E : ℝ, E = (2 * (N : ℝ) - r2) / (N : ℝ) ^ 2 := ⟨_, rfl⟩
  have hr2N : (r2 : ℝ) ≤ N := by exact_mod_cast h2N
  have hEpos : 0 < E := by
    rw [hE]
    exact div_pos (by linarith) (pow_pos hNpos 2)
  have hNE : (N : ℝ) * E = 2 - (r2 : ℝ) / N := by
    rw [hE]
    field_simp
  have hαpos : 0 < (m1 : ℝ) * r1 / r2 := by positivity
  have hτ0 : (0 : ℝ) < 1 / (N : ℝ) := one_div_pos.mpr hNpos
  have hN5R : (5 : ℝ) ≤ N := by exact_mod_cast hN4
  have hτ1 : 1 / (N : ℝ) ≤ 1 := by
    rw [div_le_iff₀ hNpos]
    linarith
  have hI' : ((N * (N + 2) * (m1 * r1 + 2 * r2 * m2) : ℕ) : ℝ) <
      (((2 * N - r2) * (N - 4) * m1 * m2 * r1 : ℕ) : ℝ) := by
    exact_mod_cast hI
  have hs1 : ((2 * N - r2 : ℕ) : ℝ) = 2 * (N : ℝ) - r2 := by
    rw [Nat.cast_sub (by omega)]; push_cast; ring
  have hs2 : ((N - 4 : ℕ) : ℝ) = (N : ℝ) - 4 := by
    rw [Nat.cast_sub (by omega)]; push_cast; ring
  push_cast [hs1, hs2] at hI'
  have hgap : 4 * (1 / (N : ℝ)) * E + (1 / (N : ℝ)) * (1 + 2 * (1 / (N : ℝ))) * (1 / (m2 : ℝ)) +
      2 * ((1 / (N : ℝ)) * (1 + 2 * (1 / (N : ℝ))) * (1 / ((m1 : ℝ) * r1 / r2))) < E := by
    have hdiff : E - (4 * (1 / (N : ℝ)) * E +
        (1 / (N : ℝ)) * (1 + 2 * (1 / (N : ℝ))) * (1 / (m2 : ℝ)) +
        2 * ((1 / (N : ℝ)) * (1 + 2 * (1 / (N : ℝ))) * (1 / ((m1 : ℝ) * r1 / r2)))) =
        ((2 * N - (r2 : ℝ)) * (N - 4) * m1 * m2 * r1 -
          N * (N + 2) * (m1 * r1 + 2 * r2 * m2)) / ((N : ℝ) ^ 3 * m1 * m2 * r1) := by
      rw [hE]
      field_simp
      ring
    have : 0 < E - (4 * (1 / (N : ℝ)) * E +
        (1 / (N : ℝ)) * (1 + 2 * (1 / (N : ℝ))) * (1 / (m2 : ℝ)) +
        2 * ((1 / (N : ℝ)) * (1 + 2 * (1 / (N : ℝ))) * (1 / ((m1 : ℝ) * r1 / r2)))) := by
      rw [hdiff]
      exact div_pos (by linarith) (by positivity)
    linarith
  have hfin : 1 / (N : ℝ) / (m2 : ℝ) + ((m2 : ℝ) * E + 1 / (N : ℝ)) * (2 * (1 / (N : ℝ)) / (m2 : ℝ)) +
      (((m1 : ℝ) * r1 / r2) * E + 2 * (1 / (N : ℝ)) + 1) *
        (2 * (1 / (N : ℝ)) / ((m1 : ℝ) * r1 / r2)) < E := by
    have key : 1 / (N : ℝ) / (m2 : ℝ) + ((m2 : ℝ) * E + 1 / (N : ℝ)) * (2 * (1 / (N : ℝ)) / (m2 : ℝ)) +
        (((m1 : ℝ) * r1 / r2) * E + 2 * (1 / (N : ℝ)) + 1) *
          (2 * (1 / (N : ℝ)) / ((m1 : ℝ) * r1 / r2)) =
        4 * (1 / (N : ℝ)) * E + (1 / (N : ℝ)) * (1 + 2 * (1 / (N : ℝ))) * (1 / (m2 : ℝ)) +
      2 * ((1 / (N : ℝ)) * (1 + 2 * (1 / (N : ℝ))) * (1 / ((m1 : ℝ) * r1 / r2))) := by
      field_simp
      ring
    rw [key]
    exact hgap
  obtain ⟨η, hη0, hηE, hA, hB⟩ := good_eta_exists (τ := 1 / (N : ℝ)) (E := E) (a := (m2 : ℝ))
    (α := (m1 : ℝ) * r1 / r2) (x0 := (m1 : ℝ) / r2) hτ0 hτ1 hEpos hm2pos hαpos hfin
  have hηN : (N : ℝ) * η ≤ 2 - (r2 : ℝ) / N := by
    rw [← hNE]
    exact mul_le_mul_of_nonneg_left hηE hNpos.le
  exact classR2_core hk hr1 h12 h2N hcop η hη0.le hηN hA hB

/-! ### The piece regime -/

/-- Class `r2`, `A`-piece `(1/(N m2), cn/cd]`. -/
def S2P (N r1 r2 m1 m2 cn cd : ℕ) : Prop :=
  0 < cd ∧ N * N * cn ≤ (2 * N - r2) * cd ∧ m2 * cn * N ≤ (N - 1) * cd ∧ cd < N * m2 * cn ∧
    2 * (N + 2) * r2 * m2 * cd < m1 * r1 * (N * m2 * cn - cd) * (N - 2)

instance (N r1 r2 m1 m2 cn cd : ℕ) : Decidable (S2P N r1 r2 m1 m2 cn cd) := by
  unfold S2P; infer_instance

theorem S2_sound {k N r1 r2 m1 m2 cn cd : ℕ} (hk : k + 1 = N) (hr1 : N < 2 * r1) (h12 : r1 < r2)
    (h2N : r2 ≤ N) (hcop : Nat.Coprime r1 r2) (hm1 : 1 ≤ m1) (hm2 : 1 ≤ m2)
    (h : S2P N r1 r2 m1 m2 cn cd) : 1 / (N : ℝ) ≤ ML (v2Fam k r1 r2 m1 m2) := by
  obtain ⟨hcd, hE, hA, hpos, hI⟩ := h
  have hN2 : 2 ≤ N := by omega
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hr1pos : (0 : ℝ) < r1 := by exact_mod_cast (by omega : 0 < r1)
  have hr2pos : (0 : ℝ) < r2 := by exact_mod_cast (by omega : 0 < r2)
  have hm1pos : (0 : ℝ) < m1 := by exact_mod_cast hm1
  have hm2pos : (0 : ℝ) < m2 := by exact_mod_cast hm2
  have hcdpos : (0 : ℝ) < cd := by exact_mod_cast hcd
  have hcnpos : 0 < cn := by
    rcases Nat.eq_zero_or_pos cn with h0 | h0
    · rw [h0] at hpos; simp at hpos
    · exact h0
  have hcnR : (0 : ℝ) < cn := by exact_mod_cast hcnpos
  have hN2R : (2 : ℝ) ≤ N := by exact_mod_cast hN2
  have hτ0 : (0 : ℝ) < 1 / (N : ℝ) := one_div_pos.mpr hNpos
  have hposR : (cd : ℝ) < N * m2 * cn := by exact_mod_cast hpos
  have hy1 : 1 / ((N : ℝ) * m2) < (cn : ℝ) / cd := by
    rw [div_lt_div_iff₀ (by positivity) hcdpos]
    nlinarith
  obtain ⟨ℓ, hℓ⟩ : ∃ ℓ : ℝ, ℓ = (cn : ℝ) / cd - 1 / ((N : ℝ) * m2) := ⟨_, rfl⟩
  have hℓpos : 0 < ℓ := by rw [hℓ]; linarith
  obtain ⟨α, hα⟩ : ∃ α : ℝ, α = (m1 : ℝ) * r1 / r2 := ⟨_, rfl⟩
  have hαpos : 0 < α := by rw [hα]; positivity
  have hXI : 2 * (1 / (N : ℝ)) * (1 + 2 * (1 / (N : ℝ))) <
      α * ℓ * (1 - 2 * (1 / (N : ℝ))) := by
    have hI' : ((2 * (N + 2) * r2 * m2 * cd : ℕ) : ℝ) <
        ((m1 * r1 * (N * m2 * cn - cd) * (N - 2) : ℕ) : ℝ) := by exact_mod_cast hI
    have hs1 : ((N * m2 * cn - cd : ℕ) : ℝ) = (N : ℝ) * m2 * cn - cd := by
      rw [Nat.cast_sub hpos.le]; push_cast; ring
    have hs2 : ((N - 2 : ℕ) : ℝ) = (N : ℝ) - 2 := by
      rw [Nat.cast_sub (by omega)]; push_cast; ring
    push_cast [hs1, hs2] at hI'
    have hdiff : α * ℓ * (1 - 2 * (1 / (N : ℝ))) - 2 * (1 / (N : ℝ)) * (1 + 2 * (1 / (N : ℝ))) =
        ((m1 : ℝ) * r1 * ((N : ℝ) * m2 * cn - cd) * ((N : ℝ) - 2) -
          2 * ((N : ℝ) + 2) * r2 * m2 * cd) / ((r2 : ℝ) * (N : ℝ) ^ 2 * m2 * cd) := by
      rw [hα, hℓ]
      field_simp
      try ring
    have : 0 < α * ℓ * (1 - 2 * (1 / (N : ℝ))) - 2 * (1 / (N : ℝ)) * (1 + 2 * (1 / (N : ℝ))) := by
      rw [hdiff]
      exact div_pos (by linarith) (by positivity)
    linarith
  have hfin : (α * ℓ + 2 * (1 / (N : ℝ)) + 1) * (2 * (1 / (N : ℝ)) / α) < ℓ := by
    have e : (α * ℓ + 2 * (1 / (N : ℝ)) + 1) * (2 * (1 / (N : ℝ)) / α) =
        ((α * ℓ + 2 * (1 / (N : ℝ)) + 1) * (2 * (1 / (N : ℝ)))) / α := by ring
    rw [e, div_lt_iff₀ hαpos]
    nlinarith
  obtain ⟨η, hη1, hη2, hB⟩ := good_eta_piece (τ := 1 / (N : ℝ)) (y1 := 1 / ((N : ℝ) * m2)) (ℓ := ℓ)
    (α := α) (x0 := (m1 : ℝ) / r2) hτ0 hℓpos hαpos hfin
  have hη2' : η ≤ (cn : ℝ) / cd := by rw [hℓ] at hη2; linarith
  have hη0 : 0 < η := lt_of_le_of_lt (by positivity) hη1
  refine classR2_core hk hr1 h12 h2N hcop η hη0.le ?_ ?_ (by rw [← hα]; exact hB)
  · have hEc : (N : ℝ) * N * cn ≤ (2 * N - r2) * cd := by
      have h1 : ((N * N * cn : ℕ) : ℝ) ≤ (((2 * N - r2) * cd : ℕ) : ℝ) := by exact_mod_cast hE
      have hs : ((2 * N - r2 : ℕ) : ℝ) = 2 * (N : ℝ) - r2 := by
        rw [Nat.cast_sub (by omega)]; push_cast; ring
      push_cast [hs] at h1
      linarith
    have h3 : (N : ℝ) * η ≤ (N : ℝ) * ((cn : ℝ) / cd) := mul_le_mul_of_nonneg_left hη2' hNpos.le
    have e1 : (N : ℝ) * ((cn : ℝ) / cd) = ((N : ℝ) * cn) / cd := by ring
    have e2 : (2 : ℝ) - (r2 : ℝ) / N = (2 * N - r2) / N := by field_simp
    have h4 : ((N : ℝ) * cn) / cd ≤ (2 * N - r2) / N := by
      rw [div_le_div_iff₀ hcdpos hNpos]
      linarith
    rw [e2]
    linarith
  · have hAc : (m2 : ℝ) * cn * N ≤ ((N : ℝ) - 1) * cd := by
      have h1 : ((m2 * cn * N : ℕ) : ℝ) ≤ (((N - 1) * cd : ℕ) : ℝ) := by exact_mod_cast hA
      have hs : ((N - 1 : ℕ) : ℝ) = (N : ℝ) - 1 := by
        rw [Nat.cast_sub (by omega)]; push_cast; ring
      push_cast [hs] at h1
      linarith
    apply nid_ge_inv hN2
    · have : 1 / ((N : ℝ) * m2) < η := hη1
      have h5 : (1 : ℝ) / N = (m2 : ℝ) * (1 / ((N : ℝ) * m2)) := by field_simp
      rw [h5]
      exact (mul_le_mul_of_nonneg_left this.le hm2pos.le)
    · have h3 : (m2 : ℝ) * η ≤ (m2 : ℝ) * ((cn : ℝ) / cd) := mul_le_mul_of_nonneg_left hη2' hm2pos.le
      have h4 : (m2 : ℝ) * ((cn : ℝ) / cd) ≤ 1 - 1 / (N : ℝ) := by
        have e : (m2 : ℝ) * ((cn : ℝ) / cd) = ((m2 : ℝ) * cn) / cd := by ring
        have e3 : (1 : ℝ) - 1 / (N : ℝ) = ((N : ℝ) - 1) / N := by field_simp
        rw [e, e3, div_le_div_iff₀ hcdpos hNpos]
        linarith
      linarith

/-- Class `r1`, `A`-piece `(1/(N m1), cn/cd]`. -/
def S1P (N r1 r2 m1 m2 cn cd : ℕ) : Prop :=
  0 < cd ∧ N * N * cn ≤ (2 * N - r1) * cd ∧ N * (r2 - r1) * cn ≤ (N - r1) * cd ∧
    m1 * cn * N ≤ (N - 1) * cd ∧ cd < N * m1 * cn ∧
    2 * (N + 2) * r1 * m1 * cd < m2 * r2 * (N * m1 * cn - cd) * (N - 2)

instance (N r1 r2 m1 m2 cn cd : ℕ) : Decidable (S1P N r1 r2 m1 m2 cn cd) := by
  unfold S1P; infer_instance

theorem S1_sound {k N r1 r2 m1 m2 cn cd : ℕ} (hk : k + 1 = N) (hr1 : N < 2 * r1) (h12 : r1 < r2)
    (h2N : r2 ≤ N) (hcop : Nat.Coprime r1 r2) (hm1 : 1 ≤ m1) (hm2 : 1 ≤ m2)
    (h : S1P N r1 r2 m1 m2 cn cd) : 1 / (N : ℝ) ≤ ML (v2Fam k r1 r2 m1 m2) := by
  obtain ⟨hcd, hE, hU, hA, hpos, hI⟩ := h
  have hN2 : 2 ≤ N := by omega
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hr1pos : (0 : ℝ) < r1 := by exact_mod_cast (by omega : 0 < r1)
  have hr2pos : (0 : ℝ) < r2 := by exact_mod_cast (by omega : 0 < r2)
  have hm1pos : (0 : ℝ) < m1 := by exact_mod_cast hm1
  have hm2pos : (0 : ℝ) < m2 := by exact_mod_cast hm2
  have hcdpos : (0 : ℝ) < cd := by exact_mod_cast hcd
  have hcnpos : 0 < cn := by
    rcases Nat.eq_zero_or_pos cn with h0 | h0
    · rw [h0] at hpos; simp at hpos
    · exact h0
  have hcnR : (0 : ℝ) < cn := by exact_mod_cast hcnpos
  have hN2R : (2 : ℝ) ≤ N := by exact_mod_cast hN2
  have hτ0 : (0 : ℝ) < 1 / (N : ℝ) := one_div_pos.mpr hNpos
  have hposR : (cd : ℝ) < N * m1 * cn := by exact_mod_cast hpos
  have hy1 : 1 / ((N : ℝ) * m1) < (cn : ℝ) / cd := by
    rw [div_lt_div_iff₀ (by positivity) hcdpos]
    nlinarith
  obtain ⟨ℓ, hℓ⟩ : ∃ ℓ : ℝ, ℓ = (cn : ℝ) / cd - 1 / ((N : ℝ) * m1) := ⟨_, rfl⟩
  have hℓpos : 0 < ℓ := by rw [hℓ]; linarith
  obtain ⟨α, hα⟩ : ∃ α : ℝ, α = (m2 : ℝ) * r2 / r1 := ⟨_, rfl⟩
  have hαpos : 0 < α := by rw [hα]; positivity
  have hXI : 2 * (1 / (N : ℝ)) * (1 + 2 * (1 / (N : ℝ))) <
      α * ℓ * (1 - 2 * (1 / (N : ℝ))) := by
    have hI' : ((2 * (N + 2) * r1 * m1 * cd : ℕ) : ℝ) <
        ((m2 * r2 * (N * m1 * cn - cd) * (N - 2) : ℕ) : ℝ) := by exact_mod_cast hI
    have hs1 : ((N * m1 * cn - cd : ℕ) : ℝ) = (N : ℝ) * m1 * cn - cd := by
      rw [Nat.cast_sub hpos.le]; push_cast; ring
    have hs2 : ((N - 2 : ℕ) : ℝ) = (N : ℝ) - 2 := by
      rw [Nat.cast_sub (by omega)]; push_cast; ring
    push_cast [hs1, hs2] at hI'
    have hdiff : α * ℓ * (1 - 2 * (1 / (N : ℝ))) - 2 * (1 / (N : ℝ)) * (1 + 2 * (1 / (N : ℝ))) =
        ((m2 : ℝ) * r2 * ((N : ℝ) * m1 * cn - cd) * ((N : ℝ) - 2) -
          2 * ((N : ℝ) + 2) * r1 * m1 * cd) / ((r1 : ℝ) * (N : ℝ) ^ 2 * m1 * cd) := by
      rw [hα, hℓ]
      field_simp
      try ring
    have : 0 < α * ℓ * (1 - 2 * (1 / (N : ℝ))) - 2 * (1 / (N : ℝ)) * (1 + 2 * (1 / (N : ℝ))) := by
      rw [hdiff]
      exact div_pos (by linarith) (by positivity)
    linarith
  have hfin : (α * ℓ + 2 * (1 / (N : ℝ)) + 1) * (2 * (1 / (N : ℝ)) / α) < ℓ := by
    have e : (α * ℓ + 2 * (1 / (N : ℝ)) + 1) * (2 * (1 / (N : ℝ)) / α) =
        ((α * ℓ + 2 * (1 / (N : ℝ)) + 1) * (2 * (1 / (N : ℝ)))) / α := by ring
    rw [e, div_lt_iff₀ hαpos]
    nlinarith
  obtain ⟨η, hη1, hη2, hB⟩ := good_eta_piece (τ := 1 / (N : ℝ)) (y1 := 1 / ((N : ℝ) * m1)) (ℓ := ℓ)
    (α := α) (x0 := (m2 : ℝ) / r1) hτ0 hℓpos hαpos hfin
  have hη2' : η ≤ (cn : ℝ) / cd := by rw [hℓ] at hη2; linarith
  have hη0 : 0 < η := lt_of_le_of_lt (by positivity) hη1
  refine classR1_core hk hr1 h12 h2N hcop η hη0.le ?_ ?_ ?_ (by rw [← hα]; exact hB)
  · have hEc : (N : ℝ) * N * cn ≤ (2 * N - r1) * cd := by
      have h1 : ((N * N * cn : ℕ) : ℝ) ≤ (((2 * N - r1) * cd : ℕ) : ℝ) := by exact_mod_cast hE
      have hs : ((2 * N - r1 : ℕ) : ℝ) = 2 * (N : ℝ) - r1 := by
        rw [Nat.cast_sub (by omega)]; push_cast; ring
      push_cast [hs] at h1
      linarith
    have h3 : (N : ℝ) * η ≤ (N : ℝ) * ((cn : ℝ) / cd) := mul_le_mul_of_nonneg_left hη2' hNpos.le
    have e1 : (N : ℝ) * ((cn : ℝ) / cd) = ((N : ℝ) * cn) / cd := by ring
    have e2 : (2 : ℝ) - (r1 : ℝ) / N = (2 * N - r1) / N := by field_simp
    have h4 : ((N : ℝ) * cn) / cd ≤ (2 * N - r1) / N := by
      rw [div_le_div_iff₀ hcdpos hNpos]
      linarith
    rw [e2]
    linarith
  · have hUc : (N : ℝ) * ((r2 : ℝ) - r1) * cn ≤ ((N : ℝ) - r1) * cd := by
      have h1 : ((N * (r2 - r1) * cn : ℕ) : ℝ) ≤ (((N - r1) * cd : ℕ) : ℝ) := by exact_mod_cast hU
      have hs : ((r2 - r1 : ℕ) : ℝ) = (r2 : ℝ) - r1 := by
        rw [Nat.cast_sub (by omega)]
      have hs2 : ((N - r1 : ℕ) : ℝ) = (N : ℝ) - r1 := by
        rw [Nat.cast_sub (by omega)]
      push_cast [hs, hs2] at h1
      linarith
    have hs : ((r2 - r1 : ℕ) : ℝ) = (r2 : ℝ) - r1 := by rw [Nat.cast_sub (by omega)]
    rw [hs]
    have hu0 : (0 : ℝ) ≤ (r2 : ℝ) - r1 := by
      have : (r1 : ℝ) ≤ r2 := by exact_mod_cast h12.le
      linarith
    have h3 : ((r2 : ℝ) - r1) * η ≤ ((r2 : ℝ) - r1) * ((cn : ℝ) / cd) :=
      mul_le_mul_of_nonneg_left hη2' hu0
    have e1 : ((r2 : ℝ) - r1) * ((cn : ℝ) / cd) = (((r2 : ℝ) - r1) * cn) / cd := by ring
    have e2 : (1 : ℝ) - (r1 : ℝ) / N = ((N : ℝ) - r1) / N := by field_simp
    have h4 : (((r2 : ℝ) - r1) * cn) / cd ≤ ((N : ℝ) - r1) / N := by
      rw [div_le_div_iff₀ hcdpos hNpos]
      nlinarith
    rw [e2]
    linarith
  · have hAc : (m1 : ℝ) * cn * N ≤ ((N : ℝ) - 1) * cd := by
      have h1 : ((m1 * cn * N : ℕ) : ℝ) ≤ (((N - 1) * cd : ℕ) : ℝ) := by exact_mod_cast hA
      have hs : ((N - 1 : ℕ) : ℝ) = (N : ℝ) - 1 := by
        rw [Nat.cast_sub (by omega)]; push_cast; ring
      push_cast [hs] at h1
      linarith
    apply nid_ge_inv hN2
    · have : 1 / ((N : ℝ) * m1) < η := hη1
      have h5 : (1 : ℝ) / N = (m1 : ℝ) * (1 / ((N : ℝ) * m1)) := by field_simp
      rw [h5]
      exact (mul_le_mul_of_nonneg_left this.le hm1pos.le)
    · have h3 : (m1 : ℝ) * η ≤ (m1 : ℝ) * ((cn : ℝ) / cd) := mul_le_mul_of_nonneg_left hη2' hm1pos.le
      have h4 : (m1 : ℝ) * ((cn : ℝ) / cd) ≤ 1 - 1 / (N : ℝ) := by
        have e : (m1 : ℝ) * ((cn : ℝ) / cd) = ((m1 : ℝ) * cn) / cd := by ring
        have e3 : (1 : ℝ) - 1 / (N : ℝ) = ((N : ℝ) - 1) / N := by field_simp
        rw [e, e3, div_le_div_iff₀ hcdpos hNpos]
        linarith
      linarith

end Gap
end Sext6
end LRSpectrumFull
