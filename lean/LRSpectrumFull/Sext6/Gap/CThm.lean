import LRSpectrumFull.Sext6.Gap.Cor
import Mathlib.NumberTheory.Primorial
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Order.Filter.AtTopBot.Basic

/-!
# Theorem C (primorial liminf)  [2026-11-24]

Source: the accompanying notes on Theorem V section 8 (ii).

For a prime `p`, `q` the next prime, `r = p#` (primorial), `N = r + 1` speeds, `m = (q+1)/2`:
`β = q`, the family set `[N]_{r → m r}` is non-tight with `ML = m/(m r + q)`, the excess over `1/(N+1)` is
exactly `1/((m r + q)(N+1))`, and `N² · excess < (1 + 1/(r(r+2)))/m`.

Consequences (only the infinitude of primes is used, no PNT):
* `liminf N² (g(N) - 1/(N+1)) = 0` in the form: for every `ε > 0` and every `M₀` there is `k ≥ M₀`
  with `0 ≤ N²(g(N) - 1/(N+1)) < ε`  (`N = k+1`), also as `∃ᶠ k in atTop`.
* there is no `c > 0` with `g(N) ≥ 1/(N+1) + c/N²` for all `N`.
* the instance `N = 31`: `g(31) ≤ 4/127 < 1/32 + 1/(4·31²)` (Stab with `c = 1/4` fails).

`g(N) = G(N)` is NOT claimed.   No `sorry`, no `axiom`.

Convention: `N = k + 1` is the number of speeds of the vector `v : Fin (k+1) → ℤ`. Speeds are the moving runners; the runner at rest is not counted, so a vector of `N` speeds means `N + 1` runners and the Lonely Runner value is `1/(N+1)`.
Hypotheses: those of the individual statements (numerical bounds, structural conditions and, where named in the list above, window predicates such as `PrimeWin`, `CopWin`, `PrimeWindow7`, which later modules discharge for explicit ranges). The unproved predicates `DusartPi`, `LRCHyp`, `CopWinHyp` are not hypotheses of any statement in this module.
Axiom audit: covered by `Axioms2` (`#print axioms`; declarations not printed there are bricks of printed ones, so their axioms are bounded by the printed lines).
-/

namespace LRSpectrumFull
namespace Sext6
namespace Gap

/-- `g(N) ≥ 1/(N+1)` for `N = k + 1 ≥ 2` (every non-tight value exceeds `1/(N+1)`; the set is nonempty). -/
theorem gNT_ge {k : ℕ} (hk : 1 ≤ k) : 1 / (((k + 1 : ℕ) : ℝ) + 1) ≤ gNT k := by
  have hN : 2 ≤ k + 1 := by omega
  obtain ⟨hv, hlt, _⟩ := corA_b (k := k) (N := k + 1) rfl hN
  apply le_csInf
  · refine ⟨ML (vFam k (k + 1) 2), vFam k (k + 1) 2, ?_, ?_, rfl, ?_⟩
    · exact vFam_injective rfl (by omega) le_rfl le_rfl
    · intro i
      exact vFam_pos (by omega) (by omega) i
    · rw [hv]; exact hlt
  · rintro x ⟨v, _, _, rfl, hx⟩
    exact hx.le

/-- Data for Theorem C: `r ≥ 2`, `q` prime, `q + 1 = 2 m`, every `b ∈ [2, q-1]` shares a factor with `r`,
and `q` is coprime to `r`. -/
structure CSpec (r q m : ℕ) : Prop where
  hr : 2 ≤ r
  hq : q.Prime
  hm : q + 1 = 2 * m
  hcov : ∀ b : ℕ, 2 ≤ b → b < q → ¬ Nat.Coprime b r
  hqr : Nat.Coprime q r

theorem CSpec.q_ge {r q m : ℕ} (h : CSpec r q m) : 3 ≤ q := by
  have h1 := h.hq.two_le
  have h2 := h.hm
  omega

theorem CSpec.m_ge {r q m : ℕ} (h : CSpec r q m) : 2 ≤ m := by
  have h1 := h.q_ge
  have h2 := h.hm
  omega

/-- Under `CSpec`, `β(r+1, r) = q`: the specification of Theorem V holds with `N = r + 1`, `β = q`. -/
theorem CSpec.spec {r q m : ℕ} (h : CSpec r q m) : Spec (r + 1) r m q := by
  have h3 := h.q_ge
  have hm := h.m_ge
  have hr := h.hr
  refine ⟨by omega, by omega, by omega, hm, by omega, h.hqr, ?_⟩
  intro b hb hcop
  by_contra hlt
  exact h.hcov b (by omega) (by omega) hcop

/-- Exact value and exact excess along the Theorem C family. -/
theorem C_value {r q m : ℕ} (h : CSpec r q m) :
    ML (vFam r r m) = (m : ℝ) / ((m * r + q : ℕ) : ℝ) ∧
    ML (vFam r r m) - 1 / (((r + 1 : ℕ) : ℝ) + 1) = 1 / (((m * r + q : ℕ) : ℝ) * ((r : ℝ) + 2)) := by
  have hS := h.spec
  have hV := value_formula_spec (k := r) (N := r + 1) rfl hS
  have hm' : ((q : ℝ) + 1) = 2 * (m : ℝ) := by exact_mod_cast h.hm
  have hD : ((m * r + q : ℕ) : ℝ) = (m : ℝ) * r + q := by push_cast; ring
  have hE : (((r + 1 : ℕ) : ℝ) + 1) = (r : ℝ) + 2 := by push_cast; ring
  have hMpos : (0 : ℝ) < m := by
    have := h.m_ge
    exact_mod_cast (by omega : 0 < m)
  have hDpos' : 0 < m * r + q := by
    have := h.q_ge
    omega
  have hDpos : (0 : ℝ) < ((m * r + q : ℕ) : ℝ) := by exact_mod_cast hDpos'
  have hEpos : (0 : ℝ) < (r : ℝ) + 2 := by positivity
  have hDpos2 : (0 : ℝ) < (m : ℝ) * r + q := by rw [← hD]; exact hDpos
  have hlt : 1 / (((r + 1 : ℕ) : ℝ) + 1) < (m : ℝ) / ((m * r + q : ℕ) : ℝ) := by
    rw [hE, hD, div_lt_div_iff₀ hEpos hDpos2]
    nlinarith [hm']
  have hv : ML (vFam r r m) = (m : ℝ) / ((m * r + q : ℕ) : ℝ) := by
    rw [hV]
    exact max_eq_right hlt.le
  refine ⟨hv, ?_⟩
  rw [hv, hE, hD, div_sub_div _ _ hDpos2.ne' hEpos.ne']
  have key : (m : ℝ) * ((r : ℝ) + 2) - ((m : ℝ) * r + q) * 1 = 1 := by
    linear_combination -hm'
  rw [key]

/-- Theorem C, quantitative core: `0 ≤ N² (g(N) - 1/(N+1)) < (1 + 1/(r(r+2)))/m`, `N = r + 1`. -/
theorem C_scaled {r q m : ℕ} (h : CSpec r q m) :
    0 ≤ ((r + 1 : ℕ) : ℝ) ^ 2 * (gNT r - 1 / (((r + 1 : ℕ) : ℝ) + 1)) ∧
    ((r + 1 : ℕ) : ℝ) ^ 2 * (gNT r - 1 / (((r + 1 : ℕ) : ℝ) + 1)) <
      (1 + 1 / ((r : ℝ) * ((r : ℝ) + 2))) / (m : ℝ) := by
  obtain ⟨hv, hex⟩ := C_value h
  have hm' : ((q : ℝ) + 1) = 2 * (m : ℝ) := by exact_mod_cast h.hm
  have hr2 : (2 : ℝ) ≤ r := by exact_mod_cast h.hr
  have hD : ((m * r + q : ℕ) : ℝ) = (m : ℝ) * r + q := by push_cast; ring
  have hMpos : (0 : ℝ) < m := by
    have := h.m_ge
    exact_mod_cast (by omega : 0 < m)
  have hRpos : (0 : ℝ) < r := by linarith
  have hQpos : (0 : ℝ) < q := by
    have := h.q_ge
    exact_mod_cast (by omega : 0 < q)
  have hEpos : (0 : ℝ) < (r : ℝ) + 2 := by positivity
  have hDpos2 : (0 : ℝ) < (m : ℝ) * r + q := add_pos_of_nonneg_of_pos (by positivity) hQpos
  have hg1 : 1 / (((r + 1 : ℕ) : ℝ) + 1) ≤ gNT r := gNT_ge (by have := h.hr; omega)
  have hpos : 0 < 1 / (((m * r + q : ℕ) : ℝ) * ((r : ℝ) + 2)) := by
    exact one_div_pos.2 (mul_pos (by rw [hD]; exact hDpos2) hEpos)
  have hlt : 1 / (((r + 1 : ℕ) : ℝ) + 1) < ML (vFam r r m) := by linarith
  have hg2 : gNT r ≤ ML (vFam r r m) := gNT_le (k := r) (N := r + 1) rfl h.spec hlt
  have hsq : ((r + 1 : ℕ) : ℝ) ^ 2 = ((r : ℝ) + 1) ^ 2 := by push_cast; ring
  rw [hsq]
  have hsqpos : (0 : ℝ) < ((r : ℝ) + 1) ^ 2 := by positivity
  refine ⟨mul_nonneg hsqpos.le (by linarith), ?_⟩
  calc ((r : ℝ) + 1) ^ 2 * (gNT r - 1 / (((r + 1 : ℕ) : ℝ) + 1))
      ≤ ((r : ℝ) + 1) ^ 2 * (ML (vFam r r m) - 1 / (((r + 1 : ℕ) : ℝ) + 1)) :=
        mul_le_mul_of_nonneg_left (by linarith) hsqpos.le
    _ = ((r : ℝ) + 1) ^ 2 * (1 / (((m : ℝ) * r + q) * ((r : ℝ) + 2))) := by
        rw [hex, hD]
    _ < ((r : ℝ) + 1) ^ 2 / ((m : ℝ) * r * ((r : ℝ) + 2)) := by
        rw [mul_one_div, div_lt_div_iff₀ (mul_pos hDpos2 hEpos)
          (mul_pos (mul_pos hMpos hRpos) hEpos)]
        have h1 : (m : ℝ) * r * ((r : ℝ) + 2) < ((m : ℝ) * r + q) * ((r : ℝ) + 2) :=
          mul_lt_mul_of_pos_right (by linarith) hEpos
        exact mul_lt_mul_of_pos_left h1 hsqpos
    _ = (1 + 1 / ((r : ℝ) * ((r : ℝ) + 2))) / (m : ℝ) := by
        have hR0 : (r : ℝ) ≠ 0 := hRpos.ne'
        have hR2 : (r : ℝ) + 2 ≠ 0 := hEpos.ne'
        have hM0 : (m : ℝ) ≠ 0 := hMpos.ne'
        field_simp
        ring

/-! ### Primorials and the next prime -/

theorem exists_next_prime (p : ℕ) :
    ∃ q, q.Prime ∧ p < q ∧ ∀ x, p < x → x.Prime → q ≤ x := by
  classical
  have hex : ∃ x, p < x ∧ x.Prime := by
    obtain ⟨x, hx1, hx2⟩ := Nat.exists_infinite_primes (p + 1)
    exact ⟨x, by omega, hx2⟩
  refine ⟨Nat.find hex, (Nat.find_spec hex).2, (Nat.find_spec hex).1, ?_⟩
  intro x hx1 hx2
  exact Nat.find_min' hex ⟨hx1, hx2⟩

theorem dvd_primorial' {a p : ℕ} (ha : a.Prime) (hle : a ≤ p) : a ∣ primorial p := by
  unfold primorial
  exact Finset.dvd_prod_of_mem (fun x : ℕ => x)
    (Finset.mem_filter.2 ⟨Finset.mem_range.2 (by omega), ha⟩)

theorem prime_dvd_primorial {q p : ℕ} (hq : q.Prime) (h : q ∣ primorial p) : q ≤ p := by
  unfold primorial at h
  obtain ⟨a, ha, hqa⟩ := (Prime.dvd_finsetProd_iff hq.prime (fun x : ℕ => x)).1 h
  rw [Finset.mem_filter, Finset.mem_range] at ha
  have := (Nat.prime_dvd_prime_iff_eq hq ha.2).1 hqa
  omega

/-- The primorial `p#` with next prime `q` satisfies the data of Theorem C. -/
theorem cspec_primorial {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p < q)
    (hmin : ∀ x, p < x → x.Prime → q ≤ x) : CSpec (primorial p) q ((q + 1) / 2) := by
  have hp2 := hp.two_le
  have hdvd : p ∣ primorial p := dvd_primorial' hp le_rfl
  have hpos := primorial_pos p
  have hrp : p ≤ primorial p := Nat.le_of_dvd hpos hdvd
  refine ⟨by omega, hq, ?_, ?_, ?_⟩
  · rcases hq.eq_two_or_odd' with h2 | ⟨t, ht⟩
    · omega
    · omega
  · intro b hb2 hbq hcop
    have hb1 : b ≠ 1 := by omega
    have hmf := Nat.minFac_prime hb1
    have hle : Nat.minFac b ≤ b := Nat.minFac_le (by omega)
    have hlep : Nat.minFac b ≤ p := by
      by_contra hgt
      have := hmin _ (by omega) hmf
      omega
    have hd : Nat.minFac b ∣ primorial p := dvd_primorial' hmf hlep
    have hc : Nat.Coprime (Nat.minFac b) (primorial p) :=
      Nat.Coprime.coprime_dvd_left (Nat.minFac_dvd b) hcop
    have h1 := Nat.Coprime.eq_one_of_dvd hc hd
    have h2 := hmf.one_lt
    omega
  · rw [Nat.Prime.coprime_iff_not_dvd hq]
    intro h
    have := prime_dvd_primorial hq h
    omega

/-! ### Scaled gap and the liminf statement -/

/-- `N² (g(N) - 1/(N+1))` with `N = k + 1`. -/
noncomputable def gapScaled (k : ℕ) : ℝ :=
  ((k + 1 : ℕ) : ℝ) ^ 2 * (gNT k - 1 / (((k + 1 : ℕ) : ℝ) + 1))

/-- **Theorem C** (liminf form, only infinitude of primes): for every `ε > 0` and `M₀` there is
`k ≥ M₀` (`N = k+1` speeds) with `0 ≤ N² (g(N) - 1/(N+1)) < ε`. -/
theorem liminf_gap_zero (ε : ℝ) (hε : 0 < ε) (M₀ : ℕ) :
    ∃ k : ℕ, M₀ ≤ k ∧ 0 ≤ gapScaled k ∧ gapScaled k < ε := by
  obtain ⟨p, hp0, hp⟩ := Nat.exists_infinite_primes (M₀ + ⌈4 / ε⌉₊ + 1)
  obtain ⟨q, hq, hpq, hmin⟩ := exists_next_prime p
  have hC := cspec_primorial hp hq hpq hmin
  generalize hmdef : (q + 1) / 2 = m at hC
  obtain ⟨h0, h1⟩ := C_scaled hC
  have hp2 := hp.two_le
  have hdvd : p ∣ primorial p := dvd_primorial' hp le_rfl
  have hrp : p ≤ primorial p := Nat.le_of_dvd (primorial_pos p) hdvd
  refine ⟨primorial p, by omega, h0, ?_⟩
  unfold gapScaled
  refine lt_of_lt_of_le h1 ?_
  have hm' : ((q : ℝ) + 1) = 2 * (m : ℝ) := by exact_mod_cast hC.hm
  have hMpos : (0 : ℝ) < (m : ℝ) := by
    have := hC.m_ge
    exact_mod_cast (by omega : 0 < m)
  have hr2 : (2 : ℝ) ≤ (primorial p : ℝ) := by exact_mod_cast hC.hr
  have hceil : 4 / ε ≤ (p : ℝ) := by
    have h1' : 4 / ε ≤ (⌈4 / ε⌉₊ : ℝ) := Nat.le_ceil _
    have h2' : (⌈4 / ε⌉₊ : ℝ) ≤ (p : ℝ) := by exact_mod_cast (by omega : ⌈4 / ε⌉₊ ≤ p)
    linarith
  have h4 : 4 ≤ (p : ℝ) * ε := (div_le_iff₀ hε).1 hceil
  have hpq' : (p : ℝ) + 1 ≤ (q : ℝ) := by exact_mod_cast hpq
  have hεM : 2 < ε * (m : ℝ) := by
    have h5 : ε * ((p : ℝ) + 1) ≤ ε * q := mul_le_mul_of_nonneg_left hpq' hε.le
    have h6 : ε * ((q : ℝ) + 1) = ε * (2 * (m : ℝ)) := by rw [hm']
    nlinarith [h5, h6, h4, hε]
  have hRpos : (0 : ℝ) < (primorial p : ℝ) * ((primorial p : ℝ) + 2) :=
    mul_pos (by linarith) (by linarith)
  have hle1 : 1 / ((primorial p : ℝ) * ((primorial p : ℝ) + 2)) ≤ 1 := by
    rw [div_le_one hRpos]
    nlinarith
  have hle2 : (1 + 1 / ((primorial p : ℝ) * ((primorial p : ℝ) + 2))) / (m : ℝ)
      ≤ 2 / (m : ℝ) :=
    div_le_div_of_nonneg_right (by linarith) hMpos.le
  have hlt3 : 2 / (m : ℝ) < ε := by
    rw [div_lt_iff₀ hMpos]
    linarith
  exact (hle2.trans hlt3.le)

/-- Frequently form: `liminf_{k → ∞} N² (g(N) - 1/(N+1)) = 0`, i.e. nonnegative and below every `ε`
infinitely often. -/
theorem liminf_gap_zero_frequently (ε : ℝ) (hε : 0 < ε) :
    ∃ᶠ k in Filter.atTop, gapScaled k < ε := by
  rw [Filter.frequently_atTop]
  intro M₀
  obtain ⟨k, hk, _, h⟩ := liminf_gap_zero ε hε M₀
  exact ⟨k, hk, h⟩

theorem gapScaled_nonneg {k : ℕ} (hk : 1 ≤ k) : 0 ≤ gapScaled k := by
  unfold gapScaled
  have := gNT_ge hk
  have h : 0 ≤ gNT k - 1 / (((k + 1 : ℕ) : ℝ) + 1) := by linarith
  positivity

/-- No lower bound `g(N) ≥ 1/(N+1) + c/N²` with `c > 0` holds for all `N`. -/
theorem no_inv_sq_lower_bound (c : ℝ) (hc : 0 < c) :
    ∃ k : ℕ, 1 ≤ k ∧ gNT k < 1 / (((k + 1 : ℕ) : ℝ) + 1) + c / ((k + 1 : ℕ) : ℝ) ^ 2 := by
  obtain ⟨k, hk, _, h⟩ := liminf_gap_zero c hc 1
  refine ⟨k, hk, ?_⟩
  unfold gapScaled at h
  have hN2 : (0 : ℝ) < ((k + 1 : ℕ) : ℝ) ^ 2 := by positivity
  have h' : gNT k - 1 / (((k + 1 : ℕ) : ℝ) + 1) < c / ((k + 1 : ℕ) : ℝ) ^ 2 := by
    rw [lt_div_iff₀ hN2]
    linarith
  linarith

/-- The explicit instance: `N = 31`, `g(31) ≤ 4/127 < 1/32 + 1/(4·31²)`; Stab with `c = 1/4` fails. -/
theorem stab_fails_31 :
    gNT 30 < 1 / (((30 + 1 : ℕ) : ℝ) + 1) + 1 / (4 * ((30 + 1 : ℕ) : ℝ) ^ 2) := by
  calc gNT 30 ≤ 4 / 127 := inst_31_30_4.2
    _ < _ := by norm_num

end Gap
end Sext6
end LRSpectrumFull
