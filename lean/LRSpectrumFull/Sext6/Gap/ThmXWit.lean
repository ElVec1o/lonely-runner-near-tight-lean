import LRSpectrumFull.Sext6.Gap.ThmXRun
import LRSpectrumFull.Sext6.Gap.MultiBridge
import LRSpectrumFull.Sext6.Gap.LowerA

/-!
# Theorem X, part 3: the speed set `([N] \ {r}) ∪ W`, the witness times, the converse  [2026-11-25]

Source: the accompanying notes on Theorem X, Section 1 Lemma 3, Section 3 (converse, minimality).

* `XMem N r x`   : `x` is an admissible speed: `x ∈ [1,N] \ {r}`, or `x ∈ [N+r+1, N+2r]` coprime to `r`.
* `IsV N r v`    : the entry set of `v` is exactly `([1,N] \ {r}) ∪ W`, `W = {D ∈ [N+r+1,N+2r] : gcd(D,r)=1}`
  (repetitions and any order allowed; `ML_congr_range` shows `ML` only sees the set).
* `wit_far`      : integer form of Lemma 3: at `t = (2 N c + 1)/(2 N r)` with `r ∣ c D' + 1`, every
  admissible speed `x` (and `x = D'` only if `D' + 2 r ≤ 2 N`) has `2 r ≤ |(2Nc+1) x - n (2Nr)|` for all `n`,
  i.e. `‖x t‖ ≥ 1/N`.
* `ML_ge_of_witness`, `ML_ge_of_le` : `D0 ≤ 2N - 2r` implies `1/N ≤ ML v` (converse of Theorem X).
* `ML_ge_of_drop` : minimality: dropping any one `D' ∈ W` gives `1/N ≤ ML`, with no hypothesis on `D0`.
No `sorry`, no `axiom`.

Convention: `N` is the size of the ambient interval `[N]`; `k` is not linked to `N` (repetitions allowed).
Hypotheses: `2 ≤ r`, `2 r ≤ N` (the theorem's hypotheses), plus the window conditions of each statement.
Axiom audit: covered by `Axioms24`.
-/

namespace LRSpectrumFull
namespace Sext6
namespace Gap

/-- Admissible speeds of the family `([1,N] \ {r}) ∪ W`. -/
def XMem (N r : ℕ) (x : ℤ) : Prop :=
  (1 ≤ x ∧ x ≤ (N : ℤ) ∧ x ≠ (r : ℤ)) ∨
    ∃ w : ℕ, x = (w : ℤ) ∧ N + r + 1 ≤ w ∧ w ≤ N + 2 * r ∧ Nat.Coprime w r

/-- The entry set of `v` is exactly `([1,N] \ {r}) ∪ W`. -/
structure IsV (N r : ℕ) {k : ℕ} (v : Fin (k + 1) → ℤ) : Prop where
  sub : ∀ i, XMem N r (v i)
  cov : ∀ x : ℕ, ((1 ≤ x ∧ x ≤ N ∧ x ≠ r) ∨
      (N + r + 1 ≤ x ∧ x ≤ N + 2 * r ∧ Nat.Coprime x r)) → ∃ i, v i = (x : ℤ)

theorem XMem.pos_le {N r : ℕ} {x : ℤ} (h : XMem N r x) : 1 ≤ x ∧ x ≤ (N : ℤ) + 2 * r := by
  rcases h with ⟨a, b, _⟩ | ⟨w, hw, h1, h2, _⟩
  · exact ⟨a, by omega⟩
  · subst hw
    have h1' : ((N + r + 1 : ℕ) : ℤ) ≤ (w : ℤ) := by exact_mod_cast h1
    have h2' : (w : ℤ) ≤ ((N + 2 * r : ℕ) : ℤ) := by exact_mod_cast h2
    push_cast at h1' h2'
    constructor <;> omega

/-- **Lemma 3, integer form.**  `r ∣ c D' + 1` (so `c` is the unit with `u(c) ≡ D'`). -/
theorem wit_far {N r D' : ℕ} (hr2 : 2 ≤ r) (hN : 2 * r ≤ N) (hD1 : N + r + 1 ≤ D')
    (hD2 : D' ≤ N + 2 * r) (c : ℤ) (hc : (r : ℤ) ∣ c * (D' : ℤ) + 1) (x : ℤ)
    (hx : XMem N r x) (hxD : x = (D' : ℤ) → D' + 2 * r ≤ 2 * N) (n : ℤ) :
    ((2 * r : ℕ) : ℤ) ≤ |(2 * (N : ℤ) * c + 1) * x - n * ((2 * N * r : ℕ) : ℤ)| := by
  obtain ⟨m, hm⟩ := hc
  have hNz : (2 : ℤ) * r ≤ N := by exact_mod_cast hN
  have hr2z : (2 : ℤ) ≤ r := by exact_mod_cast hr2
  have hD1z : (N : ℤ) + r + 1 ≤ D' := by exact_mod_cast hD1
  have hD2z : (D' : ℤ) ≤ N + 2 * r := by exact_mod_cast hD2
  obtain ⟨hx1, hx2⟩ := hx.pos_le
  obtain ⟨j, hj⟩ : ∃ j : ℤ, j = c * x - r * n := ⟨_, rfl⟩
  have e : (2 * (N : ℤ) * c + 1) * x - n * ((2 * N * r : ℕ) : ℤ) = 2 * N * j + x := by
    rw [hj]; push_cast; ring
  rw [e]
  push_cast
  have hNnn : (0 : ℤ) ≤ N := by omega
  by_cases hj1 : 1 ≤ j
  · have h0 : (N : ℤ) * 1 ≤ N * j := mul_le_mul_of_nonneg_left hj1 hNnn
    exact le_trans (by nlinarith) (le_abs_self _)
  by_cases hj2 : j ≤ -2
  · have h0 : (N : ℤ) * j ≤ N * (-2) := mul_le_mul_of_nonneg_left hj2 hNnn
    exact le_trans (by nlinarith) (neg_le_abs _)
  have hj01 : j = 0 ∨ j = -1 := by omega
  rcases hj01 with h0 | h1
  · -- j = 0 : r ∣ x, so x ≥ 2 r
    have hj0 : c * x - r * n = 0 := by rw [← hj, h0]
    have hxr : x = r * (x * m - n * D') := by linear_combination x * hm - (D' : ℤ) * hj0
    have hx2r : 2 * (r : ℤ) ≤ x := by
      rcases hx with ⟨a, b, hne⟩ | ⟨w, hw, h1, h2, _⟩
      · have hu1 : 1 ≤ x * m - n * D' := by
          by_contra hcon
          push Not at hcon
          nlinarith
        have hu2 : x * m - n * D' ≠ 1 := fun h => hne (by rw [hxr, h]; ring)
        have hu3 : 2 ≤ x * m - n * D' := by omega
        nlinarith
      · have h1' : ((N + r + 1 : ℕ) : ℤ) ≤ (w : ℤ) := by exact_mod_cast h1
        push_cast at h1'
        rw [hw]; omega
    rw [h0]
    exact le_trans (by nlinarith) (le_abs_self _)
  · -- j = -1 : r ∣ x - D'
    have hj1' : -1 = c * x - r * n := by rw [← hj, h1]
    have hdiv : x - D' = r * ((x - D') * m - D' * (n - m)) := by
      linear_combination x * hm + (D' : ℤ) * hj1'
    rw [h1]
    rcases hx with ⟨a, b, hne⟩ | ⟨w, hw, hw1, hw2, _⟩
    · exact le_trans (by nlinarith) (neg_le_abs _)
    · have hw1' : ((N + r + 1 : ℕ) : ℤ) ≤ (w : ℤ) := by exact_mod_cast hw1
      have hw2' : (w : ℤ) ≤ ((N + 2 * r : ℕ) : ℤ) := by exact_mod_cast hw2
      push_cast at hw1' hw2'
      have habs : |x - (D' : ℤ)| < r := by
        rw [abs_lt]; constructor <;> omega
      have hz := Int.eq_zero_of_abs_lt_dvd ⟨_, hdiv⟩ habs
      have hxe : x = (D' : ℤ) := by omega
      have hle := hxD hxe
      have hlez : (D' : ℤ) + 2 * r ≤ 2 * N := by exact_mod_cast hle
      exact le_trans (by nlinarith) (neg_le_abs _)

/-- **Converse witness.**  If `v` has only admissible entries, `D'` is a window element coprime to `r`,
and the entry `D'` (if present) satisfies `D' + 2 r ≤ 2 N`, then `1/N ≤ ML v`. -/
theorem ML_ge_of_witness {k N r D' : ℕ} (hr2 : 2 ≤ r) (hN : 2 * r ≤ N) (hD1 : N + r + 1 ≤ D')
    (hD2 : D' ≤ N + 2 * r) (hcop : Nat.Coprime D' r) (v : Fin (k + 1) → ℤ)
    (hv : ∀ i, XMem N r (v i)) (hxD : ∀ i, v i = (D' : ℤ) → D' + 2 * r ≤ 2 * N) :
    1 / (N : ℝ) ≤ ML v := by
  have hc : IsCoprime (D' : ℤ) (r : ℤ) := Nat.isCoprime_iff_coprime.mpr hcop
  obtain ⟨a, b, hab⟩ := hc
  have hdiv : (r : ℤ) ∣ (-a) * (D' : ℤ) + 1 := ⟨b, by linarith⟩
  have hNpos : 0 < N := by omega
  have hrpos : 0 < r := by omega
  have hQ : 0 < 2 * N * r := by positivity
  have hNR : (N : ℝ) ≠ 0 := by exact_mod_cast hNpos.ne'
  have hrR : (r : ℝ) ≠ 0 := by exact_mod_cast hrpos.ne'
  refine ML_ge_of_far v (1 / (N : ℝ))
    (((2 * (N : ℤ) * (-a) + 1 : ℤ) : ℝ) / ((2 * N * r : ℕ) : ℝ)) ?_
  intro i
  have e : ((v i : ℤ) : ℝ) * (((2 * (N : ℤ) * (-a) + 1 : ℤ) : ℝ) / ((2 * N * r : ℕ) : ℝ))
      = ((((2 * (N : ℤ) * (-a) + 1) * v i : ℤ)) : ℝ) / ((2 * N * r : ℕ) : ℝ) := by
    push_cast; ring
  rw [e]
  have key := nid_div_ge hQ ((2 * (N : ℤ) * (-a) + 1) * v i) (2 * r)
    (fun n => wit_far hr2 hN hD1 hD2 (-a) hdiv (v i) (hv i) (hxD i) n)
  have e2 : ((2 * r : ℕ) : ℝ) / ((2 * N * r : ℕ) : ℝ) = 1 / (N : ℝ) := by
    push_cast; field_simp
  rw [e2] at key
  exact key

/-- **Converse of Theorem X** (`D0 ≤ 2N - 2r` implies `1/N ≤ ML`). -/
theorem ML_ge_of_le {k N r D : ℕ} (hS : DSpec N r D) (hr2 : 2 ≤ r) (hle : D + 2 * r ≤ 2 * N)
    (v : Fin (k + 1) → ℤ) (hV : IsV N r v) : 1 / (N : ℝ) ≤ ML v :=
  ML_ge_of_witness hr2 hS.hN (by have := hS.hD1; omega) hS.le_window hS.hcop v hV.sub
    (fun _ _ => hle)

/-- **Minimality (v).**  Dropping any one element `D'` of `W` gives `1/N ≤ ML`, with no hypothesis on `D0`. -/
theorem ML_ge_of_drop {k N r D' : ℕ} (hr2 : 2 ≤ r) (hN : 2 * r ≤ N) (hD1 : N + r + 1 ≤ D')
    (hD2 : D' ≤ N + 2 * r) (hcop : Nat.Coprime D' r) (v : Fin (k + 1) → ℤ)
    (hv : ∀ i, XMem N r (v i)) (hne : ∀ i, v i ≠ (D' : ℤ)) : 1 / (N : ℝ) ≤ ML v :=
  ML_ge_of_witness hr2 hN hD1 hD2 hcop v hv (fun i h => absurd h (hne i))

end Gap
end Sext6
end LRSpectrumFull
