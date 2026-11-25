import LRSpectrumFull.Sext6.Gap.Q81S1

/-!
# Q8.1, Theorem C for `N = 5..9`: the covering theorem  [2026-11-25]

Source: the accompanying notes on Zhang's Question 8.1 section 3, Lemma 4, made uniform in `(m1, m2)`.
Setting as in `Q81S1`.  `covP` is the union of four integer regimes (all decidable):
* `R1P`   : the counting regime (both multipliers large);
* `S2ok`  : class `r2`, the `A`-piece, `m2` small and `m1` large (two admissible upper ends `cn/cd`);
* `S1ok`  : class `r1`, the `A`-piece, `m1` small and `m2` large (three admissible upper ends);
* `explOK`: an explicit rational `η = p/q` from a finite list (certificate).

* `cov_sound` : `covP` gives `1/N ≤ ML V`.
* `cover_all` : `covP` holds for every `m1 ≥ r2`, `m2 ≥ r1`, given four finite checks (the corner, the two tails and the box).
No `sorry`, no `axiom`.

Convention: `N = k + 1` is the number of speeds of the vector `v : Fin (k+1) → ℤ`. Speeds are the moving runners; the runner at rest is not counted, so a vector of `N` speeds means `N + 1` runners and the Lonely Runner value is `1/(N+1)`.
Hypotheses: those of the individual statements (numerical bounds, structural conditions and, where named in the list above, window predicates such as `PrimeWin`, `CopWin`, `PrimeWindow7`, which later modules discharge for explicit ranges). The unproved predicates `DusartPi`, `LRCHyp`, `CopWinHyp` are not hypotheses of any statement in this module.
Axiom audit: covered by `Axioms22` (`#print axioms`; declarations not printed there are bricks of printed ones, so their axioms are bounded by the printed lines).
-/

namespace LRSpectrumFull
namespace Sext6
namespace Gap

def S2ok (N r1 r2 m1 m2 : ℕ) : Prop :=
  S2P N r1 r2 m1 m2 (N - 1) (N * m2) ∨ S2P N r1 r2 m1 m2 (2 * N - r2) (N * N)

def S1ok (N r1 r2 m1 m2 : ℕ) : Prop :=
  S1P N r1 r2 m1 m2 (N - 1) (N * m1) ∨ S1P N r1 r2 m1 m2 (2 * N - r1) (N * N) ∨
    S1P N r1 r2 m1 m2 (N - r1) (N * (r2 - r1))

def explOK (N r1 r2 m1 m2 : ℕ) (L : List (ℕ × ℕ × ℕ)) : Prop :=
  ∃ c ∈ L, (c.1 = 2 ∧ chk2P N r1 r2 m1 m2 c.2.1 c.2.2) ∨ (c.1 = 1 ∧ chk1P N r1 r2 m1 m2 c.2.1 c.2.2)

def covP (N r1 r2 : ℕ) (L : List (ℕ × ℕ × ℕ)) (m1 m2 : ℕ) : Prop :=
  R1P N r1 r2 m1 m2 ∨ S2ok N r1 r2 m1 m2 ∨ S1ok N r1 r2 m1 m2 ∨ explOK N r1 r2 m1 m2 L

instance (N r1 r2 m1 m2 : ℕ) : Decidable (S2ok N r1 r2 m1 m2) := by unfold S2ok; infer_instance
instance (N r1 r2 m1 m2 : ℕ) : Decidable (S1ok N r1 r2 m1 m2) := by unfold S1ok; infer_instance
instance (N r1 r2 m1 m2 : ℕ) (L : List (ℕ × ℕ × ℕ)) : Decidable (explOK N r1 r2 m1 m2 L) := by
  unfold explOK; infer_instance
instance (N r1 r2 : ℕ) (L : List (ℕ × ℕ × ℕ)) (m1 m2 : ℕ) : Decidable (covP N r1 r2 L m1 m2) := by
  unfold covP; infer_instance

theorem cov_sound {k N r1 r2 m1 m2 : ℕ} (L : List (ℕ × ℕ × ℕ)) (hk : k + 1 = N)
    (hr1 : N < 2 * r1) (h12 : r1 < r2) (h2N : r2 ≤ N) (hcop : Nat.Coprime r1 r2)
    (hm1 : 1 ≤ m1) (hm2 : 1 ≤ m2) (h : covP N r1 r2 L m1 m2) :
    1 / (N : ℝ) ≤ ML (v2Fam k r1 r2 m1 m2) := by
  rcases h with h | h | h | h
  · exact R1_sound hk hr1 h12 h2N hcop hm1 hm2 h
  · rcases h with h | h
    · exact S2_sound hk hr1 h12 h2N hcop hm1 hm2 h
    · exact S2_sound hk hr1 h12 h2N hcop hm1 hm2 h
  · rcases h with h | h | h
    · exact S1_sound hk hr1 h12 h2N hcop hm1 hm2 h
    · exact S1_sound hk hr1 h12 h2N hcop hm1 hm2 h
    · exact S1_sound hk hr1 h12 h2N hcop hm1 hm2 h
  · obtain ⟨c, _, h | h⟩ := h
    · exact chk2_sound hk hr1 h12 h2N hcop h.2
    · exact chk1_sound hk hr1 h12 h2N hcop h.2

theorem lin_mono {a b c x x' y : ℕ} (h : a * x + b * y < c * x * y) (hx : x ≤ x') :
    a * x' + b * y < c * x' * y := by
  have hx0 : 0 < x := by
    rcases Nat.eq_zero_or_pos x with h0 | h0
    · subst h0; simp at h
    · exact h0
  have hac : a < c * y := by
    have : a * x < (c * y) * x := by nlinarith [h, Nat.zero_le (b * y)]
    exact Nat.lt_of_mul_lt_mul_right this
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hx
  nlinarith [Nat.mul_le_mul_left d hac.le]

theorem R1P_mono_m1 {N r1 r2 m1 m1' m2 : ℕ} (h : R1P N r1 r2 m1 m2) (hm : m1 ≤ m1') :
    R1P N r1 r2 m1' m2 := by
  unfold R1P at *
  have := lin_mono (a := N * (N + 2) * r1) (b := N * (N + 2) * (2 * r2)) (c := (2 * N - r2) * (N - 4) * r1)
    (x := m1) (x' := m1') (y := m2) (by nlinarith [h]) hm
  nlinarith [this]

theorem R1P_mono_m2 {N r1 r2 m1 m2 m2' : ℕ} (h : R1P N r1 r2 m1 m2) (hm : m2 ≤ m2') :
    R1P N r1 r2 m1 m2' := by
  unfold R1P at *
  have := lin_mono (a := N * (N + 2) * (2 * r2)) (b := N * (N + 2) * r1) (c := (2 * N - r2) * (N - 4) * r1)
    (x := m2) (x' := m2') (y := m1) (by nlinarith [h]) hm
  nlinarith [this]

theorem S2P_mono {N r1 r2 m1 m1' m2 cn cd : ℕ} (h : S2P N r1 r2 m1 m2 cn cd) (hm : m1 ≤ m1') :
    S2P N r1 r2 m1' m2 cn cd := by
  obtain ⟨a, b, c, d, e⟩ := h
  refine ⟨a, b, c, d, lt_of_lt_of_le e ?_⟩
  exact Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ hm))

theorem S1P_mono {N r1 r2 m1 m2 m2' cn cd : ℕ} (h : S1P N r1 r2 m1 m2 cn cd) (hm : m2 ≤ m2') :
    S1P N r1 r2 m1 m2' cn cd := by
  obtain ⟨a, b, c, d, e, f⟩ := h
  refine ⟨a, b, c, d, e, lt_of_lt_of_le f ?_⟩
  exact Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ hm))

theorem S2ok_mono {N r1 r2 m1 m1' m2 : ℕ} (h : S2ok N r1 r2 m1 m2) (hm : m1 ≤ m1') :
    S2ok N r1 r2 m1' m2 := by
  rcases h with h | h
  · exact Or.inl (S2P_mono h hm)
  · exact Or.inr (S2P_mono h hm)

theorem S1ok_mono {N r1 r2 m1 m2 m2' : ℕ} (h : S1ok N r1 r2 m1 m2) (hm : m2 ≤ m2') :
    S1ok N r1 r2 m1 m2' := by
  rcases h with h | h | h
  · exact Or.inl (S1P_mono h hm)
  · exact Or.inr (Or.inl (S1P_mono h hm))
  · exact Or.inr (Or.inr (S1P_mono h hm))

/-- Coverage for all multipliers from four finite checks. -/
theorem cover_all {N r1 r2 P Q : ℕ} (L : List (ℕ × ℕ × ℕ))
    (hT1 : R1P N r1 r2 P Q)
    (hT2 : ∀ m2, m2 < Q → r1 ≤ m2 → R1P N r1 r2 P m2 ∨ S2ok N r1 r2 P m2)
    (hT3 : ∀ m1, m1 < P → r2 ≤ m1 → R1P N r1 r2 m1 Q ∨ S1ok N r1 r2 m1 Q)
    (hbox : ∀ m1, m1 < P → r2 ≤ m1 → ∀ m2, m2 < Q → r1 ≤ m2 → covP N r1 r2 L m1 m2) :
    ∀ m1 m2, r2 ≤ m1 → r1 ≤ m2 → covP N r1 r2 L m1 m2 := by
  intro m1 m2 hm1 hm2
  by_cases h1 : m1 < P
  · by_cases h2 : m2 < Q
    · exact hbox m1 h1 hm1 m2 h2 hm2
    · have hQ : Q ≤ m2 := by omega
      rcases hT3 m1 h1 hm1 with h | h
      · exact Or.inl (R1P_mono_m2 h hQ)
      · exact Or.inr (Or.inr (Or.inl (S1ok_mono h hQ)))
  · have hP : P ≤ m1 := by omega
    by_cases h2 : m2 < Q
    · rcases hT2 m2 h2 hm2 with h | h
      · exact Or.inl (R1P_mono_m1 h hP)
      · exact Or.inr (Or.inl (S2ok_mono h hP))
    · have hQ : Q ≤ m2 := by omega
      exact Or.inl (R1P_mono_m2 (R1P_mono_m1 hT1 hP) hQ)

end Gap
end Sext6
end LRSpectrumFull
