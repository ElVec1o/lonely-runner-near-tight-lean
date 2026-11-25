import LRSpectrumFull.Sext6.Gap.OELow

/-!
# Theorem OE-low, finite range `14 ≤ N ≤ 78`: the certificate checker  [2026-11-24]

For each `N` a table (one entry per `r ≤ N/2`) lists

* `Ds`  : at most three moduli `D ∈ [N+1+r, 2N]`, `gcd(D, r) = 1` (Lemma-W witnesses),
* `exc` : the `w` that no listed modulus settles (empty except `(N, r) = (14, 6)`),
* `D0`, `Wb` : a Lemma-L modulus `D0 ≤ 2N - 1` with `D0 N² ≤ 2 (2N - D0) Wb`, so every `w ≥ Wb` is settled.

`tabOK N tab = true` (a closed Boolean, checked by `decide +kernel`) says that the table is complete
(`r = 1, ..., N/2`), that every entry is well formed, and that every `w ∈ (N, Wb)` is settled by some listed
modulus or listed in `exc`.

* `okW`, `wOK`, `allW`, `dOK`, `entOK`, `tabOK` : the Boolean checker.
* `okW_sound`, `allW_sound`, `entOK_sound`, `tabOK_sound` : soundness, in terms of `WitnessCover`.
No `sorry`, no `axiom`.

Convention: `N = k + 1` is the number of entries (speeds) of the one-entry vector `wFam k r w = ([1,N] \ {r}) ∪ {w}`. Speeds are the moving runners; the runner at rest is not counted, so a vector of `N` speeds means `N + 1` runners and the Lonely Runner value is `1/(N+1)`.
Hypotheses: those of the individual statements (numerical bounds, structural conditions and, where named in the list above, window predicates such as `PrimeWin`, `CopWin`, `PrimeWindow7`, which later modules discharge for explicit ranges). The unproved predicates `DusartPi`, `LRCHyp`, `CopWinHyp` are not hypotheses of any statement in this module.
Axiom audit: covered by `Axioms6` (first); every later audit module imports this module (`#print axioms`; declarations not printed there are bricks of printed ones, so their axioms are bounded by the printed lines).
-/

namespace LRSpectrumFull
namespace Sext6
namespace Gap

/-- One row of a certificate table. -/
structure Ent where
  r : Nat
  Ds : List Nat
  exc : List Nat
  D0 : Nat
  Wb : Nat

/-- `w ≢ 0, r, -r (mod D)` as a Boolean. -/
def okW (r w D : Nat) : Bool :=
  decide (w % D ≠ 0) && decide (w % D ≠ r % D) && decide ((w + r) % D ≠ 0)

def wOK (r : Nat) (Ds exc : List Nat) (w : Nat) : Bool :=
  exc.contains w || Ds.any (fun D => okW r w D)

/-- Candidate check: `w` outside `(N, Wb)` is vacuous, otherwise some listed modulus settles it. -/
def vOK (N Wb r : Nat) (Ds exc : List Nat) (w : Nat) : Bool :=
  decide (w ≤ N) || decide (Wb ≤ w) || wOK r Ds exc w

/-- `allB`: for `j < n`, the three `w ≡ 0, r, -r (mod D1)` of the form `D1 j + e` pass `vOK`. -/
def allB (N Wb r D1 : Nat) (Ds exc : List Nat) : Nat → Bool
  | 0 => true
  | j + 1 => vOK N Wb r Ds exc (D1 * j) && vOK N Wb r Ds exc (D1 * j + r) &&
      vOK N Wb r Ds exc (D1 * j + (D1 - r)) && allB N Wb r D1 Ds exc j

def dOK (N r D : Nat) : Bool :=
  decide (N + 1 + r ≤ D) && decide (D ≤ 2 * N) && decide (Nat.gcd D r = 1)

def entOK (N : Nat) (e : Ent) : Bool :=
  e.Ds.all (dOK N e.r) && decide (e.Ds ≠ []) && dOK N e.r e.D0 && decide (e.D0 + 1 ≤ 2 * N) &&
    decide (e.D0 * N ^ 2 ≤ 2 * (2 * N - e.D0) * e.Wb) &&
    allB N e.Wb e.r (e.Ds.headD 1) e.Ds e.exc (e.Wb / (e.Ds.headD 1) + 1)

def tabOK (N : Nat) (tab : List Ent) : Bool :=
  decide (tab.map Ent.r = List.range' 1 (N / 2)) && tab.all (entOK N) &&
    tab.all (fun e => e.exc.isEmpty ||
      (decide (N = 14) && decide (e.r = 6) && decide (e.exc = [69, 75, 144, 431])))

theorem okW_sound {r w D : Nat} (hD : 0 < D) (h : okW r w D = true) :
    ¬ ((D : ℤ) ∣ (w : ℤ)) ∧ ¬ ((D : ℤ) ∣ (w : ℤ) - (r : ℤ)) ∧ ¬ ((D : ℤ) ∣ (w : ℤ) + (r : ℤ)) := by
  simp only [okW, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨h0, h1⟩, h2⟩ := h
  refine ⟨?_, ?_, ?_⟩
  · intro hd
    exact h0 (Nat.mod_eq_zero_of_dvd (Int.natCast_dvd_natCast.mp hd))
  · intro hd
    apply h1
    have hm : (r : ℤ) ≡ (w : ℤ) [ZMOD (D : ℤ)] := Int.modEq_iff_dvd.mpr hd
    have hm' : r ≡ w [MOD D] := Int.natCast_modEq_iff.mp hm
    exact hm'.symm
  · intro hd
    apply h2
    have : D ∣ w + r := by
      have : (D : ℤ) ∣ ((w + r : ℕ) : ℤ) := by push_cast; exact hd
      exact Int.natCast_dvd_natCast.mp this
    exact Nat.mod_eq_zero_of_dvd this

theorem allB_sound {N Wb r D1 : Nat} {Ds exc : List Nat} :
    ∀ n, allB N Wb r D1 Ds exc n = true → ∀ j, j < n →
      vOK N Wb r Ds exc (D1 * j) = true ∧ vOK N Wb r Ds exc (D1 * j + r) = true ∧
      vOK N Wb r Ds exc (D1 * j + (D1 - r)) = true := by
  intro n
  induction n with
  | zero => intro _ j hj; omega
  | succ n ih =>
    intro h j hj
    simp only [allB, Bool.and_eq_true] at h
    obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := h
    rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj' | hj'
    · exact ih h4 j hj'
    · subst hj'
      exact ⟨h1, h2, h3⟩

theorem wOK_cov {N : Nat} {e : Ent} (hDs : ∀ D ∈ e.Ds, dOK N e.r D = true) {w : Nat}
    (hj : wOK e.r e.Ds e.exc w = true) : WitnessCover N e.r w ∨ w ∈ e.exc := by
  simp only [wOK, Bool.or_eq_true, List.contains_iff_mem, List.any_eq_true] at hj
  rcases hj with hj | ⟨D, hDm, hok⟩
  · exact Or.inr (by simpa using hj)
  · left
    have hd := hDs D hDm
    simp only [dOK, Bool.and_eq_true, decide_eq_true_eq] at hd
    obtain ⟨⟨hd1, hd2⟩, hd3⟩ := hd
    obtain ⟨c0, c1, c2⟩ := okW_sound (by omega) hok
    exact Or.inl ⟨D, hd1, hd2, hd3, c0, c1, c2⟩

/-- Soundness of one row: every `w > N` is either covered or listed as an exception. -/
theorem entOK_sound {N : Nat} {e : Ent} (hN : 3 ≤ N) (hr : 1 ≤ e.r) (h : entOK N e = true) :
    ∀ w, N < w → WitnessCover N e.r w ∨ w ∈ e.exc := by
  simp only [entOK, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at h
  obtain ⟨⟨⟨⟨⟨hDs, hne⟩, hD0⟩, hD0b⟩, hL⟩, hB⟩ := h
  intro w hw
  by_cases hwb : w < e.Wb
  · obtain ⟨D1, rest, hD1⟩ : ∃ D1 rest, e.Ds = D1 :: rest := by
      cases hh : e.Ds with
      | nil => exact absurd hh hne
      | cons a b => exact ⟨a, b, rfl⟩
    have hD1m : D1 ∈ e.Ds := by rw [hD1]; exact List.mem_cons_self
    have hd := hDs D1 hD1m
    simp only [dOK, Bool.and_eq_true, decide_eq_true_eq] at hd
    obtain ⟨⟨hd1, hd2⟩, hd3⟩ := hd
    have hhead : e.Ds.headD 1 = D1 := by rw [hD1]; rfl
    rw [hhead] at hB
    have hD1pos : 0 < D1 := by omega
    have hrD : e.r < D1 := by omega
    by_cases hok : okW e.r w D1 = true
    · have hw' : wOK e.r e.Ds e.exc w = true := by
        simp only [wOK, Bool.or_eq_true, List.any_eq_true]
        exact Or.inr ⟨D1, hD1m, hok⟩
      exact wOK_cov hDs hw'
    · have hbad : w % D1 = 0 ∨ w % D1 = e.r ∨ w % D1 = D1 - e.r := by
        have hnot : ¬ (w % D1 ≠ 0 ∧ w % D1 ≠ e.r % D1 ∧ (w + e.r) % D1 ≠ 0) := by
          intro hh
          apply hok
          simp only [okW, Bool.and_eq_true, decide_eq_true_eq]
          exact ⟨⟨hh.1, hh.2.1⟩, hh.2.2⟩
        have hrm : e.r % D1 = e.r := Nat.mod_eq_of_lt hrD
        rw [hrm] at hnot
        by_cases a0 : w % D1 = 0
        · exact Or.inl a0
        · by_cases a1 : w % D1 = e.r
          · exact Or.inr (Or.inl a1)
          · right; right
            have a2 : (w + e.r) % D1 = 0 := by
              by_contra a2
              exact hnot ⟨a0, a1, a2⟩
            have hm : w % D1 < D1 := Nat.mod_lt _ hD1pos
            have hadd : (w % D1 + e.r % D1) % D1 = 0 := by rw [← Nat.add_mod]; exact a2
            rw [hrm] at hadd
            obtain ⟨c, hc⟩ := Nat.dvd_of_mod_eq_zero hadd
            have hpos : 0 < w % D1 := Nat.pos_of_ne_zero a0
            rcases c with _ | _ | c
            · omega
            · omega
            · have : D1 * 2 ≤ D1 * (c + 1 + 1) := Nat.mul_le_mul_left D1 (by omega)
              omega
      have hdm := Nat.div_add_mod w D1
      have hjlt : w / D1 < e.Wb / D1 + 1 := by
        have : w / D1 ≤ e.Wb / D1 := Nat.div_le_div_right (by omega)
        omega
      have hv := allB_sound _ hB (w / D1) hjlt
      have hw'' : wOK e.r e.Ds e.exc w = true := by
        rcases hbad with hb | hb | hb
        · have hv1 := hv.1
          have ew : D1 * (w / D1) = w := by omega
          rw [ew] at hv1
          simp only [vOK, Bool.or_eq_true, decide_eq_true_eq] at hv1
          rcases hv1 with (hv1 | hv1) | hv1
          · omega
          · omega
          · exact hv1
        · have hv1 := hv.2.1
          have ew : D1 * (w / D1) + e.r = w := by omega
          rw [ew] at hv1
          simp only [vOK, Bool.or_eq_true, decide_eq_true_eq] at hv1
          rcases hv1 with (hv1 | hv1) | hv1
          · omega
          · omega
          · exact hv1
        · have hv1 := hv.2.2
          have ew : D1 * (w / D1) + (D1 - e.r) = w := by omega
          rw [ew] at hv1
          simp only [vOK, Bool.or_eq_true, decide_eq_true_eq] at hv1
          rcases hv1 with (hv1 | hv1) | hv1
          · omega
          · omega
          · exact hv1
      exact wOK_cov hDs hw''
  · left
    simp only [dOK, Bool.and_eq_true, decide_eq_true_eq] at hD0
    obtain ⟨⟨hd1, hd2⟩, hd3⟩ := hD0
    refine Or.inr ⟨e.D0, 2 * N - e.D0, hd1, by omega, by omega, hd3, ?_⟩
    have hwb' : e.Wb ≤ w := Nat.le_of_not_lt hwb
    calc e.D0 * N ^ 2 ≤ 2 * (2 * N - e.D0) * e.Wb := hL
      _ ≤ 2 * (2 * N - e.D0) * w := Nat.mul_le_mul_left _ hwb'

/-- Soundness of a table. -/
theorem tabOK_sound {N : Nat} {tab : List Ent} (hN : 3 ≤ N) (h : tabOK N tab = true) :
    ∀ r, 1 ≤ r → 2 * r ≤ N → ∀ w, N < w →
      WitnessCover N r w ∨ (N = 14 ∧ r = 6 ∧ (w = 69 ∨ w = 75 ∨ w = 144 ∨ w = 431)) := by
  simp only [tabOK, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at h
  obtain ⟨⟨hmap, hent⟩, hexc⟩ := h
  intro r hr1 hr2 w hw
  have hmem : r ∈ tab.map Ent.r := by
    rw [hmap]
    simp only [List.mem_range'_1]
    omega
  obtain ⟨e, he, her⟩ := List.mem_map.mp hmem
  have hs := entOK_sound hN (by rw [her]; exact hr1) (hent e he) w hw
  rw [her] at hs
  rcases hs with hs | hs
  · exact Or.inl hs
  · right
    have hx := hexc e he
    simp only [Bool.or_eq_true, List.isEmpty_iff, Bool.and_eq_true, decide_eq_true_eq] at hx
    rcases hx with hx | ⟨⟨h14, h6⟩, hl⟩
    · rw [hx] at hs
      simp at hs
    · refine ⟨h14, by rw [← her]; exact h6, ?_⟩
      rw [hl] at hs
      simpa using hs

end Gap
end Sext6
end LRSpectrumFull
