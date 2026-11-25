import LRSpectrumFull.Sext6.K313.Chk
/- Soundness of the Bool checker, core-only (no Mathlib).  Layers L-b (search invariant) and L-c (masks to sets). -/
namespace KC

theorem one_shl (c : Nat) : (1 <<< c) = 2^c := by rw [Nat.shiftLeft_eq, Nat.one_mul]
theorem bit_tb (c x : Nat) : (1 <<< c).testBit x = decide (c = x) := by rw [one_shl, Nat.testBit_two_pow]

theorem clr_spec : ∀ x : Nat, x ≠ 0 → ∃ c, x.testBit c = true ∧
    ∀ i, (clr x).testBit i = (x.testBit i && !decide (i = c)) := by
  intro x
  induction x using Nat.strongRecOn with
  | _ x ih =>
    intro hx
    rcases Nat.mod_two_eq_zero_or_one x with h0 | h1
    · have hz : x / 2 ≠ 0 := by omega
      obtain ⟨c', hc', hy⟩ := ih (x / 2) (by omega) hz
      refine ⟨c' + 1, ?_, ?_⟩
      · rw [Nat.testBit_succ]; exact hc'
      · intro i
        rcases i with _ | j
        · simp [clr, Nat.testBit_and, Nat.testBit_zero, h0]
        · have e : (x - 1) / 2 = x / 2 - 1 := by omega
          have hy' := hy j
          simp only [clr, Nat.testBit_and] at hy' ⊢
          simp only [Nat.testBit_succ]
          rw [e, hy']
          simp
    · refine ⟨0, ?_, ?_⟩
      · simp [Nat.testBit_zero, h1]
      · intro i
        rcases i with _ | j
        · have : (x - 1) % 2 = 0 := by omega
          simp [clr, Nat.testBit_and, Nat.testBit_zero, h1, this]
        · have e : (x - 1) / 2 = x / 2 := by omega
          simp only [clr, Nat.testBit_and]
          simp only [Nat.testBit_succ]
          rw [e]
          simp

theorem lowb_spec (x : Nat) (hx : x ≠ 0) : ∃ c, lowb x = 1 <<< c ∧ x.testBit c = true ∧
    ∀ i, (clr x).testBit i = (x.testBit i && !decide (i = c)) := by
  obtain ⟨c, hc, hy⟩ := clr_spec x hx
  refine ⟨c, ?_, hc, hy⟩
  apply Nat.eq_of_testBit_eq; intro i
  unfold lowb
  rw [Nat.testBit_xor, hy, bit_tb]
  by_cases h : i = c
  · subst h; simp [hc]
  · have h' : c ≠ i := fun e => h e.symm
    cases x.testBit i <;> simp [h, h']

theorem idx_bit : ∀ c, c < 256 → idx (1 <<< c) = c := by decide +kernel

/-- coverage relation on residues 1..h -/
def cv (p h r a : Nat) : Prop := 1 ≤ r ∧ r ≤ h ∧ 1 ≤ a ∧ a ≤ h ∧ coverB p r a = true

theorem cv_comm (p h r a : Nat) : cv p h r a ↔ cv p h a r := by
  unfold cv coverB; rw [Nat.mul_comm r a]
  constructor <;> rintro ⟨a1, a2, a3, a4, a5⟩ <;> exact ⟨a3, a4, a1, a2, a5⟩

theorem cvb_iff (p h r a : Nat) : cvb p h r a = true ↔ cv p h r a := by
  simp [cvb, cv, and_assoc]

structure Env (p h T M W : Nat) : Prop where
  hh : h < 256
  hHW : h < W
  rows : ∀ r, r < 256 → ∀ a, (msk T M W r).testBit a = true ↔ cv p h r a

theorem env_of_tabOK (p h T M W : Nat) (h1 : h < 256) (h2 : h < W) (hM : M = 2 ^ W)
    (hT : tabOK p h T M W = true) : Env p h T M W := by
  refine ⟨h1, h2, ?_⟩
  intro r hr a
  by_cases ha : a < W
  · have := List.all_eq_true.1 hT r (List.mem_range.2 hr)
    have := List.all_eq_true.1 this a (List.mem_range.2 ha)
    rw [← cvb_iff]
    simpa using this
  · have hlt : msk T M W r < 2 ^ W := by unfold msk; rw [hM]; exact Nat.mod_lt _ (Nat.two_pow_pos W)
    have : (msk T M W r).testBit a = false := Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le hlt (Nat.pow_le_pow_right (by omega) (by omega)))
    rw [this]
    constructor
    · intro h; cases h
    · intro hc; exact absurd (Nat.lt_of_le_of_lt hc.2.2.2.1 h2) ha

/-- semantic: residue classes in `s` (mask) together with list `L` contain a class `u*(1..6)` -/
def ClassIn (p h s : Nat) (L : List Nat) : Prop :=
  ∃ u, 1 ≤ u ∧ u ≤ h ∧ ∀ i, 1 ≤ i → i ≤ 6 → (s.testBit (red p (u*i)) = true ∨ red p (u*i) ∈ L)

theorem ClassIn.mono {p h s : Nat} {L L' : List Nat} (hL : ∀ x, x ∈ L → x ∈ L') (c : ClassIn p h s L) : ClassIn p h s L' := by
  obtain ⟨u, h1, h2, h3⟩ := c
  exact ⟨u, h1, h2, fun i a b => (h3 i a b).imp id (hL _)⟩

def Good (p h k s unc ex : Nat) : Prop :=
  ∀ L : List Nat, L.length ≤ k → (∀ t ∈ L, ex.testBit t = false) →
    (∀ a, unc.testBit a = true → ∃ t ∈ L, cv p h t a) → ClassIn p h s L

def BU (u : Nat) : Prop := ∀ a, u.testBit a = true → a < 256

theorem testBit_diff (u m a : Nat) : (u ^^^ (u &&& m)).testBit a = (u.testBit a && !m.testBit a) := by
  simp only [Nat.testBit_xor, Nat.testBit_and]; cases u.testBit a <;> cases m.testBit a <;> rfl

theorem BU_diff {u m : Nat} (h : BU u) : BU (u ^^^ (u &&& m)) := by
  intro a ha; rw [testBit_diff] at ha
  exact h a (Bool.and_eq_true_iff.1 ha).1

/-- leaf soundness -/
theorem anyCls_sound (p h s : Nat) : ∀ f rest, (∀ i, rest.testBit i = true → s.testBit i = true ∧ i < 256) →
    anyCls p h s f rest = true → ClassIn p h s [] := by
  intro f
  induction f with
  | zero => intro rest _ h; simp [anyCls] at h
  | succ f ih =>
    intro rest hr h
    by_cases h0 : rest = 0
    · subst h0; simp [anyCls] at h
    · obtain ⟨c, hb, hc, hy⟩ := lowb_spec rest h0
      have hc256 := (hr c hc).2
      have hidx : idx (1 <<< c) = c := idx_bit c hc256
      simp only [anyCls, if_neg (by simpa using h0), hb, hidx, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq,
        beq_iff_eq] at h
      rcases h with ⟨⟨⟨hc1, hc2⟩, hm⟩⟩ | h
      · refine ⟨c, hc1, hc2, ?_⟩
        intro i hi1 hi2
        left
        rw [← hm]
        have : ∀ j, j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨ j = 5 ∨ j = 6 → (mk6 p c).testBit (red p (c*j)) = true := by
          intro j hj
          rcases hj with rfl | rfl | rfl | rfl | rfl | rfl <;>
            simp [mk6, Nat.testBit_or, one_shl, Nat.testBit_two_pow_self]
        exact this i (by omega)
      · apply ih (clr rest) _ h
        intro i hi
        have := hy i
        rw [this] at hi
        have h2 : rest.testBit i = true := by cases hh : rest.testBit i <;> simp_all
        exact hr i h2

theorem leafB_sound (p h s : Nat) (hs : ∀ i, s.testBit i = true → i < 256) (H : leafB p h s = true) :
    ∀ L : List Nat, ClassIn p h s L :=
  fun L => (anyCls_sound p h s 8 s (fun i hi => ⟨hi, hs i hi⟩) H).mono (by simp)

theorem andAll_mono (T M W : Nat) : ∀ f rest acc i, acc.testBit i = true →
    (∀ a, rest.testBit a = true → a < 256 ∧ (msk T M W a).testBit i = true) →
    (andAll T M W f rest acc).testBit i = true := by
  intro f
  induction f with
  | zero => intro rest acc i h _; simpa [andAll] using h
  | succ f ih =>
    intro rest acc i hacc hr
    by_cases h0 : (rest == 0 || acc == 0) = true
    · simp only [andAll, h0, if_true]; exact hacc
    · have h0' : rest ≠ 0 := by intro e; apply h0; simp [e]
      simp only [andAll, h0, if_false, Bool.false_eq_true]
      obtain ⟨c, hb, hc, hy⟩ := lowb_spec rest h0'
      have hidx : idx (1 <<< c) = c := idx_bit c (hr c hc).1
      rw [hb, hidx]
      apply ih
      · rw [Nat.testBit_and, hacc]; simpa using (hr c hc).2
      · intro a ha
        rw [hy] at ha
        exact hr a (by cases hh : rest.testBit a <;> simp_all)

theorem leavesB_sound (p h s : Nat) : ∀ f cand, leavesB p h s f cand = true →
    ∀ i, cand.testBit i = true → leafB p h (s ||| (1 <<< i)) = true := by
  intro f
  induction f with
  | zero => intro cand h; simp [leavesB] at h; subst h; simp
  | succ f ih =>
    intro cand h i hi
    by_cases h0 : cand = 0
    · subst h0; simp at hi
    · obtain ⟨c, hb, hc, hy⟩ := lowb_spec cand h0
      simp only [leavesB, Bool.or_eq_true, beq_iff_eq, h0, false_or, Bool.and_eq_true] at h
      by_cases hic : i = c
      · subst hic; rw [← hb]; exact h.1
      · apply ih (clr cand) h.2 i
        rw [hy]; simp [hi, hic]

theorem ClassIn.shift {p h s c : Nat} {L L' : List Nat} (hc : c ∈ L) (hL : ∀ x, x ∈ L' → x ∈ L)
    (C : ClassIn p h (s ||| (1 <<< c)) L') : ClassIn p h s L := by
  obtain ⟨u, h1, h2, h3⟩ := C
  refine ⟨u, h1, h2, fun i a b => ?_⟩
  rcases h3 i a b with hh | hh
  · rw [Nat.testBit_or, bit_tb] at hh
    simp only [Bool.or_eq_true, decide_eq_true_eq] at hh
    rcases hh with hh | hh
    · exact Or.inl hh
    · exact Or.inr (hh ▸ hc)
  · exact Or.inr (hL _ hh)

variable {p h T M W : Nat}

theorem kids_sound (hE : Env p h T M W) (unc s k : Nat) (child : Nat → Nat → Nat → Bool)
    (hchild : ∀ u e s', BU u → BU s' → child u e s' = true → Good p h k s' u e) (hu : BU unc) (hs : BU s) :
    ∀ f cand ex, (∀ i, cand.testBit i = true → i < 256) → kidsB child T M W unc s f cand ex = true →
    ∀ L : List Nat, L.length ≤ k + 1 → (∀ t ∈ L, ex.testBit t = false) →
    (∀ a, unc.testBit a = true → ∃ t ∈ L, cv p h t a) → (∃ t ∈ L, cand.testBit t = true) → ClassIn p h s L := by
  intro f
  induction f with
  | zero =>
    intro cand ex _ hk L _ _ _ ⟨t, _, ht⟩
    simp [kidsB] at hk; subst hk; simp at ht
  | succ f ih =>
    intro cand ex hcb hk L hlen hex hcov ⟨t, htL, htc⟩
    have h0 : cand ≠ 0 := by intro e; subst e; simp at htc
    obtain ⟨c, hb, hc, hy⟩ := lowb_spec cand h0
    have hc256 := hcb c hc
    have hidx : idx (1 <<< c) = c := idx_bit c hc256
    simp only [kidsB, Bool.or_eq_true, beq_iff_eq, h0, false_or, Bool.and_eq_true, hb, hidx] at hk
    obtain ⟨hk1, hk2⟩ := hk
    by_cases hcL : c ∈ L
    · have hbs : BU (s ||| 1 <<< c) := by
        intro i hi; rw [Nat.testBit_or, bit_tb] at hi
        simp only [Bool.or_eq_true, decide_eq_true_eq] at hi
        rcases hi with hi | hi
        · exact hs i hi
        · subst hi; exact hc256
      have hgood := hchild _ _ _ (BU_diff hu) hbs hk1
      have hC := hgood (L.erase c) (by have := List.length_erase_of_mem hcL; omega)
        (fun t' ht' => hex t' (List.mem_of_mem_erase ht'))
        (by
          intro a ha
          rw [testBit_diff] at ha
          have ha1 : unc.testBit a = true := by cases hh : unc.testBit a <;> simp_all
          have ha2 : (msk T M W c).testBit a = false := by cases hh : (msk T M W c).testBit a <;> simp_all
          obtain ⟨t', ht'L, ht'cv⟩ := hcov a ha1
          refine ⟨t', (List.mem_erase_of_ne ?_).2 ht'L, ht'cv⟩
          intro e; subst e
          have := (hE.rows t' hc256 a).2 ht'cv
          rw [this] at ha2; cases ha2)
      exact ClassIn.shift hcL (fun x hx => List.mem_of_mem_erase hx) hC
    · have htc' : t ≠ c := fun e => hcL (e ▸ htL)
      refine ih (clr cand) (ex ||| 1 <<< c) ?_ hk2 L hlen ?_ hcov ⟨t, htL, ?_⟩
      · intro i hi; rw [hy] at hi
        exact hcb i (by cases hh : cand.testBit i <;> simp_all)
      · intro t' ht'
        have : t' ≠ c := fun e => hcL (e ▸ ht')
        rw [Nat.testBit_or, bit_tb, hex t' ht']; simp [this, Ne.symm this]
      · rw [hy]; simp [htc, htc']

theorem stepB_sound (hE : Env p h T M W) (lp : Bool) (k : Nat) (rec : Nat → Nat → Nat → Bool)
    (hrec : ∀ u e s', BU u → BU s' → rec u e s' = true → Good p h k s' u e) (unc ex s : Nat) (hu : BU unc)
    (hs : BU s)
    (hk : stepB p h T M W lp k rec unc ex s = true) : Good p h (k + 1) s unc ex := by
  intro L hlen hex hcov
  by_cases h0 : unc = 0
  · subst h0
    simp only [stepB, beq_self_eq_true, if_true] at hk
    exact leafB_sound p h s hs hk L
  · simp only [stepB, if_neg (by simpa using h0 : ¬ (unc == 0) = true)] at hk
    obtain ⟨c0, hb0, hc0, hy0⟩ := lowb_spec unc h0
    have hc0256 := hu c0 hc0
    have hidx : idx (1 <<< c0) = c0 := idx_bit c0 hc0256
    obtain ⟨t, htL, htcv⟩ := hcov c0 hc0
    have htrow : (msk T M W c0).testBit t = true := (hE.rows c0 hc0256 t).2 ((cv_comm _ _ _ _).1 htcv)
    by_cases hlast : (lp && k == 0) = true
    · simp only [hlast, if_true] at hk
      have hk0 : k = 0 := by simpa using (Bool.and_eq_true_iff.1 hlast).2
      subst hk0
      -- L = [t]
      have hLt : L = [t] := by
        match L, hlen, htL with
        | [], _, htL => simp at htL
        | [x], _, htL => simp at htL; rw [htL]
        | _ :: _ :: _, hl, _ => simp at hl
      subst hLt
      simp only [lastB, hb0, hidx] at hk
      have hacc : (andAll T M W 240 (clr unc) (msk T M W c0 ^^^ (msk T M W c0 &&& ex))).testBit t = true := by
        apply andAll_mono
        · rw [testBit_diff, htrow, hex t (by simp)]; rfl
        · intro a ha
          rw [hy0] at ha
          have ha1 : unc.testBit a = true := by cases hh : unc.testBit a <;> simp_all
          obtain ⟨t', ht', hcv'⟩ := hcov a ha1
          have : t' = t := by simpa using ht'
          subst this
          exact ⟨hu a ha1, (hE.rows a (hu a ha1) t').2 ((cv_comm _ _ _ _).1 hcv')⟩
      have hleaf := leavesB_sound p h s 240 _ hk t hacc
      have hs' : BU (s ||| 1 <<< t) := by
        intro i hi; rw [Nat.testBit_or, bit_tb] at hi
        simp only [Bool.or_eq_true, decide_eq_true_eq] at hi
        rcases hi with hi | hi
        · exact hs i hi
        · subst hi; exact Nat.lt_of_le_of_lt ((hE.rows c0 hc0256 t).1 htrow).2.2.2.1 hE.hh
      exact ClassIn.shift (by simp) (fun x hx => by simp at hx) (leafB_sound p h _ hs' hleaf [])
    · simp only [hlast, if_false, Bool.false_eq_true] at hk
      simp only [hb0, hidx] at hk
      refine kids_sound hE unc s k rec hrec hu hs 240 _ ex ?_ hk L hlen hex hcov ⟨t, htL, ?_⟩
      · intro i hi; rw [testBit_diff] at hi
        have : (msk T M W c0).testBit i = true := by cases hh : (msk T M W c0).testBit i <;> simp_all
        exact Nat.lt_of_le_of_lt ((hE.rows c0 hc0256 i).1 this).2.2.2.1 hE.hh
      · rw [testBit_diff, htrow, hex t htL]; rfl

theorem dfsB_sound (hE : Env p h T M W) (lp : Bool) : ∀ k unc ex s, BU unc →
    BU s → dfsB p h T M W lp k unc ex s = true → Good p h k s unc ex := by
  intro k
  induction k with
  | zero =>
    intro unc ex s hu hs hk L hlen _ hcov
    by_cases h0 : unc = 0
    · subst h0; simp only [dfsB, beq_self_eq_true, if_true] at hk; exact leafB_sound p h s hs hk L
    · obtain ⟨c, _, hc, _⟩ := lowb_spec unc h0
      have : L = [] := List.eq_nil_of_length_eq_zero (by omega)
      subst this
      obtain ⟨t, ht, _⟩ := hcov c hc
      simp at ht
  | succ k ih =>
    intro unc ex s hu hs hk
    refine stepB_sound hE lp k (dfsB p h T M W lp k) ?_ unc ex s hu hs hk
    intro u e s' hu' hs'' hk'
    exact ih u e s' hu' hs'' hk'
end KC
