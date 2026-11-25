import Mathlib.Data.ZMod.Basic
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Finset.Card
import LRSpectrumFull.Sext6.Statement
import LRSpectrumFull.Sext6.K313.Sound0
/- Soundness theorem for the Bool checker (layer L-a, Mathlib) and assembly.  See CHECKPOINT AF. -/
namespace KC
open LRSpectrumFull.Sext6

variable {p h T M W : Nat}

theorem topB_sound (hE : Env p h T M W) (lp : Bool) (m : Nat) (rec : Nat → Nat → Nat → Bool)
    (hrec : ∀ u e s', BU u → BU s' → rec u e s' = true → Good p h m s' u e) :
    ∀ D unc ex s, BU unc → BU s → topB p h T M W lp m rec D unc ex s = true → Good p h (m + D) s unc ex := by
  intro D
  induction D with
  | zero => intro unc ex s hu hs hk; exact hrec unc ex s hu hs hk
  | succ D ih =>
    intro unc ex s hu hs hk
    exact stepB_sound hE lp (m + D) (topB p h T M W lp m rec D) (fun u e s' hu' hs' hk' => ih u e s' hu' hs' hk')
      unc ex s hu hs hk

/-- what the search proves, as a statement about residue sets in 1..h -/
def CoreStmt (p h : Nat) : Prop :=
  ∀ R : Finset ℕ, R.card ≤ 6 → 1 ∈ R → (∀ r ∈ R, 1 ≤ r ∧ r ≤ h) →
    (∀ a, 1 ≤ a → a ≤ h → ∃ r ∈ R, coverB p r a = true) →
    ∃ u, 1 ≤ u ∧ u ≤ h ∧ ∀ i, 1 ≤ i → i ≤ 6 → red p (u * i) ∈ R

theorem unc0_key (hE : Env p h T M W) (hM : M = 2 ^ W) (hW : W = h + 1) :
    ∀ a, (unc0 T M W).testBit a = true → 1 ≤ a ∧ a ≤ h ∧ ¬ cv p h 1 a := by
  have hMW : ∀ a, (M - 1).testBit a = decide (a < W) := fun a => by rw [hM]; exact Nat.testBit_two_pow_sub_one W a
  have h1' : ∀ a : Nat, (1 : Nat).testBit a = decide (a = 0) := by
    intro a; cases a <;> simp [Nat.testBit_succ]
  have key : ∀ a, (unc0 T M W).testBit a = true → 1 ≤ a ∧ a ≤ h ∧ ¬ cv p h 1 a := by
    intro a hu
    have hrow := hE.rows 1 (by norm_num) a
    simp only [unc0, Nat.testBit_xor, hMW, h1'] at hu
    by_cases hr : (msk T M W 1).testBit a = true
    · have hc := hrow.1 hr
      have ha1 : 1 ≤ a := hc.2.2.1
      have ha2 : a ≤ h := hc.2.2.2.1
      have : a < W := by omega
      rw [hr] at hu
      simp [this, show a ≠ 0 by omega] at hu
    · have hr' : (msk T M W 1).testBit a = false := by simpa using hr
      rw [hr'] at hu
      have hnc : ¬ cv p h 1 a := fun hc => hr (hrow.2 hc)
      by_cases ha0 : a = 0
      · subst ha0
        have hW0 : 0 < W := by omega
        simp [hW0] at hu
      · by_cases haW : a < W
        · exact ⟨by omega, by omega, hnc⟩
        · simp [haW, ha0] at hu
  exact key

theorem core_of_good (hE : Env p h T M W) (hM : M = 2 ^ W) (hW : W = h + 1) (hW256 : W ≤ 256)
    (hg : Good p h 5 2 (unc0 T M W) 2) : CoreStmt p h := by
  intro R hcard h1 hR hit
  have key := unc0_key hE hM hW
  have hBU : BU (unc0 T M W) := by
    intro a ha
    have := key a ha
    omega
  have hex : ∀ t ∈ (R.erase 1).toList, (2 : Nat).testBit t = false := by
    intro t ht
    rw [Finset.mem_toList, Finset.mem_erase] at ht
    have h2 : (2 : Nat).testBit t = decide (1 = t) := by
      simpa using Nat.testBit_two_pow (n := 1) (m := t)
    rw [h2]; simp [Ne.symm ht.1]
  have hcov : ∀ a, (unc0 T M W).testBit a = true → ∃ t ∈ (R.erase 1).toList, cv p h t a := by
    intro a ha
    obtain ⟨ha1, ha2, hnc⟩ := key a ha
    obtain ⟨r, hrR, hrc⟩ := hit a ha1 ha2
    have hr1 : r ≠ 1 := by
      intro e; subst e
      exact hnc ⟨le_refl _, by omega, ha1, ha2, hrc⟩
    refine ⟨r, by rw [Finset.mem_toList, Finset.mem_erase]; exact ⟨hr1, hrR⟩, ?_⟩
    exact ⟨(hR r hrR).1, (hR r hrR).2, ha1, ha2, hrc⟩
  have hlen : (R.erase 1).toList.length ≤ 5 := by
    rw [Finset.length_toList, Finset.card_erase_of_mem h1]; omega
  obtain ⟨u, hu1, hu2, hu3⟩ := hg _ hlen hex hcov
  refine ⟨u, hu1, hu2, fun i hi1 hi2 => ?_⟩
  rcases hu3 i hi1 hi2 with hh | hh
  · have h2 : (2 : Nat).testBit (red p (u * i)) = decide (1 = red p (u * i)) := by
      simpa using Nat.testBit_two_pow (n := 1) (m := red p (u * i))
    rw [h2] at hh
    have : 1 = red p (u * i) := by simpa using hh
    rw [← this]; exact h1
  · exact Finset.mem_of_mem_erase (Finset.mem_toList.1 hh)

/-! ## Layer L-a: from CoreStmt to CleanPrime -/

section LA
variable (p : ℕ) [Fact p.Prime]

theorem red_cast (n : ℕ) : ((red p n : ℕ) : ZMod p) = (n : ZMod p) ∨ ((red p n : ℕ) : ZMod p) = -(n : ZMod p) := by
  have hn : ((n % p : ℕ) : ZMod p) = (n : ZMod p) := ZMod.natCast_mod n p
  have hlt : n % p < p := Nat.mod_lt _ (Fact.out : p.Prime).pos
  unfold red
  simp only []
  by_cases hc : 2 * (n % p) > p
  · rw [if_pos hc]; right
    rw [Nat.cast_sub hlt.le, ZMod.natCast_self, hn]; ring
  · rw [if_neg hc]; left; exact hn

theorem red_range (hp2 : p % 2 = 1) (n : ℕ) (hn : n % p ≠ 0) : 1 ≤ red p n ∧ red p n ≤ (p - 1) / 2 := by
  have hlt : n % p < p := Nat.mod_lt _ (Fact.out : p.Prime).pos
  unfold red; simp only []
  split_ifs <;> omega

def dz (z : ZMod p) : ℕ := min z.val (p - z.val)

theorem dz_neg (z : ZMod p) : dz p (-z) = dz p z := by
  unfold dz
  have hlt := ZMod.val_lt z
  by_cases hz : z = 0
  · subst hz; simp
  · rw [ZMod.neg_val, if_neg hz]; omega

theorem coverB_iff (r a : ℕ) : coverB p r a = true ↔ 7 * dz p ((r * a : ℕ) : ZMod p) ≤ p := by
  unfold coverB dz
  rw [ZMod.val_natCast]; simp

theorem bdist_eq (x : ℤ) : bdist p x = (dz p (x : ZMod p) : ℤ) := by
  unfold bdist dz
  have := ZMod.val_intCast (n := p) x
  have hlt := ZMod.val_lt (x : ZMod p)
  rw [← this]; push_cast [Nat.cast_sub hlt.le]; rfl

end LA

theorem clean_of_core (p : ℕ) (hp : p.Prime) (hp7 : 7 < p) (hC : CoreStmt p ((p - 1) / 2)) : CleanPrime p := by
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : Fact (1 < p) := ⟨by omega⟩
  have hp2 : p % 2 = 1 := by
    rcases hp.eq_two_or_odd with h | h
    · omega
    · exact h
  intro S hcard hnz hit
  have hne : ∀ z : ℤ, ¬ (p : ℤ) ∣ z → (z : ZMod p) ≠ 0 := fun z hz h0 =>
    hz ((ZMod.intCast_zmod_eq_zero_iff_dvd z p).1 h0)
  obtain ⟨r0, hr0S, -⟩ := hit 1 (by
    intro h; have := Int.le_of_dvd one_pos h; omega)
  set x0 : ZMod p := (r0 : ZMod p) with hx0
  have hx0ne : x0 ≠ 0 := hne r0 (hnz r0 hr0S)
  have hunit : IsUnit x0 := (isUnit_iff_ne_zero (G₀ := ZMod p)).2 hx0ne
  have hinv : x0⁻¹ * x0 = 1 := ZMod.inv_mul_of_unit x0 hunit
  have hinv2 : x0 * x0⁻¹ = 1 := by rw [mul_comm]; exact hinv
  have hinv0 : x0⁻¹ ≠ 0 := fun h0 => by rw [h0, zero_mul] at hinv; exact zero_ne_one hinv
  let φ : ℤ → ℕ := fun r => red p ((x0⁻¹ * (r : ZMod p)).val)
  have hφcast : ∀ r : ℤ, ((φ r : ℕ) : ZMod p) = x0⁻¹ * (r : ZMod p) ∨ ((φ r : ℕ) : ZMod p) = -(x0⁻¹ * (r : ZMod p)) := by
    intro r
    have := red_cast p ((x0⁻¹ * (r : ZMod p)).val)
    rwa [ZMod.natCast_zmod_val] at this
  have hφne : ∀ r ∈ S, (x0⁻¹ * (r : ZMod p)) ≠ 0 := fun r hr =>
    mul_ne_zero hinv0 (hne r (hnz r hr))
  have hφrange : ∀ r ∈ S, 1 ≤ φ r ∧ φ r ≤ (p - 1) / 2 := by
    intro r hr
    have hv : (x0⁻¹ * (r : ZMod p)).val ≠ 0 := fun h0 => hφne r hr ((ZMod.val_eq_zero _).1 h0)
    have hlt := ZMod.val_lt (x0⁻¹ * (r : ZMod p))
    refine red_range p hp2 _ ?_
    rw [Nat.mod_eq_of_lt hlt]; exact hv
  have hcore := hC (S.image φ) (Finset.card_image_le.trans hcard)
    (by
      rw [Finset.mem_image]
      refine ⟨r0, hr0S, ?_⟩
      show red p ((x0⁻¹ * (r0 : ZMod p)).val) = 1
      rw [← hx0, hinv, ZMod.val_one]
      unfold red; simp only []
      rw [Nat.mod_eq_of_lt (by omega)]; split_ifs <;> omega)
    (by
      intro r hr; rw [Finset.mem_image] at hr
      obtain ⟨s, hs, rfl⟩ := hr; exact hφrange s hs)
    (by
      intro a ha1 ha2
      have hpa : ¬ (p : ℤ) ∣ ((x0⁻¹.val : ℤ) * (a : ℤ)) := by
        intro hd
        have h0 : (((x0⁻¹.val : ℤ) * (a : ℤ) : ℤ) : ZMod p) = 0 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).2 hd
        push_cast at h0
        rw [ZMod.natCast_zmod_val] at h0
        have hane : (a : ZMod p) ≠ 0 := by
          intro h0'
          have := (ZMod.natCast_eq_zero_iff a p).1 h0'
          have := Nat.le_of_dvd (by omega) this
          omega
        exact mul_ne_zero hinv0 hane h0
      obtain ⟨r, hrS, hrh⟩ := hit _ hpa
      refine ⟨φ r, Finset.mem_image_of_mem _ hrS, ?_⟩
      rw [coverB_iff]
      rw [bdist_eq] at hrh
      have hz : (((x0⁻¹.val : ℤ) * (a : ℤ) * 0 : ℤ) : ZMod p) = 0 := by simp
      have e1 : (((r * ((x0⁻¹.val : ℤ) * (a : ℤ)) : ℤ)) : ZMod p) = x0⁻¹ * (r : ZMod p) * (a : ZMod p) := by
        push_cast; rw [ZMod.natCast_zmod_val]; ring
      rw [e1] at hrh
      have hrh' : 7 * dz p (x0⁻¹ * (r : ZMod p) * (a : ZMod p)) ≤ p := by exact_mod_cast hrh
      push_cast
      rcases hφcast r with hc | hc
      · rw [hc]; simpa [mul_assoc, mul_comm, mul_left_comm] using hrh'
      · rw [hc, neg_mul, dz_neg]; simpa [mul_assoc, mul_comm, mul_left_comm] using hrh')
  obtain ⟨u, hu1, hu2, hu3⟩ := hcore
  have hu0 : (u : ZMod p) ≠ 0 := by
    intro h0
    have := (ZMod.natCast_eq_zero_iff u p).1 h0
    have := Nat.le_of_dvd (by omega) this
    omega
  refine ⟨r0 * u, ?_, ?_⟩
  · intro hd
    have h0 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).2 hd
    push_cast at h0
    exact mul_ne_zero hx0ne hu0 h0
  · intro i hi
    have hi' := Finset.mem_Icc.1 hi
    have hi1 : 1 ≤ i.toNat := by omega
    obtain ⟨hs, hsS, hsφ⟩ := Finset.mem_image.1 (hu3 i.toNat hi1 (by omega))
    refine ⟨hs, hsS, ?_⟩
    have hc1 := hφcast hs
    have hc2 := red_cast p (u * i.toNat)
    rw [hsφ] at hc1
    have hi_cast : ((i.toNat : ℕ) : ZMod p) = (i : ZMod p) := by
      have : (i.toNat : ℤ) = i := Int.toNat_of_nonneg (by omega)
      rw [← this]; simp
    push_cast at hc2
    rw [hi_cast] at hc2
    have hr : (hs : ZMod p) = x0 * (x0⁻¹ * (hs : ZMod p)) := by
      rw [← mul_assoc, hinv2, one_mul]
    have hdv : ∀ z : ℤ, (z : ZMod p) = 0 → (p : ℤ) ∣ z := fun z hz => (ZMod.intCast_zmod_eq_zero_iff_dvd z p).1 hz
    rcases hc1 with h1 | h1 <;> rcases hc2 with h2 | h2
    · left; apply hdv; push_cast; rw [hr, ← h1, h2]; simp [hx0]; ring
    · right; apply hdv; push_cast
      have : x0⁻¹ * (hs : ZMod p) = -((u : ZMod p) * i) := by rw [← h1]; exact h2
      rw [hr, this]; simp [hx0]; ring
    · right; apply hdv; push_cast
      have : x0⁻¹ * (hs : ZMod p) = -((u : ZMod p) * i) := by
        have := h1.symm.trans h2; exact neg_inj.1 (by rw [← this]; ring_nf) 
      rw [hr, this]; simp [hx0]; ring
    · left; apply hdv; push_cast
      have : x0⁻¹ * (hs : ZMod p) = ((u : ZMod p) * i) := by
        have := h1.symm.trans h2; exact neg_inj.1 this
      rw [hr, this]; simp [hx0]; ring


theorem bu2 : BU 2 := by
  intro a ha
  have h2 : (2 : Nat).testBit a = decide (1 = a) := by simpa using Nat.testBit_two_pow (n := 1) (m := a)
  rw [h2] at ha; simp at ha; omega

theorem good_root_of_top (hE : Env p h T M W) (hM : M = 2 ^ W) (hW : W = h + 1) (hW256 : W ≤ 256)
    (L : List (Nat × Nat × Nat))
    (hL : ∀ x ∈ L, dfsB p h T M W true 3 x.1 x.2.1 x.2.2 = true)
    (htop : topB p h T M W true 3 (memB L) 2 (unc0 T M W) 2 2 = true) : Good p h 5 2 (unc0 T M W) 2 := by
  have key := unc0_key hE hM hW
  have hBU : BU (unc0 T M W) := by
    intro a ha; have := key a ha; have := hE.hh; omega
  refine topB_sound hE true 3 (memB L) ?_ 2 (unc0 T M W) 2 2 hBU bu2 htop
  intro u e s' hu hs hk
  simp only [memB, List.any_eq_true, Bool.and_eq_true, beq_iff_eq] at hk
  obtain ⟨x, hx, ⟨e1, e2⟩, e3⟩ := hk
  have := hL x hx
  rw [e1, e2, e3] at this
  exact dfsB_sound hE true 3 u e s' hu hs this

theorem good_root_of_dfs (hE : Env p h T M W) (hM : M = 2 ^ W) (hW : W = h + 1)
    (hk : dfsB p h T M W true 5 (unc0 T M W) 2 2 = true) : Good p h 5 2 (unc0 T M W) 2 := by
  have key := unc0_key hE hM hW
  have hBU : BU (unc0 T M W) := by
    intro a ha; have := key a ha; have := hE.hh; omega
  exact dfsB_sound hE true 5 _ _ _ hBU bu2 hk

/-- SOUNDNESS (split form): table check + piece checks + top assembly give CleanPrime p. -/
theorem chk_sound_split (p T : Nat) (hp : p.Prime) (hp7 : 7 < p) (hp512 : p < 512)
    (hT : tabOK p ((p - 1) / 2) T (2 ^ ((p - 1) / 2 + 1)) ((p - 1) / 2 + 1) = true)
    (L : List (Nat × Nat × Nat))
    (hL : ∀ x ∈ L, dfsB p ((p - 1) / 2) T (2 ^ ((p - 1) / 2 + 1)) ((p - 1) / 2 + 1) true 3 x.1 x.2.1 x.2.2 = true)
    (htop : topB p ((p - 1) / 2) T (2 ^ ((p - 1) / 2 + 1)) ((p - 1) / 2 + 1) true 3 (memB L) 2
      (unc0 T (2 ^ ((p - 1) / 2 + 1)) ((p - 1) / 2 + 1)) 2 2 = true) : CleanPrime p := by
  have hE := env_of_tabOK p ((p - 1) / 2) T _ _ (by omega) (by omega) rfl hT
  exact clean_of_core p hp hp7 (core_of_good hE rfl rfl (by omega) (good_root_of_top hE rfl rfl (by omega) L hL htop))

/-- SOUNDNESS (monolithic form), used for small-prime controls. -/
theorem chk_sound (p T : Nat) (hp : p.Prime) (hp7 : 7 < p) (hp512 : p < 512)
    (hT : tabOK p ((p - 1) / 2) T (2 ^ ((p - 1) / 2 + 1)) ((p - 1) / 2 + 1) = true)
    (hk : dfsB p ((p - 1) / 2) T (2 ^ ((p - 1) / 2 + 1)) ((p - 1) / 2 + 1) true 5
      (unc0 T (2 ^ ((p - 1) / 2 + 1)) ((p - 1) / 2 + 1)) 2 2 = true) : CleanPrime p := by
  have hE := env_of_tabOK p ((p - 1) / 2) T _ _ (by omega) (by omega) rfl hT
  exact clean_of_core p hp hp7 (core_of_good hE rfl rfl (by omega) (good_root_of_dfs hE rfl rfl hk))


theorem memB_rec (hE : Env p h T M W) (m : Nat) (L : List (Nat × Nat × Nat))
    (hL : ∀ x ∈ L, ∀ u e s', BU u → BU s' → x.1 = u → x.2.1 = e → x.2.2 = s' → Good p h m s' u e) :
    ∀ u e s', BU u → BU s' → memB L u e s' = true → Good p h m s' u e := by
  intro u e s' hu hs hk
  simp only [memB, List.any_eq_true, Bool.and_eq_true, beq_iff_eq] at hk
  obtain ⟨x, hx, ⟨e1, e2⟩, e3⟩ := hk
  exact hL x hx u e s' hu hs e1 e2 e3

theorem good4_of_sub (hE : Env p h T M W) (L : List (Nat × Nat × Nat))
    (hL : ∀ x ∈ L, dfsB p h T M W true 3 x.1 x.2.1 x.2.2 = true) (u e s : Nat)
    (htop : topB p h T M W true 3 (memB L) 1 u e s = true) : BU u → BU s → Good p h 4 s u e := by
  intro hu hs
  refine topB_sound hE true 3 (memB L) (memB_rec hE 3 L ?_) 1 u e s hu hs htop
  intro x hx u e s' hu hs e1 e2 e3
  have := hL x hx
  rw [e1, e2, e3] at this
  exact dfsB_sound hE true 3 u e s' hu hs this

theorem good_root_of_L1 (hE : Env p h T M W) (hM : M = 2 ^ W) (hW : W = h + 1)
    (L : List (Nat × Nat × Nat))
    (hG : ∀ x ∈ L, BU x.1 → BU x.2.2 → Good p h 4 x.2.2 x.1 x.2.1)
    (htop : topB p h T M W true 4 (memB L) 1 (unc0 T M W) 2 2 = true) : Good p h 5 2 (unc0 T M W) 2 := by
  have key := unc0_key hE hM hW
  have hBU : BU (unc0 T M W) := by
    intro a ha; have := key a ha; have := hE.hh; omega
  refine topB_sound hE true 4 (memB L) (memB_rec hE 4 L ?_) 1 (unc0 T M W) 2 2 hBU bu2 htop
  intro x hx u e s' hu hs e1 e2 e3
  have := hG x hx
  rw [e1, e2, e3] at this
  exact this hu hs

theorem clean_of_L1 (p T : Nat) (hp : p.Prime) (hp7 : 7 < p) (hp512 : p < 512)
    (hT : tabOK p ((p - 1) / 2) T (2 ^ ((p - 1) / 2 + 1)) ((p - 1) / 2 + 1) = true)
    (L : List (Nat × Nat × Nat))
    (hG : ∀ x ∈ L, BU x.1 → BU x.2.2 → Good p ((p - 1) / 2) 4 x.2.2 x.1 x.2.1)
    (htop : topB p ((p - 1) / 2) T (2 ^ ((p - 1) / 2 + 1)) ((p - 1) / 2 + 1) true 4 (memB L) 1
      (unc0 T (2 ^ ((p - 1) / 2 + 1)) ((p - 1) / 2 + 1)) 2 2 = true) : CleanPrime p := by
  have hE := env_of_tabOK p ((p - 1) / 2) T _ _ (by omega) (by omega) rfl hT
  exact clean_of_core p hp hp7 (core_of_good hE rfl rfl (by omega) (good_root_of_L1 hE rfl rfl L hG htop))

end KC
