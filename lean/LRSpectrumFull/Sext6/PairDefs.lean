/-
# PairDefs (definitions for PairGrid): the 30-grid exclusion table for relative labelings (F2 pair-agreement, part 1).  [AK, 2026-11-24]

Matches `AJ_pairlift/gridlift.c` with D = 30.  A relative labeling is `c_m = eta_m * sigma(m)`, `m = 1..6`,
`sigma in S6`, `eta in {+-1}^6`, `eta_1 = +1` (global sign normalised away; the all-minus copy is the
same labeling via `(a,b) -> (a,-b)`).  In gridlift.c, `M_D(lambda) = max_{(a,b) != 0} min_m bd_D(a*m + b*c_m)`
and the labeling is excluded iff `7 * M_D > D`, i.e. (D = 30, integers) iff `M_30 >= 5`.
`Excl30 c` below says exactly `exists (a,b) with bd_30(a*m + b*c_m) >= 5 for all m`.  The grid point
`(0,0)` has `bd = 0 < 5` so it can never be a witness: the `(a,b) != (0,0)` clause of the C code is implicit.
Integers a, b are arbitrary (not only in `[0,30)`): bdist only sees the residue mod 30, so this is the
same predicate.

PROVED here (kernel `decide`, no native_decide, no sorry):
* `core_table`: every signed permutation `(c_1..c_6)` with `c_1 > 0`, distinct absolute values 1..6,
  other than the identity, is hit by one of 22 witnesses `(a,b)` (a pool found by greedy cover in C,
  `AK_pairlean/pool.c`; the pool is only a proof device, the statement is existential over all `(a,b)`);
* `pair_excl`: statement via `sigma : Perm (Fin 6)`, `eta : Fin 6 -> Z`;
* `identical_not_excl30`: the identical labeling is NOT excluded (negative control; all 900 grid points).
-/
import LRSpectrumFull.Sext6.Statement
import Mathlib.Tactic.FinCases
import Mathlib.Data.Int.ModEq

namespace LRSpectrumFull
namespace Sext6

/-- `m`-th slot condition on the 30-grid: `bd_30(a*m + b*c) >= 5`. -/
def slotGood (a b m c : ℤ) : Prop := 5 ≤ bdist 30 (a * m + b * c)

instance (a b m c : ℤ) : Decidable (slotGood a b m c) := by
  unfold slotGood; infer_instance

/-- The labeling `c` (`c m` = signed label at `q` of the runner with label `m+1` at `p`) is excluded on the
30-grid: a grid witness has all six distances `>= 5/30 = 1/6`. -/
def Excl30 (c : Fin 6 → ℤ) : Prop :=
  ∃ a b : ℤ, ∀ m : Fin 6, 5 ≤ bdist 30 (a * (((m : ℕ) : ℤ) + 1) + b * c m)

/-- 22 witnesses, greedy cover computed by `AK_pairlean/pool.c`. -/
def pool30 : List (ℤ × ℤ) :=
  [(3,1), (5,5), (5,10), (6,12), (1,4), (6,6), (1,27), (6,18), (5,15), (5,20), (11,2), (10,7), (1,5),
   (6,24), (6,8), (7,15), (10,15), (9,2), (2,15), (13,15), (1,6), (1,10)]

def good6 (w : ℤ × ℤ) (c1 c2 c3 c4 c5 c6 : ℤ) : Prop :=
  slotGood w.1 w.2 1 c1 ∧ slotGood w.1 w.2 2 c2 ∧ slotGood w.1 w.2 3 c3 ∧
  slotGood w.1 w.2 4 c4 ∧ slotGood w.1 w.2 5 c5 ∧ slotGood w.1 w.2 6 c6

instance (w : ℤ × ℤ) (c1 c2 c3 c4 c5 c6 : ℤ) : Decidable (good6 w c1 c2 c3 c4 c5 c6) := by
  unfold good6; infer_instance

def V12 : List ℤ := [1, 2, 3, 4, 5, 6, -1, -2, -3, -4, -5, -6]
def V6 : List ℤ := [1, 2, 3, 4, 5, 6]

/-- Layered decidable statement (keeps instance synthesis shallow). -/
def T6 (c1 c2 c3 c4 c5 : ℤ) : Prop :=
  ∀ c6 ∈ V12, c6.natAbs ≠ c1.natAbs → c6.natAbs ≠ c2.natAbs → c6.natAbs ≠ c3.natAbs →
    c6.natAbs ≠ c4.natAbs → c6.natAbs ≠ c5.natAbs →
    ¬ (c1 = 1 ∧ c2 = 2 ∧ c3 = 3 ∧ c4 = 4 ∧ c5 = 5 ∧ c6 = 6) →
    ∃ w ∈ pool30, good6 w c1 c2 c3 c4 c5 c6
instance (c1 c2 c3 c4 c5 : ℤ) : Decidable (T6 c1 c2 c3 c4 c5) := by unfold T6; infer_instance

def T5 (c1 c2 c3 c4 : ℤ) : Prop :=
  ∀ c5 ∈ V12, c5.natAbs ≠ c1.natAbs → c5.natAbs ≠ c2.natAbs → c5.natAbs ≠ c3.natAbs →
    c5.natAbs ≠ c4.natAbs → T6 c1 c2 c3 c4 c5
instance (c1 c2 c3 c4 : ℤ) : Decidable (T5 c1 c2 c3 c4) := by unfold T5; infer_instance

def T4 (c1 c2 c3 : ℤ) : Prop :=
  ∀ c4 ∈ V12, c4.natAbs ≠ c1.natAbs → c4.natAbs ≠ c2.natAbs → c4.natAbs ≠ c3.natAbs → T5 c1 c2 c3 c4
instance (c1 c2 c3 : ℤ) : Decidable (T4 c1 c2 c3) := by unfold T4; infer_instance

def T3 (c1 c2 : ℤ) : Prop :=
  ∀ c3 ∈ V12, c3.natAbs ≠ c1.natAbs → c3.natAbs ≠ c2.natAbs → T4 c1 c2 c3
instance (c1 c2 : ℤ) : Decidable (T3 c1 c2) := by unfold T3; infer_instance

def T2 (c1 : ℤ) : Prop := ∀ c2 ∈ V12, c2.natAbs ≠ c1.natAbs → T3 c1 c2
instance (c1 : ℤ) : Decidable (T2 c1) := by unfold T2; infer_instance

def T1 : Prop := ∀ c1 ∈ V6, T2 c1
instance : Decidable T1 := by unfold T1; infer_instance


end Sext6
end LRSpectrumFull
