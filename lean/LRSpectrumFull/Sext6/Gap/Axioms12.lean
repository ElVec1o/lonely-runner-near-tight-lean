import LRSpectrumFull.Sext6.Gap.FinalCore
import Lean

/-!
# Axioms12: audit of the hypothesis-free headline theorems  [2026-11-25]

1. `#print axioms` of every theorem of `FinalCore` and of the new block theorems.
2. `#check` of the headline signatures: none has a `DusartPi` argument.
3. A dependency-closure check: the set of constants reachable from each headline theorem (types and values, through
   Mathlib) does NOT contain `DusartPi`; positive control: the closure of the Dusart-hypothesis theorem `ML_ge_S_table`
   does contain it.

This module proves nothing: it prints `#print axioms` (and `#check`) for the declarations it names, and is imported by `Sext6.Gap.All`.
-/

open Lean Elab Command
open LRSpectrumFull.Sext6.Gap

partial def depClosure (env : Environment) (todo : Array Name) (seen : NameSet) : NameSet :=
  if todo.isEmpty then seen else
  let n := todo.back!
  let todo := todo.pop
  if seen.contains n then depClosure env todo seen else
  let seen := seen.insert n
  match env.find? n with
  | none => depClosure env todo seen
  | some ci =>
    let cs := ci.type.getUsedConstants ++
      (match ci.value? with | some v => v.getUsedConstants | none => #[])
    depClosure env (todo ++ cs) seen

def checkNoDep (target : Name) (heads : List Name) : CommandElabM Unit := do
  let env ← getEnv
  for h in heads do
    let cl := depClosure env #[h] {}
    logInfo m!"{h}: {cl.size} constants reachable; {target} reachable: {cl.contains target}"

#print axioms copWinT_of_copWinC
#print axioms copWinC_of_copWinT
#print axioms copWinC_iff
#print axioms copWinT_of_cheb_N
#print axioms copWinT_of_cheb
#print axioms copWinHypC
#print axioms chebG_succ
#print axioms chebG_le_pow
#print axioms cheb_hyp_ge
#print axioms copWin_hi
#print axioms primeWinF4_mid
#print axioms primeWinF5_mid
#print axioms primeWinF6_mid
#print axioms primeWinF7_mid
#print axioms primeWinF8_mid
#print axioms primeWinF9_mid
#print axioms primeWinF10_mid
#print axioms primeWinF11_mid
#print axioms primeWinF12_mid
#print axioms copWin_table
#print axioms copWin_large
#print axioms copWin_unconditional
#print axioms ML_ge_S_unconditional
#print axioms cor_a_unconditional
#print axioms ML_ge_robust_unconditional
#print axioms theoremS_unconditional
#print axioms cor_a_robust_unconditional
#print axioms OE_low_of_copWin
#print axioms OE_low_unconditional
#print axioms theoremW_unconditional

#check @copWin_table
#check @copWin_large
#check @copWin_unconditional
#check @ML_ge_S_unconditional
#check @cor_a_unconditional
#check @ML_ge_robust_unconditional
#check @theoremS_unconditional
#check @cor_a_robust_unconditional
#check @OE_low_unconditional
#check @theoremW_unconditional
#print NCheb

run_cmd (checkNoDep ``DusartPi [``copWin_table, ``copWin_large, ``copWin_unconditional, ``ML_ge_S_unconditional, ``cor_a_unconditional, ``ML_ge_robust_unconditional, ``theoremS_unconditional, ``cor_a_robust_unconditional, ``OE_low_unconditional, ``theoremW_unconditional, ``ML_ge_S_table])
