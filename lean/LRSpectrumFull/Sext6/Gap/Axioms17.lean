import LRSpectrumFull.Sext6.Gap.RobustK13Cheb
import Lean

/-!
# Axioms17: audit of the Chebyshev-threshold Theorem S  [2026-11-25]

`#print axioms`, `#check`, and the `DusartPi` dependency closure for `RobustK13Cheb` (positive control:
`ML_ge_S_table` reaches `DusartPi`).

This module proves nothing: it prints `#print axioms` (and `#check`) for the declarations it names, and is imported by `Sext6.Gap.All`.
-/

open Lean Elab Command
open LRSpectrumFull.Sext6.Gap

partial def depClosure17 (env : Environment) (todo : Array Name) (seen : NameSet) : NameSet :=
  if todo.isEmpty then seen else
  let n := todo.back!
  let todo := todo.pop
  if seen.contains n then depClosure17 env todo seen else
  let seen := seen.insert n
  match env.find? n with
  | none => depClosure17 env todo seen
  | some ci =>
    let cs := ci.type.getUsedConstants ++
      (match ci.value? with | some v => v.getUsedConstants | none => #[])
    depClosure17 env (todo ++ cs) seen

def checkNoDep17 (target : Name) (heads : List Name) : CommandElabM Unit := do
  let env ← getEnv
  for h in heads do
    let cl := depClosure17 env #[h] {}
    logInfo m!"{h}: {cl.size} constants reachable; {target} reachable: {cl.contains target}"

#print axioms copWin_cheb
#print axioms theoremS_cheb
#print axioms cor_a_cheb
#print axioms chebCond_pow
#print axioms copWin_pow
#print axioms copWin_cheb_table
#print axioms theoremS_cheb_table
#print axioms cor_a_cheb_table
#print axioms mcheb_le_ncheb

#check @copWin_cheb
#check @theoremS_cheb
#check @copWin_pow
#check @copWin_cheb_table
#check @theoremS_cheb_table
#print ChebCond
#print MCheb

run_cmd (checkNoDep17 ``DusartPi [``copWin_cheb, ``theoremS_cheb, ``cor_a_cheb, ``copWin_pow, ``copWin_cheb_table, ``theoremS_cheb_table, ``cor_a_cheb_table, ``ML_ge_S_table])
