import LRSpectrumFull.Sext6.Gap.RobustK13Tab
import Lean

/-!
# Axioms18: audit of Theorem S from the exact sieve threshold, `13 ≤ k`  [2026-11-25]

`#print axioms`, `#check`, `#print NstarX`, and the `DusartPi` dependency closure of `RobustK13Tab`.

This module proves nothing: it prints `#print axioms` (and `#check`) for the declarations it names, and is imported by `Sext6.Gap.All`.
-/

open Lean Elab Command
open LRSpectrumFull.Sext6.Gap

partial def depClosure18 (env : Environment) (todo : Array Name) (seen : NameSet) : NameSet :=
  if todo.isEmpty then seen else
  let n := todo.back!
  let todo := todo.pop
  if seen.contains n then depClosure18 env todo seen else
  let seen := seen.insert n
  match env.find? n with
  | none => depClosure18 env todo seen
  | some ci =>
    let cs := ci.type.getUsedConstants ++
      (match ci.value? with | some v => v.getUsedConstants | none => #[])
    depClosure18 env (todo ++ cs) seen

def checkNoDep18 (target : Name) (heads : List Name) : CommandElabM Unit := do
  let env ← getEnv
  for h in heads do
    let cl := depClosure18 env #[h] {}
    logInfo m!"{h}: {cl.size} constants reachable; {target} reachable: {cl.contains target}"

#print axioms copWin_ext
#print axioms copWin_all
#print axioms theoremS_all
#print axioms cor_a_all

#check @copWin_ext
#check @copWin_all
#check @theoremS_all
#print NstarX
#print NstarAll

run_cmd (checkNoDep18 ``DusartPi [``copWin_ext, ``copWin_all, ``theoremS_all, ``cor_a_all, ``ML_ge_S_table])
