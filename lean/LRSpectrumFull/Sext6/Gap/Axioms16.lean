import LRSpectrumFull.Sext6.Gap.FS1Final
import Lean

/-!
# Axioms16: audit of Theorem FS1 without `DusartPi`  [2026-11-25]

1. `#print axioms` of `FS1_unconditional`, `FS1_shape_unconditional`, with the old Dusart-hypothesis versions
   `FS1_all`, `FS1_shape_all` as positive controls (these take `DusartPi` as an argument).
2. `#check` of the signatures (no `DusartPi` argument in the new ones).
3. Dependency closure through types and values: `DusartPi` is NOT reachable from the new theorems; it IS reachable
   from `FS1_all` (positive control).

This module proves nothing: it prints `#print axioms` (and `#check`) for the declarations it names, and is imported by `Sext6.Gap.All`.
-/

open Lean Elab Command
open LRSpectrumFull.Sext6.Gap

partial def depClosure16 (env : Environment) (todo : Array Name) (seen : NameSet) : NameSet :=
  if todo.isEmpty then seen else
  let n := todo.back!
  let todo := todo.pop
  if seen.contains n then depClosure16 env todo seen else
  let seen := seen.insert n
  match env.find? n with
  | none => depClosure16 env todo seen
  | some ci =>
    let cs := ci.type.getUsedConstants ++
      (match ci.value? with | some v => v.getUsedConstants | none => #[])
    depClosure16 env (todo ++ cs) seen

def checkNoDep16 (target : Name) (heads : List Name) : CommandElabM Unit := do
  let env ← getEnv
  for h in heads do
    let cl := depClosure16 env #[h] {}
    logInfo m!"{h}: {cl.size} constants reachable; {target} reachable: {cl.contains target}"

#print axioms FS1_unconditional
#print axioms FS1_shape_unconditional
#print axioms FS1_all
#print axioms FS1_shape_all

#check @FS1_unconditional
#check @FS1_shape_unconditional
#check @FS1_all

run_cmd (checkNoDep16 ``DusartPi [``FS1_unconditional, ``FS1_shape_unconditional, ``FS1_all, ``FS1_shape_all])
