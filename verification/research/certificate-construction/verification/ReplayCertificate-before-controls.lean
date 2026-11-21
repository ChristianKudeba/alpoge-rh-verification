import Lean
import Lean.Replay

open Lean

/-- Collect proof terms and all of their dependencies, including entire mutual
inductive blocks and their constructors needed by `Environment.replay`. -/
partial def collect (env : Environment) (todo : List Name)
    (seen : Std.HashMap Name ConstantInfo := {}) : Except String (Std.HashMap Name ConstantInfo) := do
  match todo with
  | [] => return seen
  | n :: rest =>
    if seen.contains n then return ← collect env rest seen
    let some ci := env.find? n | throw s!"Missing declaration {n}"
    if ci.isUnsafe || ci.isPartial then throw s!"Unsafe or partial proof dependency {n}"
    if let .axiomInfo _ := ci then
      unless n == `propext || n == `Classical.choice || n == `Quot.sound do
        throw s!"Unapproved axiom {n}"
    let extra := match ci with
      | .inductInfo i => i.all ++ i.ctors
      | .ctorInfo i => [i.induct]
      | .recInfo i => i.all
      | _ => []
    collect env (extra ++ ci.getUsedConstantsAsSet.toList ++ rest) (seen.insert n ci)

def main (args : List String) : IO UInt32 := do
  match args with
  | module :: targets =>
    if targets.isEmpty then throw <| IO.userError "Expected at least one fully qualified target"
    initSearchPath (← findSysroot)
    let env ← importModules #[{module := module.toName}] {} (loadExts := false)
    let names := targets.map String.toName
    let constants ← match collect env names with
      | .ok cs => pure cs
      | .error message => throw <| IO.userError message
    IO.println s!"Replaying {constants.size} declarations for {targets} into an empty kernel environment"
    let empty ← mkEmptyEnvironment
    let checked ← empty.replay constants
    for n in names do
      unless (checked.toKernelEnv.find? n).isSome do
        throw <| IO.userError s!"Missing target after replay: {n}"
    let axioms := constants.toList.filterMap fun (n, ci) =>
      if ci matches .axiomInfo _ then some n else none
    IO.println s!"REPLAY PASSED; axioms: {axioms}"
    return 0
  | _ =>
    IO.eprintln "Usage: lean --run ReplayCertificate.lean MODULE TARGET..."
    return 2
