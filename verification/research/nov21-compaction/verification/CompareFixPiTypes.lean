import Lean
open Lean

def findConstant (path : System.FilePath) (name : Name) : IO ConstantInfo := do
  let (data, _) ← readModuleData path
  match data.constants.find? (·.name == name) with
  | some c => return c
  | none => throw <| IO.userError s!"Missing constant {name} in {path}"

def main (args : List String) : IO UInt32 := do
  match args with
  | [original, candidate, output] =>
    let n := `UpperTheory.Reformulated.B.Gr34.mem_UC
    let a ← findConstant original n
    let b ← findConstant candidate n
    unless a.levelParams == b.levelParams do
      throw <| IO.userError "Universe parameter list changed"
    unless a.type == b.type do
      IO.FS.writeFile (output ++ ".original") (reprStr a.type)
      IO.FS.writeFile (output ++ ".candidate") (reprStr b.type)
      throw <| IO.userError "Kernel type expressions differ"
    IO.FS.writeFile output (reprStr a.type)
    IO.println s!"EXACT TYPE AST MATCH; target={n}; hash64={hash a.type}; universeParams={a.levelParams}"
    return 0
  | _ => throw <| IO.userError "Expected ORIGINAL_OLEAN CANDIDATE_OLEAN TYPE_AST_OUTPUT"
