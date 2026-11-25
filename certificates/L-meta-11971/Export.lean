import TwinReduction
open Simlowker.Twins11971.Graph in
def main (args : List String) : IO Unit := do
  let output ← IO.FS.Handle.mk (args.headD "core.cnf") .write
  output.putStrLn s!"p cnf 8000 {formula.length}"
  for clause in formula do
    let literals := clause.map fun v => (if v % 2 = 1 then "-" else "") ++ toString (v / 2)
    output.putStrLn ((String.intercalate " " literals) ++ " 0")
