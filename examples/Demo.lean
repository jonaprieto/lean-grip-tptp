/-
Copyright (c) 2026 Jonathan Prieto-Cubides. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonathan Prieto-Cubides
-/

import TPTP

open TPTP

private def source : String :=
  "include('Axioms/foo.p').\n" ++
    "fof(goal, conjecture, ! [X] : (p(X) => q(X)),\n" ++
    "  inference(resolution, [status(thm)], [foo])).\n"

def main : IO Unit := do
  IO.println "TPTP/TSTP parser demo"
  match parseString source with
  | .ok document =>
      IO.println s!"items: {document.items.size}"
      IO.println (Document.render document)
      match document.items[1]? with
      | some (Item.statement statement) =>
          match statement.parseFormula with
          | .ok formula =>
              match Formula.Expr.toTPTP formula with
              | .ok rendered => IO.println s!"formula: {rendered}"
              | .error message => IO.println s!"render error: {message}"
          | .error error => IO.println (error.pretty statement.formula.toUTF8)
      | _ => pure ()
  | .error error => IO.println (error.pretty source.toUTF8)
