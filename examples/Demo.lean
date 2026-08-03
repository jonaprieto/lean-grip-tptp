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
    "  inference(resolution, [status(thm)], [foo])).\n" ++
    "cnf(clause, axiom, (p(a) | ~(q(a)) | r(a) != s(a))).\n" ++
    "tff(nat_type, type, nat: $tType).\n" ++
    "tff(zero_type, type, zero: nat).\n" ++
    "tff(add_type, type, add: (nat * nat) > nat).\n" ++
    "tff(goal_tff, conjecture, ! [X:nat] : add(X,zero) = X).\n"

private def printStatement (statement : Statement) : IO Unit := do
  IO.println s!"{statement.kind} {statement.name}: {statement.formula}"
  match statement.kind with
  | .fof =>
      match FOF.parseStatementFormula statement with
      | .ok formula =>
          IO.println s!"  FOF: {formula.render}"
          match FOF.validate formula with
          | .ok () => IO.println "  validation: ok"
          | .error error => IO.println s!"  validation: {error}"
      | .error (.syntax error) => IO.println (error.pretty statement.formula.toUTF8)
      | .error (.wrongKind expected actual) => IO.println s!"  kind error: {expected} vs {actual}"
  | .cnf =>
      match CNF.parseStatementFormula statement with
      | .ok clause => IO.println s!"  CNF: {clause.render}"
      | .error (.syntax error) => IO.println (error.pretty statement.formula.toUTF8)
      | .error (.wrongKind expected actual) => IO.println s!"  kind error: {expected} vs {actual}"
  | .tff =>
      match TFF.parseStatementBody statement with
      | .ok (.declaration declaration) => IO.println s!"  TFF declaration: {declaration.render}"
      | .ok (.formula formula) => IO.println s!"  TFF formula: {formula.render}"
      | .error (.syntax error) => IO.println (error.pretty statement.formula.toUTF8)
      | .error (.wrongKind expected actual) => IO.println s!"  kind error: {expected} vs {actual}"
  | _ => IO.println "  typed parser: not enabled for this kind"

def main : IO Unit := do
  IO.println "TPTP/TSTP parser demo"
  match parseString source with
  | .ok document =>
      IO.println s!"items: {document.items.size}"
      let mut tffBodies : Array TFF.Body := #[]
      for item in document.items do
        match item with
        | .include value => IO.println s!"include: {value.path}"
        | .statement statement =>
            printStatement statement
            if statement.kind == .tff then
              match TFF.parseStatementBody statement with
              | .ok body => tffBodies := tffBodies.push body
              | .error _ => pure ()
      match TFF.validateDocument tffBodies with
      | .ok signature =>
          IO.println s!"TFF validation: ok ({signature.declarations.size} declarations)"
      | .error error => IO.println s!"TFF validation: {error}"
  | .error error => IO.println (error.pretty source.toUTF8)
