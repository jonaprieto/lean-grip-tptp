/-
Copyright (c) 2026 Jonathan Prieto-Cubides. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonathan Prieto-Cubides
-/

import TPTP

open TPTP

private def checkFile (path : String) : IO Unit := do
  let source ← IO.FS.readFile path
  match parseString source with
  | .ok _ => pure ()
  | .error error =>
      throw (IO.userError s!"{path}:\n{error.pretty source.toUTF8}")

private def formulaError (statement : Statement) (error : FormulaError) : String :=
  match error with
  | .syntax error => error.pretty statement.formula.toUTF8
  | .wrongKind expected actual => s!"expected {expected}, found {actual}"

private def checkTypedFile (path : String) : IO (Nat × Nat × Nat) := do
  let source ← IO.FS.readFile path
  let document ← match parseString source with
    | .ok value => pure value
    | .error error => throw (IO.userError s!"{path}:\n{error.pretty source.toUTF8}")
  let mut fof := 0
  let mut cnf := 0
  let mut tff := 0
  let mut tffBodies : Array TFF.Body := #[]
  for item in document.items do
    match item with
    | .include _ => pure ()
    | .statement statement =>
        match statement.kind with
        | .fof =>
            match FOF.parseStatementFormula statement with
            | .ok formula =>
                match FOF.validate formula with
                | .ok () => fof := fof + 1
                | .error error =>
                    throw (IO.userError s!"{path}: {statement.name}: {error}")
            | .error error =>
                throw (IO.userError s!"{path}: {formulaError statement error}")
        | .cnf =>
            match CNF.parseStatementFormula statement with
            | .ok clause =>
                match CNF.validate clause with
                | .ok () => cnf := cnf + 1
                | .error error =>
                    throw (IO.userError s!"{path}: {statement.name}: {error}")
            | .error error =>
                throw (IO.userError s!"{path}: {formulaError statement error}")
        | .tff =>
            match TFF.parseStatementBody statement with
            | .ok body =>
                tffBodies := tffBodies.push body
                tff := tff + 1
            | .error (.syntax error) =>
                throw (IO.userError
                  s!"{path}: {statement.name}: {error.pretty statement.formula.toUTF8}")
            | .error (.wrongKind expected actual) =>
                throw (IO.userError s!"{path}: expected {expected}, found {actual}")
        | _ => pure ()
  match TFF.validateDocument tffBodies with
  | .ok _ => pure (fof, cnf, tff)
  | .error error => throw (IO.userError s!"{path}: TFF validation: {error}")

def main (arguments : List String) : IO Unit := do
  let arguments := match arguments with
    | "--" :: rest => rest
    | rest => rest
  let typed := arguments.any (· == "--typed")
  let paths := arguments.filter (· != "--typed")
  if paths.isEmpty then
    throw (IO.userError "usage: lake exe corpus -- [--typed] FILE...")
  if typed then
    let mut fof := 0
    let mut cnf := 0
    let mut tff := 0
    for path in paths do
      let counts ← checkTypedFile path
      fof := fof + counts.1
      cnf := cnf + counts.2.1
      tff := tff + counts.2.2
    IO.println s!"TPTP typed corpus: {paths.length} files, {fof} FOF, {cnf} CNF, {tff} TFF"
  else
    for path in paths do
      checkFile path
    IO.println s!"TPTP corpus: {paths.length} files parsed"
