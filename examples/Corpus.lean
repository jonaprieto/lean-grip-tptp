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

private def checkTypedFile (path : String) : IO (Nat × Nat) := do
  let source ← IO.FS.readFile path
  let document ← match parseString source with
    | .ok value => pure value
    | .error error => throw (IO.userError s!"{path}:\n{error.pretty source.toUTF8}")
  let mut fof := 0
  let mut cnf := 0
  for item in document.items do
    match item with
    | .include _ => pure ()
    | .statement statement =>
        match statement.kind with
        | .fof =>
            match FOF.parseStatementFormula statement with
            | .ok _ => fof := fof + 1
            | .error error =>
                throw (IO.userError s!"{path}: {formulaError statement error}")
        | .cnf =>
            match CNF.parseStatementFormula statement with
            | .ok _ => cnf := cnf + 1
            | .error error =>
                throw (IO.userError s!"{path}: {formulaError statement error}")
        | _ => pure ()
  pure (fof, cnf)

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
    for path in paths do
      let counts ← checkTypedFile path
      fof := fof + counts.1
      cnf := cnf + counts.2
    IO.println s!"TPTP typed corpus: {paths.length} files, {fof} FOF, {cnf} CNF"
  else
    for path in paths do
      checkFile path
    IO.println s!"TPTP corpus: {paths.length} files parsed"
