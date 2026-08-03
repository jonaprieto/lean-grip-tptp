/-
Copyright (c) 2026 Jonathan Prieto-Cubides. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonathan Prieto-Cubides
-/

import TPTP

open TPTP

private def check (condition : Bool) (message : String) : IO Unit :=
  if condition then pure () else throw (IO.userError message)

private def documentSource : String :=
  "% a comment\n" ++
    "include('Axioms/foo.p', [a1, a2]).\n" ++
    "fof(ax, axiom, p(a)).\n" ++
    "tff(type, type, $int < $int, introduced(definition)).\n" ++
    "cnf(goal, conjecture, p(a) | ~q(a), inference(resolution, [status(thm)], [ax])).\n"

private def checkDocument : IO Unit := do
  let document ← match parseString documentSource with
    | .ok value => pure value
    | .error error => throw (IO.userError (error.pretty documentSource.toUTF8))
  check (document.items.size == 4) "document item count"
  match document.items[0]? with
  | some (Item.include value) =>
      check (value.path == .quoted "'Axioms/foo.p'") "quoted include path"
      check (value.selection == some "[a1, a2]") "include selection"
  | _ => throw (IO.userError "first item is not an include")
  match document.items[1]? with
  | some (Item.statement value) =>
      check (value.kind == .fof) "fof kind"
      check (value.role == .axiom) "axiom role"
      check (value.formula == "p(a)") "formula body"
  | _ => throw (IO.userError "second item is not a statement")
  match document.items[3]? with
  | some (Item.statement value) =>
      check (value.annotations == some "inference(resolution, [status(thm)], [ax])")
        "nested annotation split"
  | _ => throw (IO.userError "fourth item is not a statement")

private def checkFormula : IO Unit := do
  let source := "! [X] : (p(X) => q(X))"
  let formula ← match Formula.parseFormulaString source with
    | .ok value => pure value
    | .error error => throw (IO.userError (error.pretty source.toUTF8))
  match formula with
  | .forall variables (.implies (.atom "p" arguments) (.atom "q" result)) =>
      check (variables.size == 1 && variables[0]? == some "X") "quantifier variables"
      check (arguments.size == 1 && result.size == 1) "atom arguments"
      match Formula.Expr.toTPTP formula with
      | .ok rendered => check (rendered == "![X] : ((p(X) => q(X)))") "formula rendering"
      | .error message => throw (IO.userError message)
  | _ => throw (IO.userError "formula AST shape")

private def checkErrors : IO Unit := do
  match parseStatementString "fof(bad, axiom, p(" with
  | .ok _ => throw (IO.userError "malformed statement accepted")
  | .error error => check (error.pos > 0) "positioned parse error"
  match Formula.parseFormulaString "p(" with
  | .ok _ => throw (IO.userError "malformed formula accepted")
  | .error _ => pure ()

private def checkComments : IO Unit := do
  let source := "fof(line, axiom, p(a) % ) , ignored\n, inference(foo, [status(thm)]))."
  let block := "fof(block, axiom, p(a) /* ) , ignored */ , inference(foo, [status(thm)]))."
  for input in [source, block] do
    match parseStatementString input with
    | .ok statement =>
        check (statement.annotations == some "inference(foo, [status(thm)])")
          "comment-aware annotation split"
    | .error error => throw (IO.userError (error.pretty input.toUTF8))

def main : IO Unit := do
  checkDocument
  checkFormula
  checkErrors
  checkComments
  IO.println "TPTP tests: ok"
