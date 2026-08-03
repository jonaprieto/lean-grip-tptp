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
    "cnf(`Goal, conjecture, p(a) | ~q(a), inference(resolution, [status(thm)], [ax])).\n"

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
      check (value.name == .quoted "`Goal") "back-quoted statement name"
      check (value.annotations == some "inference(resolution, [status(thm)], [ax])")
        "nested annotation split"
  | _ => throw (IO.userError "fourth item is not a statement")
  match parseStatementString "fof(datatype, type-datatype, p(a))." with
  | .ok statement => check (statement.role == .other "type-datatype") "subrole"
  | .error error =>
      throw (IO.userError (error.pretty "fof(datatype, type-datatype, p(a)).".toUTF8))

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

private def checkFOF : IO Unit := do
  let source := "! [X] : (p(X) => q(X))"
  let formula ← match FOF.parseFormulaString source with
    | .ok value => pure value
    | .error error => throw (IO.userError (error.pretty source.toUTF8))
  let expected : FOF.Formula :=
    .forall #["X"] (.implies
      (.atom (.predicate { raw := "p" } #[.variable "X"]))
      (.atom (.predicate { raw := "q" } #[.variable "X"])))
  check (formula == expected) "complete FOF formula shape"
  match FOF.validate formula with
  | .ok () => pure ()
  | .error error => throw (IO.userError s!"bound FOF rejected: {error}")
  let rendered := formula.render
  check (rendered == "! [X] : ((p(X) => q(X)))") "canonical FOF rendering"
  match FOF.parseFormulaString rendered with
  | .ok reparsed => check (reparsed == formula) "FOF parse/render/parse"
  | .error error => throw (IO.userError (error.pretty rendered.toUTF8))
  for input in [
      "p & q & r", "p | q | r", "p <=> q", "p => q", "p <= q", "p <~> q",
      "p ~| q", "p ~& q", "a = b", "a != b", "p(\"x\")", "p('quoted')",
      "p(`X)", "p(-1, 1/2, 1.5, 1E2, 1.5E-2)", "$distinct(a, b)", "$$tool(a)",
      "$quotient_e(a, b)"
    ] do
    match FOF.parseFormulaString input with
    | .ok _ => pure ()
    | .error error =>
        throw (IO.userError (s!"FOF rejected `{input}`:\n{error.pretty input.toUTF8}"))
  let statement : Statement :=
    { kind := .fof, name := .bare "goal", role := .conjecture, formula := source }
  match FOF.parseStatementFormula statement with
  | .ok _ => pure ()
  | .error _ => throw (IO.userError "FOF statement formula rejected")
  let wrongKind : Statement := { statement with kind := .cnf }
  match FOF.parseStatementFormula wrongKind with
  | .error (.wrongKind .fof .cnf) => pure ()
  | _ => throw (IO.userError "FOF accepted a CNF statement")
  match FOF.parseFormulaString "p => q & r" with
  | .ok _ => throw (IO.userError "FOF accepted mixed unparenthesized connectives")
  | .error _ => pure ()
  match FOF.parseFormulaString "p(" with
  | .ok _ => throw (IO.userError "FOF accepted malformed term")
  | .error _ => pure ()
  for input in ["1", "\"object\""] do
    match FOF.parseFormulaString input with
    | .ok _ => throw (IO.userError s!"FOF accepted invalid proposition `{input}`")
    | .error _ => pure ()
  let unbound : FOF.Formula :=
    .atom (.predicate { raw := "p" } #[.variable "X"])
  match FOF.validate unbound with
  | .error (.unboundVariable "X") => pure ()
  | _ => throw (IO.userError "FOF accepted an unbound variable")
  let duplicate : FOF.Formula := .forall #["X", "X"] .truth
  match FOF.validate duplicate with
  | .error (.duplicateBinder "X") => pure ()
  | _ => throw (IO.userError "FOF accepted a duplicate binder")
  let empty : FOF.Formula := .forall #[] .truth
  match FOF.validate empty with
  | .error .emptyBinder => pure ()
  | _ => throw (IO.userError "FOF accepted an empty binder")
  let unknown : FOF.Formula := .atom (.predicate { raw := "$mystery" } #[])
  match FOF.validate unknown with
  | .error (.unknownDefinedSymbol "$mystery") => pure ()
  | _ => throw (IO.userError "FOF accepted an unknown defined symbol")
  let missingArguments : FOF.Formula := .atom (.predicate { raw := "$less" } #[])
  match FOF.validate missingArguments with
  | .error (.invalidDefinedArity "$less" 0) => pure ()
  | _ => throw (IO.userError "FOF accepted a defined predicate without arguments")

private def checkCNF : IO Unit := do
  let source := "(p(a) | ~q(a) | r(a) != s(a))"
  let clause ← match CNF.parseFormulaString source with
    | .ok value => pure value
    | .error error => throw (IO.userError (error.pretty source.toUTF8))
  check (clause.literals.size == 3) "CNF literal count"
  for input in ["p(a) | ~(q(a)) | r(a) != s(a)", "((p(a) | ~q(a)) )"] do
    match CNF.parseFormulaString input with
    | .ok _ => pure ()
    | .error error =>
        throw (IO.userError (s!"CNF regression `{input}`:\n{error.pretty input.toUTF8}"))
  match clause.literals[1]? with
  | some (CNF.Literal.negative (FirstOrder.Atom.predicate symbol _)) =>
      check (symbol.raw == "q") "CNF negative literal"
  | _ => throw (IO.userError "CNF negative literal shape")
  match clause.literals[2]? with
  | some (CNF.Literal.positive (FirstOrder.Atom.inequality _ _)) => pure ()
  | _ => throw (IO.userError "CNF inequality literal shape")
  let rendered := clause.render
  check (rendered == "p(a) | ~(q(a)) | r(a) != s(a)") "canonical CNF rendering"
  match CNF.parseFormulaString rendered with
  | .ok reparsed => check (reparsed == clause) "CNF parse/render/parse"
  | .error error => throw (IO.userError (error.pretty rendered.toUTF8))
  let empty ← match CNF.parseFormulaString "$false" with
    | .ok value => pure value
    | .error error => throw (IO.userError (error.pretty "$false".toUTF8))
  check empty.literals.isEmpty "CNF empty clause"
  check (empty.render == "$false") "CNF empty clause rendering"
  for input in [
      "$true", "$distinct(a, b)", "$$system(a)", "1 != 2", "\"a\" != \"b\"",
      "~($less(a, b))"
    ] do
    match CNF.parseFormulaString input with
    | .ok _ => pure ()
    | .error error =>
        throw (IO.userError (s!"CNF rejected `{input}`:\n{error.pretty input.toUTF8}"))
  let statement : Statement :=
    { kind := .cnf, name := .bare "goal", role := .conjecture, formula := source }
  match CNF.parseStatementFormula statement with
  | .ok value => check (value == clause) "CNF statement formula"
  | .error _ => throw (IO.userError "CNF statement formula rejected")
  for input in ["p => q", "![X] : p(X)", "()"] do
    match CNF.parseFormulaString input with
    | .ok _ => throw (IO.userError s!"CNF accepted `{input}`")
    | .error _ => pure ()
  for input in ["p & q | r", "p | q & r", "p => q => r", "p |", "~ ~p"] do
    match CNF.parseFormulaString input with
    | .ok _ => throw (IO.userError s!"CNF accepted `{input}`")
    | .error _ => pure ()

def main : IO Unit := do
  checkDocument
  checkFormula
  checkErrors
  checkComments
  checkFOF
  checkCNF
  IO.println "TPTP tests: ok"
