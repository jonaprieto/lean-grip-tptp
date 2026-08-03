/-
Copyright (c) 2026 Jonathan Prieto-Cubides. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonathan Prieto-Cubides
-/

import TPTP

/-!
# FOF/CNF conformance matrix

The cases mirror the supported productions in `notes/TPTP-Syntax-BNF.md`. Each positive
case exercises a production family; each negative case is a close malformed form that must
not be accepted by the typed parser.
-/

open TPTP

private def isOk {α β : Type} : Except α β → Bool
  | .ok _ => true
  | .error _ => false

private def checkFOF (accepted : Bool) (label source : String) : IO Unit := do
  let result := FOF.parseFormulaString source
  if (isOk result == accepted) then
    match result with
    | .ok formula =>
        match FOF.validate formula with
        | .ok () => pure ()
        | .error error => throw (IO.userError s!"FOF validation failed for {label}: {error}")
    | .error _ => pure ()
  else
    match result with
    | .ok _ => throw (IO.userError s!"FOF unexpectedly accepted {label}: `{source}`")
    | .error error =>
        throw (IO.userError s!"FOF unexpectedly rejected {label}: {error.pretty source.toUTF8}")

private def checkCNF (accepted : Bool) (label source : String) : IO Unit := do
  let result := CNF.parseFormulaString source
  if (isOk result == accepted) then
    match result with
    | .ok clause =>
        match CNF.validate clause with
        | .ok () => pure ()
        | .error error => throw (IO.userError s!"CNF validation failed for {label}: {error}")
    | .error _ => pure ()
  else
    match result with
    | .ok _ => throw (IO.userError s!"CNF unexpectedly accepted {label}: `{source}`")
    | .error error =>
        throw (IO.userError s!"CNF unexpectedly rejected {label}: {error.pretty source.toUTF8}")

private def fofAccepted : List (String × String) := [
  ("plain proposition", "p"),
  ("quoted proposition", "'quoted name'"),
  ("escaped quoted name", "p('quoted \\\\ name')"),
  ("back-quoted proposition", "`X"),
  ("predicate", "p(a, f(b))"),
  ("system predicate", "$$system(a)"),
  ("equality", "f(a) = g(b)"),
  ("inequality", "f(a) != g(b)"),
  ("defined proposition", "$true"),
  ("defined predicate", "$distinct(a, b)"),
  ("defined comparison", "$less(a, b)"),
  ("defined integer test", "$is_int(a)"),
  ("defined term", "$quotient_e(a, b) = c"),
  ("distinct object", "p(\"object\")"),
  ("signed integer", "p(-12, +3)"),
  ("signed zero", "p(-0, +0)"),
  ("rational", "p(1/2)"),
  ("real fraction", "p(1.25)"),
  ("real exponent", "p(-1.25E+2)"),
  ("negation", "~p"),
  ("universal quantifier", "![X] : p(X)"),
  ("existential quantifier", "?[X, Y] : p(X, Y)"),
  ("and", "p & q & r"),
  ("or", "p | q | r"),
  ("iff", "p <=> q"),
  ("implies", "p => q"),
  ("implied by", "p <= q"),
  ("xor", "p <~> q"),
  ("nor", "p ~| q"),
  ("nand", "p ~& q"),
  ("nested formula", "(p & q) => (~r | s)"),
  ("comments and whitespace", "! /* bind */ [ X ] : p( X ) % tail\n")
]

private def fofRejected : List (String × String) := [
  ("empty input", ""),
  ("uppercase proposition", "P"),
  ("underscore proposition", "_"),
  ("empty single-quoted name", "p('')"),
  ("numeric proposition", "1"),
  ("distinct-object proposition", "\"object\""),
  ("empty argument list", "p()"),
  ("trailing argument comma", "p(a,)"),
  ("missing binder colon", "![X] p(X)"),
  ("empty binder", "![] : p"),
  ("missing close parenthesis", "(p"),
  ("chained non-associative connective", "p => q => r"),
  ("mixed associative connectives", "p & q | r"),
  ("mixed associative connectives reversed", "p | q & r"),
  ("trailing connective", "p |"),
  ("malformed exponent", "p(1.0E)"),
  ("malformed exponent marker", "p(1.0e)"),
  ("malformed rational", "p(1/0)"),
  ("leading zero integer", "p(00)"),
  ("unterminated quote", "p('unterminated)"),
  ("invalid quote escape", "p('bad\\escape')")
]

private def cnfAccepted : List (String × String) := [
  ("positive literal", "p"),
  ("negative literal", "~p"),
  ("parenthesized negative literal", "~(p(a))"),
  ("equality literal", "a = b"),
  ("inequality literal", "a != b"),
  ("disjunction", "p | ~q | r"),
  ("nested clause", "((p | ~q))"),
  ("defined proposition", "$true"),
  ("defined predicate", "$distinct(a, b)"),
  ("system predicate", "$$system(a)"),
  ("numeric terms", "1 != 2"),
  ("distinct objects", "\"a\" != \"b\"")
]

private def cnfRejected : List (String × String) := [
  ("empty input", ""),
  ("empty clause spelling", "()"),
  ("empty argument list", "p()"),
  ("quantifier", "![X] : p(X)"),
  ("binary connective", "p => q"),
  ("conjunction", "p & q"),
  ("trailing disjunction", "p |"),
  ("double negation marker", "~ ~p"),
  ("trailing argument comma", "p(a,)")
]

private def checkValidation : IO Unit := do
  let valid := FOF.Formula.atom
    (.predicate { raw := "$less" } #[.constant { raw := "a" }, .constant { raw := "b" }])
  match FOF.validate valid with
  | .error error => throw (IO.userError s!"valid defined predicate rejected: {error}")
  | .ok () => pure ()
  let unknown := FOF.Formula.atom (.predicate { raw := "$unknown" } #[])
  match FOF.validate unknown with
  | .error (.unknownDefinedSymbol "$unknown") => pure ()
  | .error error => throw (IO.userError s!"wrong unknown-symbol error: {error}")
  | .ok () => throw (IO.userError "unknown defined symbol accepted")
  let missing := FOF.Formula.atom (.predicate { raw := "$less" } #[])
  match FOF.validate missing with
  | .error (.invalidDefinedArity "$less" 0) => pure ()
  | .error error => throw (IO.userError s!"wrong defined-use error: {error}")
  | .ok () => throw (IO.userError "defined predicate without arguments accepted")
  let badClause : CNF.Clause :=
    { literals := #[.positive (.predicate { raw := "$unknown" } #[])] }
  match CNF.validate badClause with
  | .error (.unknownDefinedSymbol "$unknown") => pure ()
  | .error error => throw (IO.userError s!"wrong CNF symbol error: {error}")
  | .ok () => throw (IO.userError "CNF unknown defined symbol accepted")
  let badApplication := FOF.Formula.atom
    (.predicate { raw := "p" } #[.function { raw := "1" } #[]])
  match FOF.validate badApplication with
  | .error (.invalidTermApplication "1") => pure ()
  | .error error => throw (IO.userError s!"wrong term-application error: {error}")
  | .ok () => throw (IO.userError "numeric term application accepted")
  match FOF.parseFormulaString "p(1(a))" with
  | .ok formula =>
      match FOF.validate formula with
      | .error (.invalidTermApplication "1") => pure ()
      | .error error => throw (IO.userError s!"wrong parsed term-application error: {error}")
      | .ok () => throw (IO.userError "parsed numeric term application accepted")
  | .error error => throw (IO.userError (error.pretty "p(1(a))".toUTF8))

def main : IO Unit := do
  for (label, source) in fofAccepted do
    checkFOF true label source
  for (label, source) in fofRejected do
    checkFOF false label source
  for (label, source) in cnfAccepted do
    checkCNF true label source
  for (label, source) in cnfRejected do
    checkCNF false label source
  checkValidation
  IO.println (s!"TPTP conformance: {fofAccepted.length} FOF accepted, " ++
    s!"{fofRejected.length} FOF rejected, {cnfAccepted.length} CNF accepted, " ++
    s!"{cnfRejected.length} CNF rejected")
