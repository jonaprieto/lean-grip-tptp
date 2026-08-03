/-
Copyright (c) 2026 Jonathan Prieto-Cubides. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonathan Prieto-Cubides
-/

import TPTP.CNF
import TPTP.FirstOrder.Parse
import TPTP.Syntax

/-!
# TPTP.CNF.Parse: total clause normal form parser

CNF is a disjunction of literals. Variables are implicitly universally quantified by the
TPTP language; this module only parses the clause syntax.
-/

namespace TPTP.CNF

open Grip GParser
open TPTP.FirstOrder.Parser

private def positiveLiteral : P Literal :=
  Literal.positive <$> FirstOrder.Parser.atom

private def parenthesizedAtom : P FirstOrder.Atom :=
  GParser.ch '(' *> trivia *> FirstOrder.Parser.atom <* GParser.ch ')' <* trivia

private def negativeLiteral : P Literal := gdo
  let ignoredMarker ← GParser.ch '~'
  let ignoredTrivia ← trivia
  let value ← GParser.chooseG parenthesizedAtom [FirstOrder.Parser.atom]
  return .negative value
  grade_by by decide

private def literal : P Literal :=
  GParser.dispatch fun byte =>
    if byte == Ascii.code '~' then negativeLiteral
    else positiveLiteral

private def separator : P Unit :=
  (fun _ => ()) <$> (GParser.ch '|' <* trivia)

private def normalize (clause : Clause) : Clause :=
  match clause.literals.toList with
  | [Literal.positive (.predicate symbol arguments)] =>
      if symbol.raw == "$false" && arguments.isEmpty then
        { literals := #[] }
      else
        clause
  | _ => clause

private def clauseParser : P Clause :=
  GParser.fix fun recursive =>
    let parenthesized : P Clause :=
      GParser.ch '(' *> trivia *> recursive <* GParser.ch ')' <* trivia
    let disjunction : P Clause :=
      GParser.map (fun (first, rest) => normalize { literals := (first :: rest).toArray })
        (GParser.map2 Prod.mk literal (GParser.many (separator *> literal)))
    GParser.chooseG parenthesized [disjunction]

/-- Parse a complete CNF clause from bytes. -/
def parseFormula (source : ByteArray) : Except Grip.ParseError Clause :=
  (trivia *> clauseParser <* trivia <* GParser.eof).parse source

/-- Parse a complete CNF clause from UTF-8 text. -/
def parseFormulaString (source : String) : Except Grip.ParseError Clause :=
  parseFormula source.toUTF8

def parseStatementFormula (statement : TPTP.Statement) : Except TPTP.FormulaError Clause :=
  if statement.kind != .cnf then
    .error (.wrongKind .cnf statement.kind)
  else
    match parseFormulaString statement.formula with
    | .ok clause => .ok clause
    | .error error => .error (.syntax error)

end TPTP.CNF
