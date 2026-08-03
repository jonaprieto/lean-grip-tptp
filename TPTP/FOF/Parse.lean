/-
Copyright (c) 2026 Jonathan Prieto-Cubides. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonathan Prieto-Cubides
-/

import TPTP.FOF
import TPTP.FirstOrder.Parse

/-!
# TPTP.FOF.Parse: total FOF formula parser

This follows the TPTP FOF grammar: `&` and `|` are associative, while the other binary
connectives are non-associative and have no general precedence.
-/

namespace TPTP.FOF

open Grip GParser
open TPTP.FirstOrder
open TPTP.FirstOrder.Parser

private def variableList : P (Array String) :=
  List.toArray <$> (GParser.ch '[' *> trivia *>
    GParser.sepBy1 variableParser (GParser.ch ',' *> trivia) <* GParser.ch ']' <* trivia)

private def atomFormula : P Formula :=
  FirstOrder.Parser.atom.map fun value =>
    match value with
    | .predicate symbol arguments =>
        if symbol.raw == "$true" && arguments.isEmpty then
          .truth
        else if symbol.raw == "$false" && arguments.isEmpty then
          .falsity
        else
          .atom value
    | .equality _ _ | .inequality _ _ => .atom value

private def binder (constructor : Array String → Formula → Formula)
    (quantifier : Char) (unitFormula : P Formula) : P Formula := gdo
  let ignoredQuantifier ← GParser.ch quantifier
  let ignoredTrivia ← trivia
  let variables ← variableList
  let ignoredColon ← GParser.ch ':'
  let ignoredBodyTrivia ← trivia
  let body ← unitFormula
  return constructor variables body
  grade_by by decide

private def negation (unitFormula : P Formula) : P Formula := gdo
  let ignoredMarker ← GParser.ch '~'
  let ignoredTrivia ← trivia
  let body ← unitFormula
  return .not body
  grade_by by decide

private def nonassocOperator : P (Formula → Formula → Formula) :=
  GParser.chooseG
    ((fun _ => Formula.iff) <$> (GParser.string "<=>" <* trivia))
    [ (fun _ => Formula.implies) <$> (GParser.string "=>" <* trivia)
    , (fun _ => Formula.impliedBy) <$> (GParser.string "<=" <* trivia)
    , (fun _ => Formula.xor) <$> (GParser.string "<~>" <* trivia)
    , (fun _ => Formula.nor) <$> (GParser.string "~|" <* trivia)
    , (fun _ => Formula.nand) <$> (GParser.string "~&" <* trivia)
    ]

private def andSeparator : P Unit :=
  (fun _ => ()) <$> (GParser.ch '&' <* trivia)

private def orSeparator : P Unit :=
  (fun _ => ()) <$> (GParser.ch '|' <* trivia)

private def nonassocFormula (unitFormula : P Formula) : P Formula := gdo
  let left ← unitFormula
  let operator ← nonassocOperator
  let right ← unitFormula
  return operator left right
  grade_by by decide

private def andFormula (unitFormula : P Formula) : P Formula :=
  GParser.map (fun (first, rest) => rest.foldl Formula.and first)
    (GParser.map2 Prod.mk unitFormula (GParser.many1 (andSeparator *> unitFormula)))

private def orFormula (unitFormula : P Formula) : P Formula :=
  GParser.map (fun (first, rest) => rest.foldl Formula.or first)
    (GParser.map2 Prod.mk unitFormula (GParser.many1 (orSeparator *> unitFormula)))

private def formulaParser : P Formula :=
  GParser.fix fun formula =>
    let unitary (unitFormula : P Formula) : P Formula :=
      GParser.dispatch fun byte =>
        if byte == Ascii.code '!' then
          binder Formula.forall '!' unitFormula
        else if byte == Ascii.code '?' then
          binder Formula.exists '?' unitFormula
        else if byte == Ascii.lparen then
          GParser.ch '(' *> trivia *> formula <* GParser.ch ')'
        else
          atomFormula
    let unitFormula : P Formula :=
      GParser.fix fun recursive =>
        GParser.chooseG (negation recursive)
          [unitary recursive]
    GParser.chooseG (nonassocFormula unitFormula)
      [orFormula unitFormula, andFormula unitFormula, unitFormula]

/-- Parse a complete FOF formula from bytes. -/
def parseFormula (source : ByteArray) : Except Grip.ParseError Formula :=
  (trivia *> formulaParser <* trivia <* GParser.eof).parse source

/-- Parse a complete FOF formula from UTF-8 text. -/
def parseFormulaString (source : String) : Except Grip.ParseError Formula :=
  parseFormula source.toUTF8

end TPTP.FOF
