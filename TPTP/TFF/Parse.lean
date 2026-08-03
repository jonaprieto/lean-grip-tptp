/-
Copyright (c) 2026 Jonathan Prieto-Cubides. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonathan Prieto-Cubides
-/

import TPTP.TFF
import TPTP.FirstOrder.Parse
import TPTP.Syntax

/-!
# TPTP.TFF.Parse: total TF0 parser

The parser follows the monomorphic typed first-order fragment. Type constructors,
polymorphic binders, FOOL terms, and subtypes are deliberately outside this
module's profile and are rejected by the grammar rather than reinterpreted.
-/

namespace TPTP.TFF

open Grip GParser
open TPTP.FirstOrder
open TPTP.FirstOrder.Parser

abbrev P (α : Type) := GParser conditional α

private def atomType : P TypeExpr :=
  TypeExpr.atom <$> FirstOrder.Parser.symbol

private def typeParser : P TypeExpr :=
  GParser.fix fun recursive =>
    let parenthesized : P TypeExpr :=
      GParser.ch '(' *> trivia *> recursive <* GParser.ch ')' <* trivia
    let unitary : P TypeExpr :=
      GParser.dispatch fun byte =>
        if byte == Ascii.lparen then parenthesized else atomType
    let product : P TypeExpr := gdo
      let first ← unitary
      let rest ← GParser.many (GParser.ch '*' *> trivia *> unitary)
      return if rest.isEmpty then first else .product (List.toArray (first :: rest))
      grade_by by decide
    GParser.map2 (fun left right => right.map (TypeExpr.mapping (match left with
      | .product values => values
      | value => #[value])) |>.getD left)
      product (GParser.optional (GParser.ch '>' *> trivia *> recursive))

private def typeDeclaration : P Declaration := gdo
  let symbol ← FirstOrder.Parser.symbol
  let _ ← GParser.ch ':'
  let _ ← trivia
  let type ← typeParser
  return { symbol, type }
  grade_by by decide

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

private def typedVariable : P TypedVariable := gdo
  let name ← variableParser
  let type ← GParser.optional (GParser.ch ':' *> trivia *> atomType)
  return { name, type }
  grade_by by decide

private def variableList : P (Array TypedVariable) :=
  List.toArray <$> (GParser.ch '[' *> trivia *>
    GParser.sepBy1 typedVariable (GParser.ch ',' *> trivia) <* GParser.ch ']' <* trivia)

private def binder (constructor : Array TypedVariable → Formula → Formula)
    (quantifier : Char) (unitFormula : P Formula) : P Formula := gdo
  let _ ← GParser.ch quantifier
  let _ ← trivia
  let variables ← GParser.optional variableList
  let _ ← GParser.ch ':'
  let _ ← trivia
  let body ← unitFormula
  return constructor (variables.getD #[]) body
  grade_by by decide

private def negation (unitFormula : P Formula) : P Formula := gdo
  let _ ← GParser.ch '~'
  let _ ← trivia
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
          GParser.ch '(' *> trivia *> formula <* GParser.ch ')' <* trivia
        else
          atomFormula
    let unitFormula : P Formula :=
      GParser.fix fun recursive =>
        GParser.chooseG (negation recursive)
          [unitary recursive]
    GParser.chooseG (nonassocFormula unitFormula)
      [orFormula unitFormula, andFormula unitFormula, unitFormula]

private def parseFormulaBytes (source : ByteArray) : Except Grip.ParseError Formula :=
  (trivia *> formulaParser <* trivia <* GParser.eof).parse source

/-- Parse a complete TF0 formula from bytes. -/
def parseFormula (source : ByteArray) : Except Grip.ParseError Formula :=
  parseFormulaBytes source

/-- Parse a complete TF0 formula from UTF-8 text. -/
def parseFormulaString (source : String) : Except Grip.ParseError Formula :=
  parseFormula source.toUTF8

/-- Parse a complete TF0 type declaration from bytes. -/
def parseTypeDeclaration (source : ByteArray) : Except Grip.ParseError Declaration :=
  (trivia *> typeDeclaration <* trivia <* GParser.eof).parse source

/-- Parse a complete TF0 type declaration from UTF-8 text. -/
def parseTypeDeclarationString (source : String) : Except Grip.ParseError Declaration :=
  parseTypeDeclaration source.toUTF8

/-- Parse the typed body of one tff statement, using the type role for declarations. -/
def parseStatementBody (statement : TPTP.Statement) : Except TPTP.FormulaError Body :=
  if statement.kind != .tff then
    .error (.wrongKind .tff statement.kind)
  else if statement.role == .type then
    match parseTypeDeclarationString statement.formula with
    | .ok declaration => .ok (.declaration declaration)
    | .error error => .error (.syntax error)
  else
    match parseFormulaString statement.formula with
    | .ok formula => .ok (.formula formula)
    | .error error => .error (.syntax error)

end TPTP.TFF
