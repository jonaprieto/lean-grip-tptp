/-
Copyright (c) 2026 Jonathan Prieto-Cubides. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonathan Prieto-Cubides
-/

import Grip
import TPTP.Syntax

/-!
# TPTP.Parse: total TPTP/TSTP parsers

The envelope parser accepts all standard statement tags while preserving the
formula and annotation bodies as text. Recursive grammar pieces use Grip's
fuelled `fix`; this module contains no `partial` parser definitions.
-/

namespace TPTP

open Grip GParser

private def isNameByte (byte : UInt8) : Bool :=
  Ascii.isAlphaNum byte || byte == 95 || byte == 36

private def isDelimiter (byte : UInt8) : Bool :=
  byte == 40 || byte == 41 || byte == 91 || byte == 93 || byte == 123 || byte == 125 ||
    byte == 34 || byte == 39 || byte == Ascii.code '%' || byte == Ascii.slash

private def whitespace : GParser conditional Unit :=
  (fun _ => ()) <$> GParser.satisfy Ascii.isWs

private def lineComment : GParser conditional Unit :=
  (fun _ => ()) <$> (GParser.byte (Ascii.code '%') *> GParser.takeWhile (· != Ascii.lf))

private def blockComment : GParser conditional Unit :=
  (fun _ => ()) <$> (GParser.string "/*" *>
    GParser.manyTill (GParser.satisfy (fun _ => true)) (GParser.string "*/"))

private def triviaUnit : GParser conditional Unit :=
  GParser.dispatch fun byte =>
    if byte == Ascii.code '%' then lineComment
    else if byte == Ascii.slash then blockComment
    else whitespace

private def trivia : GParser flexible Nat := GParser.skipMany triviaUnit

private def escapedByte : GParser conditional UInt8 :=
  GParser.byte Ascii.backslash *> GParser.satisfy (fun _ => true)

private def quotedPiece (quote : UInt8) (body : GParser flexible String) :
    GParser conditional String :=
  GParser.capture (GParser.byte quote *> body <* GParser.byte quote)

private def escapedChunk : GParser conditional String :=
  GParser.map (fun byte => String.ofList ['\\', Char.ofNat byte.toNat]) escapedByte

private def quotedBody (quote : UInt8) : GParser flexible String :=
  String.join <$> GParser.many (GParser.alt
    (GParser.capture (GParser.takeWhile1 (fun byte => byte != quote && byte != Ascii.backslash)))
    escapedChunk)

private def quotedName : GParser conditional Name :=
  Name.quoted <$> quotedPiece Ascii.apostrophe (quotedBody Ascii.apostrophe)

private def bareName : GParser conditional Name :=
  Name.bare <$> GParser.capture (GParser.takeWhile1 isNameByte)

private def name : GParser conditional Name := quotedName <|> bareName

private def rawGroup (opener closer : Char) (body : GParser conditional String) :
    GParser conditional String :=
  GParser.map (fun value => String.ofList [opener] ++ value ++ String.ofList [closer])
    (GParser.ch opener *> body <* GParser.ch closer)

private def rawLineComment : GParser conditional String :=
  GParser.capture (GParser.byte (Ascii.code '%') *> GParser.takeWhile (· != Ascii.lf))

private def rawBlockComment : GParser conditional String :=
  GParser.capture (GParser.string "/*" *>
    GParser.manyTill (GParser.satisfy (fun _ => true)) (GParser.string "*/"))

private def rawText : GParser conditional String :=
  GParser.capture (GParser.takeWhile1 (fun value => !isDelimiter value))

private def rawSlash : GParser conditional String :=
  GParser.capture (GParser.byte Ascii.slash)

private def rawPiece (body : GParser conditional String) : GParser conditional String :=
  GParser.dispatch fun byte =>
    if byte == 40 then rawGroup '(' ')' body
    else if byte == 91 then rawGroup '[' ']' body
    else if byte == 123 then rawGroup '{' '}' body
    else if byte == 34 then quotedPiece 34 (quotedBody 34)
    else if byte == 39 then quotedPiece 39 (quotedBody 39)
    else if byte == Ascii.code '%' then rawLineComment
    else if byte == Ascii.slash then GParser.alt rawBlockComment rawSlash
    else rawText

private def rawBody : GParser conditional String :=
  GParser.fix fun body => String.join <$> GParser.many1 (rawPiece body)

private inductive Comment where
  | line
  | block

private def splitAnnotation (body : String) : String × Option String :=
  let rec go (input : List Char) (round square curly : Nat) (quote : Option Char)
      (escaped : Bool) (comment : Option Comment) (formula : List Char) :
      String × Option String :=
    match input with
    | [] => (String.ofList formula.reverse, none)
    | character :: rest =>
        match quote with
        | some delimiter =>
            if escaped then go rest round square curly quote false comment (character :: formula)
            else if character == '\\' then
              go rest round square curly quote true comment (character :: formula)
            else if character == delimiter then
              go rest round square curly none false comment (character :: formula)
            else
              go rest round square curly quote false comment (character :: formula)
        | none =>
            match comment with
            | some .line =>
                go rest round square curly none false
                  (if character == '\n' then none else some .line) (character :: formula)
            | some .block =>
                match rest with
                | [] => go [] round square curly none false (some .block) (character :: formula)
                | first :: tail =>
                    if character == '*' && first == '/' then
                      go tail round square curly none false none ('/' :: '*' :: formula)
                    else
                      go (first :: tail) round square curly none false (some .block)
                        (character :: formula)
            | none =>
                if character == '"' || character == '\'' then
                  go rest round square curly (some character) false none (character :: formula)
                else if character == '%' then
                  go rest round square curly none false (some .line) (character :: formula)
                else if character == '/' then
                  match rest with
                  | [] => go [] round square curly none false none (character :: formula)
                  | first :: tail =>
                      if first == '*' then
                        go tail round square curly none false (some .block)
                          ('*' :: '/' :: formula)
                      else
                        go (first :: tail) round square curly none false none (character :: formula)
                else if character == '(' then
                  go rest (round + 1) square curly none false none (character :: formula)
                else if character == ')' && round > 0 then
                  go rest (round - 1) square curly none false none (character :: formula)
                else if character == '[' then
                  go rest round (square + 1) curly none false none (character :: formula)
                else if character == ']' && square > 0 then
                  go rest round (square - 1) curly none false none (character :: formula)
                else if character == '{' then
                  go rest round square (curly + 1) none false none (character :: formula)
                else if character == '}' && curly > 0 then
                  go rest round square (curly - 1) none false none (character :: formula)
                else if character == ',' && round == 0 && square == 0 && curly == 0 then
                  (String.ofList formula.reverse, some (String.ofList rest))
                else
                  go rest round square curly none false none (character :: formula)
  termination_by input.length
  decreasing_by all_goals simp_all <;> omega
  go body.toList 0 0 0 none false none []

private def kind : GParser conditional Kind :=
  Kind.ofString <$> GParser.capture (GParser.takeWhile1 isNameByte)

private def role : GParser conditional Role :=
  Role.ofString <$> GParser.capture (GParser.takeWhile1 isNameByte)

private def statementParser : GParser conditional Statement := gdo
  let kind ← kind
  let _ ← trivia
  let _ ← GParser.ch '('
  let _ ← trivia
  let name ← name
  let _ ← trivia
  let _ ← GParser.ch ','
  let _ ← trivia
  let role ← role
  let _ ← trivia
  let _ ← GParser.ch ','
  let _ ← trivia
  let body ← rawBody
  let _ ← trivia
  let _ ← GParser.ch ')'
  let _ ← GParser.ch '.'
  let parts := splitAnnotation body
  return {
    kind,
    name,
    role,
    formula := parts.1.trimAscii.toString
    annotations := parts.2.map (·.trimAscii.toString)
  }
  grade_by by decide

private def includeParser : GParser conditional Include := gdo
  let _ ← GParser.string "include"
  let _ ← trivia
  let _ ← GParser.ch '('
  let _ ← trivia
  let path ← name
  let selection ← GParser.optional (trivia *> GParser.ch ',' *> trivia *> rawBody)
  let _ ← trivia
  let _ ← GParser.ch ')'
  let _ ← GParser.ch '.'
  return { path, selection := selection.map (·.trimAscii.toString) }
  grade_by by decide

private def itemParser : GParser conditional Item :=
  (Item.include <$> includeParser) <|> (Item.statement <$> statementParser)

private def documentParser : Grip.Parser Document :=
  let items := trivia *> GParser.many (itemParser <* trivia) <* GParser.eof
  GParser.map (fun values => { items := values.toArray }) (GParser.weakenFallible items)

/-- Parse a complete TPTP/TSTP document from bytes. -/
def parse (source : ByteArray) : Except Grip.ParseError Document :=
  documentParser.parse source

/-- Parse a complete TPTP/TSTP document from UTF-8 text. -/
def parseString (source : String) : Except Grip.ParseError Document :=
  parse source.toUTF8

/-- Parse exactly one TPTP/TSTP statement. -/
def parseStatement (source : ByteArray) : Except Grip.ParseError Statement :=
  (trivia *> statementParser <* trivia <* GParser.eof).parse source

/-- Parse exactly one TPTP/TSTP statement from UTF-8 text. -/
def parseStatementString (source : String) : Except Grip.ParseError Statement :=
  parseStatement source.toUTF8

namespace Formula

private def token : GParser conditional String :=
  GParser.capture (GParser.takeWhile1 isNameByte) <* trivia

private def argumentList (term : GParser conditional Term) : GParser conditional (Array Term) :=
  GParser.ch '(' *> trivia *>
    ((GParser.pure #[] <* GParser.ch ')') <|>
      (List.toArray <$> GParser.sepBy1 term (trivia *> GParser.ch ',' <* trivia)
        <* trivia <* GParser.ch ')'))

private def termParser : GParser conditional Term :=
  GParser.fix fun (term : GParser conditional Term) => gdo
    let name ← token
    let arguments ← GParser.optional (argumentList term)
    let arguments := arguments.getD #[]
    let first := name.toList.head!
    let value := if (first.isUpper || first == '_') && arguments.isEmpty then
        Term.var name
      else if arguments.isEmpty then
        Term.constant name
      else
        Term.function name arguments
    return value
    grade_by by decide

private def atomParser : GParser conditional Expr := gdo
  let predicate ← token
  let arguments ← GParser.optional (argumentList termParser)
  let arguments := arguments.getD #[]
  let value := if predicate == "$true" && arguments.isEmpty then
      Expr.truth
    else if predicate == "$false" && arguments.isEmpty then
      Expr.falsity
    else
      Expr.atom predicate arguments
  return value
  grade_by by decide

private def variableList : GParser conditional (Array String) :=
  GParser.ch '[' *> trivia *>
    (List.toArray <$> GParser.sepBy1 token (trivia *> GParser.ch ',' <* trivia)
      <* trivia <* GParser.ch ']')

private def formulaParser : GParser conditional Expr :=
  GParser.fix fun (formula : GParser conditional Expr) =>
    let unary : GParser conditional Expr :=
      GParser.fix fun unary =>
        GParser.dispatch fun byte =>
          if byte == Ascii.code '~' then
            Expr.not <$> (GParser.ch '~' *> trivia *> unary)
          else if byte == Ascii.code '!' then
            Expr.forall <$> (GParser.ch '!' *> trivia *> variableList <* trivia <*
              GParser.ch ':' <* trivia)
              <*> formula
          else if byte == Ascii.code '?' then
            Expr.exists <$> (GParser.ch '?' *> trivia *> variableList <* trivia <*
              GParser.ch ':' <* trivia)
              <*> formula
          else if byte == Ascii.lparen then
            GParser.ch '(' *> trivia *> formula <* trivia <* GParser.ch ')'
          else
            atomParser
    let andParser : GParser conditional Expr :=
      GParser.map (fun (first, rest) => rest.foldl (fun left right => .and left right) first)
        (GParser.map2 Prod.mk unary
          (GParser.many (trivia *> GParser.ch '&' *> trivia *> unary)))
    let orParser : GParser conditional Expr :=
      GParser.map (fun (first, rest) => rest.foldl (fun left right => .or left right) first)
        (GParser.map2 Prod.mk andParser
          (GParser.many (trivia *> GParser.ch '|' *> trivia *> andParser)))
    let impliesParser : GParser conditional Expr :=
      GParser.fix fun (implies : GParser conditional Expr) => gdo
        let left ← orParser
        let right ← GParser.optional (trivia *> GParser.string "=>" *> trivia *> implies)
        return right.map (Expr.implies left) |>.getD left
    GParser.fix fun iff => gdo
      let left ← impliesParser
      let right ← GParser.optional (trivia *> GParser.string "<=>" *> trivia *> iff)
      return right.map (Expr.iff left) |>.getD left
      grade_by by decide

/-- Parse the supported first-order formula fragment from bytes. -/
def parseFormula (source : ByteArray) : Except Grip.ParseError Expr :=
  (trivia *> formulaParser <* trivia <* GParser.eof).parse source

/-- Parse the supported first-order formula fragment from UTF-8 text. -/
def parseFormulaString (source : String) : Except Grip.ParseError Expr :=
  parseFormula source.toUTF8

end Formula

def Statement.parseFormula (statement : Statement) : Except Grip.ParseError Formula.Expr :=
  Formula.parseFormulaString statement.formula

end TPTP
