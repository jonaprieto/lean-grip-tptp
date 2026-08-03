/-
Copyright (c) 2026 Jonathan Prieto-Cubides. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonathan Prieto-Cubides
-/

import Grip
import TPTP.FirstOrder

/-!
# TPTP.FirstOrder.Parse: shared lexical and atomic parsers

FOF and CNF use the same terms and atomic formulas. This module owns their common
tokens so the dialect parsers cannot drift apart.
-/

namespace TPTP.FirstOrder.Parser

open Grip GParser

abbrev P (α : Type) := GParser conditional α

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

def trivia : GParser flexible Nat := GParser.skipMany triviaUnit

private def visible (quote : UInt8) (byte : UInt8) : Bool :=
  32 ≤ byte && byte ≤ 126 && byte != quote && byte != Ascii.backslash

private def escaped (quote : UInt8) : GParser conditional String :=
  GParser.map (fun byte => String.ofList ['\\', Char.ofNat byte.toNat])
    (GParser.byte Ascii.backslash *> GParser.satisfy (fun byte => byte == quote ||
      byte == Ascii.backslash))

private def quotedBody (quote : UInt8) : GParser flexible String :=
  String.join <$> GParser.many (GParser.alt
    (GParser.capture (GParser.takeWhile1 (visible quote)))
    (escaped quote))

private def quoted (quote : UInt8) : P Symbol :=
  Symbol.mk <$> (GParser.capture (GParser.byte quote *> quotedBody quote <* GParser.byte quote)
    <* trivia)

private def wordTail : UInt8 → Bool := fun byte => Ascii.isAlphaNum byte || byte == 95

private def lowerWord : P Symbol :=
  Symbol.mk <$> (GParser.capture
    (GParser.satisfy Ascii.isLower *> GParser.takeWhile wordTail) <* trivia)

private def upperWord : P String :=
  GParser.capture (GParser.satisfy Ascii.isUpper *> GParser.takeWhile wordTail) <* trivia

private def backquoted : P Symbol :=
  Symbol.mk <$> (GParser.capture
    (GParser.byte 96 *> GParser.satisfy Ascii.isUpper *> GParser.takeWhile wordTail) <* trivia)

private def dollarWord : P Symbol :=
  Symbol.mk <$> (GParser.capture
    (GParser.byte (Ascii.code '$') *> GParser.optional (GParser.byte (Ascii.code '$')) *>
      GParser.takeWhile (fun byte => Ascii.isAlphaNum byte || byte == 95)) <* trivia)

private def zero : P Unit := (fun _ => ()) <$> GParser.ch '0'

private def positiveInteger : P Unit :=
  (fun _ => ()) <$> (GParser.satisfy (fun byte => 49 ≤ byte && byte ≤ 57) *>
    GParser.takeWhile Ascii.isDigit)

private def unsignedInteger : P Unit :=
  GParser.chooseG zero [positiveInteger]

private def digits : P Unit :=
  (fun _ => ()) <$> GParser.takeWhile1 Ascii.isDigit

private def sign : P Unit :=
  GParser.chooseG ((fun _ => ()) <$> GParser.ch '+')
    [(fun _ => ()) <$> GParser.ch '-']

private def signedDigits : P Unit := gdo
  let ignoredSign ← GParser.optional sign
  digits
  grade_by by decide

private def decimalFraction : P Unit := gdo
  unsignedInteger
  let ignoredDot ← GParser.ch '.'
  digits
  grade_by by decide

private def exponentMantissa : P Unit :=
  GParser.chooseG decimalFraction [unsignedInteger]

private def exponentMarker : P Unit :=
  GParser.chooseG ((fun _ => ()) <$> GParser.ch 'e')
    [(fun _ => ()) <$> GParser.ch 'E']

private def decimalExponent : P Unit := gdo
  let ignoredMantissa ← exponentMantissa
  let ignoredExponent ← exponentMarker
  signedDigits
  grade_by by decide

private def unsignedReal : P Unit :=
  GParser.chooseG decimalExponent [decimalFraction]

private def unsignedRational : P Unit := gdo
  unsignedInteger
  let ignoredSlash ← GParser.ch '/'
  positiveInteger
  grade_by by decide

private def unsignedNumber : P Unit :=
  GParser.chooseG unsignedReal [unsignedRational, unsignedInteger]

private def numberCore : P Unit := gdo
  let ignoredSign ← GParser.optional sign
  unsignedNumber
  grade_by by decide

private def number : P Symbol :=
  Symbol.mk <$> (GParser.capture numberCore <* trivia)

def symbol : P Symbol :=
  GParser.dispatch fun byte =>
    if byte == Ascii.code '$' then dollarWord
    else if byte == Ascii.apostrophe then quoted Ascii.apostrophe
    else if byte == 96 then backquoted
    else if byte == 34 then quoted 34
    else if Ascii.isLower byte then lowerWord
    else number

private def predicateSymbol : P Symbol :=
  GParser.chooseG dollarWord [quoted Ascii.apostrophe, backquoted, lowerWord]

def variableParser : P String := upperWord

def argumentList (term : P Term) : P (Array Term) :=
  List.toArray <$> (GParser.ch '(' *> trivia *>
    GParser.sepBy1 term (GParser.ch ',' *> trivia) <* GParser.ch ')' <* trivia)

private def symbolTerm (recursive : P Term) : P Term := gdo
  let symbol ← symbol
  let arguments ← GParser.optional (argumentList recursive)
  return arguments.map (Term.function symbol) |>.getD (.constant symbol)
  grade_by by decide

def term : P Term :=
  GParser.fix fun recursive =>
    GParser.chooseG (Term.variable <$> variableParser) [symbolTerm recursive]

private def equality : P Atom :=
  FirstOrder.Atom.equality <$> term <* (GParser.ch '=' *> trivia) <*> term

private def inequality : P Atom :=
  FirstOrder.Atom.inequality <$> term <* (GParser.string "!=" *> trivia) <*> term

private def predicate : P Atom := gdo
  let symbol ← predicateSymbol
  let arguments ← GParser.optional (argumentList term)
  return .predicate symbol (arguments.getD #[])
  grade_by by decide

def atom : P Atom := GParser.chooseG equality [inequality, predicate]

end TPTP.FirstOrder.Parser
