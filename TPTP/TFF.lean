/-
Copyright (c) 2026 Jonathan Prieto-Cubides. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonathan Prieto-Cubides
-/

import TPTP.FirstOrder

/-!
# TPTP.TFF: typed first-order syntax

This module models the TF0 and TF1 typed first-order fragments of TFF. It keeps
type checking separate from parsing: the parser preserves the syntax tree, while
`TPTP.TFF.Validate` checks declarations, scopes, applications, and types.
-/

namespace TPTP.TFF

abbrev Symbol := FirstOrder.Symbol
abbrev Term := FirstOrder.Term
abbrev Atom := FirstOrder.Atom

structure TypeBinder where
  name : String
  deriving BEq, Repr

inductive TypeExpr where
  | atom (symbol : Symbol)
  | application (constructor : Symbol) (arguments : Array TypeExpr)
  | product (elements : Array TypeExpr)
  | mapping (arguments : Array TypeExpr) (result : TypeExpr)
  | forall (variables : Array TypeBinder) (body : TypeExpr)
  deriving BEq, Repr

structure TypedVariable where
  name : String
  type : Option TypeExpr := none
  deriving BEq, Repr

inductive Formula where
  | atom (value : Atom)
  | truth
  | falsity
  | not (body : Formula)
  | and (left right : Formula)
  | or (left right : Formula)
  | implies (left right : Formula)
  | impliedBy (left right : Formula)
  | iff (left right : Formula)
  | xor (left right : Formula)
  | nor (left right : Formula)
  | nand (left right : Formula)
  | forall (variables : Array TypedVariable) (body : Formula)
  | exists (variables : Array TypedVariable) (body : Formula)
  deriving BEq, Repr

structure Declaration where
  symbol : Symbol
  type : TypeExpr
  deriving BEq, Repr

inductive Body where
  | formula (value : Formula)
  | declaration (value : Declaration)
  deriving BEq, Repr

private def substitutionLookup (substitution : Array (String × TypeExpr))
    (name : String) : Option TypeExpr :=
  substitution.find? (fun pair => pair.1 == name) |>.map Prod.snd

private def isTypeVariable (name : String) : Bool :=
  match name.toList with
  | first :: _ => first.isUpper
  | [] => false

private def appendUnique (values : Array String) (value : String) : Array String :=
  if values.toList.contains value then values else values.push value

private def freeVariablesAux : TypeExpr → Array String
  | .atom symbol => if isTypeVariable symbol.raw then #[symbol.raw] else #[]
  | .application _ arguments | .product arguments =>
      arguments.foldl (fun result type =>
        (freeVariablesAux type).foldl appendUnique result) #[]
  | .mapping arguments result =>
      let values := arguments.foldl (fun values type =>
        (freeVariablesAux type).foldl appendUnique values) #[]
      (freeVariablesAux result).foldl appendUnique values
  | .forall variables body =>
      (freeVariablesAux body).filter (fun name =>
        !variables.any (fun binder => binder.name == name))

private def binderNamesAux : TypeExpr → Array String
  | .atom _ => #[]
  | .application _ arguments | .product arguments =>
      arguments.foldl (fun result type =>
        (binderNamesAux type).foldl appendUnique result) #[]
  | .mapping arguments result =>
      let values := arguments.foldl (fun values type =>
        (binderNamesAux type).foldl appendUnique values) #[]
      (binderNamesAux result).foldl appendUnique values
  | .forall variables body =>
      let values := variables.toList.map TypeBinder.name |>.toArray
      (binderNamesAux body).foldl appendUnique values

/-- Collect free type variables in source order. -/
def TypeExpr.freeVariables (type : TypeExpr) : Array String :=
  freeVariablesAux type

private def renameBound (oldName newName : String) : TypeExpr → TypeExpr
  | .atom symbol =>
      if symbol.raw == oldName then .atom { raw := newName } else .atom symbol
  | .application constructor arguments =>
      .application constructor (arguments.map (renameBound oldName newName))
  | .product elements => .product (elements.map (renameBound oldName newName))
  | .mapping arguments result =>
      .mapping (arguments.map (renameBound oldName newName)) (renameBound oldName newName result)
  | .forall variables body =>
      if variables.any (fun binder => binder.name == oldName) then
        .forall variables body
      else
        .forall variables (renameBound oldName newName body)

private partial def freshName (base : String) (used : Array String) : String :=
  let rec loop (index : Nat) : String :=
    let candidate := if index == 0 then base else s!"{base}_{index}"
    if used.toList.contains candidate then loop (index + 1) else candidate
  loop 0

private def substitutionFreeVariables (substitution : Array (String × TypeExpr)) : Array String :=
  substitution.foldl (fun result pair =>
    (freeVariablesAux pair.2).foldl appendUnique result) #[]

private partial def substituteAux (substitution : Array (String × TypeExpr)) : TypeExpr → TypeExpr
  | .atom symbol => substitutionLookup substitution symbol.raw |>.getD (.atom symbol)
  | .application constructor arguments =>
      .application constructor (arguments.map (substituteAux substitution))
  | .product elements => .product (elements.map (substituteAux substitution))
  | .mapping arguments result =>
      .mapping (arguments.map (substituteAux substitution)) (substituteAux substitution result)
  | .forall variables body =>
      let replacementFree := substitutionFreeVariables substitution
      let boundNames := variables.toList.map TypeBinder.name |>.toArray
      let used := ((variables.toList.map TypeBinder.name).toArray ++
        binderNamesAux body ++ replacementFree)
      let (variables, body) := variables.foldl
        (fun (variables, body) binder =>
          if replacementFree.toList.contains binder.name then
            let fresh := freshName binder.name used
            (variables.push { binder with name := fresh }, renameBound binder.name fresh body)
          else
            (variables.push binder, body))
        (#[], body)
      let filtered := substitution.filter (fun pair =>
        !boundNames.toList.contains pair.1)
      .forall variables (substituteAux filtered body)

/-- Capture-avoiding substitution for the type variables in a type expression. -/
def TypeExpr.substitute (substitution : Array (String × TypeExpr)) (type : TypeExpr) : TypeExpr :=
  substituteAux substitution type

/-- Rename a bound type variable without capturing a free variable. -/
def TypeExpr.alphaRename (oldName newName : String) : TypeExpr → TypeExpr := fun type =>
  if oldName == newName then
    type
  else
    match type with
    | .atom symbol => .atom symbol
    | .application constructor arguments =>
        .application constructor (arguments.map (TypeExpr.alphaRename oldName newName))
    | .product elements => .product (elements.map (TypeExpr.alphaRename oldName newName))
    | .mapping arguments result =>
        .mapping (arguments.map (TypeExpr.alphaRename oldName newName))
          (TypeExpr.alphaRename oldName newName result)
    | .forall variables body =>
        if variables.any (fun binder => binder.name == oldName) then
          let used := ((variables.toList.map TypeBinder.name).toArray ++ binderNamesAux body)
          let fresh := if used.toList.contains newName then freshName newName used else newName
          .forall (variables.map (fun binder =>
            if binder.name == oldName then { binder with name := fresh } else binder))
            (renameBound oldName fresh body)
        else
          .forall variables (TypeExpr.alphaRename oldName newName body)

end TPTP.TFF
