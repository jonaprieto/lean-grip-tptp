/-
Copyright (c) 2026 Jonathan Prieto-Cubides. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonathan Prieto-Cubides
-/

import TPTP.FirstOrder

/-!
# TPTP.TFF: monomorphic typed first-order syntax

This module models TF0, the monomorphic typed first-order fragment of TFF. It
keeps type checking separate from parsing: the parser preserves the syntax tree,
while `TPTP.TFF.Validate` checks declarations, scopes, applications, and types.
-/

namespace TPTP.TFF

abbrev Symbol := FirstOrder.Symbol
abbrev Term := FirstOrder.Term
abbrev Atom := FirstOrder.Atom

inductive TypeExpr where
  | atom (symbol : Symbol)
  | product (elements : Array TypeExpr)
  | mapping (arguments : Array TypeExpr) (result : TypeExpr)
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

end TPTP.TFF
