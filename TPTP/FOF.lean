/-
Copyright (c) 2026 Jonathan Prieto-Cubides. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonathan Prieto-Cubides
-/

import TPTP.FirstOrder

/-!
# TPTP.FOF: first-order formula syntax
-/

namespace TPTP.FOF

abbrev Symbol := FirstOrder.Symbol
abbrev Term := FirstOrder.Term
abbrev Atom := FirstOrder.Atom

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
  | forall (variables : Array String) (body : Formula)
  | exists (variables : Array String) (body : Formula)
  deriving BEq, Repr

end TPTP.FOF
