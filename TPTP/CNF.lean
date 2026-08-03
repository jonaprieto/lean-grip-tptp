/-
Copyright (c) 2026 Jonathan Prieto-Cubides. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonathan Prieto-Cubides
-/

import TPTP.FirstOrder

/-!
# TPTP.CNF: clause normal form syntax
-/

namespace TPTP.CNF

abbrev Symbol := FirstOrder.Symbol
abbrev Term := FirstOrder.Term
abbrev Atom := FirstOrder.Atom

inductive Literal where
  | positive (value : Atom)
  | negative (value : Atom)
  deriving BEq, Repr

structure Clause where
  /-- Literals in their source order. CNF variables are implicitly universal. -/
  literals : Array Literal
  deriving BEq, Repr

end TPTP.CNF
