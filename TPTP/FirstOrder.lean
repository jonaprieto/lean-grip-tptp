/-
Copyright (c) 2026 Jonathan Prieto-Cubides. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonathan Prieto-Cubides
-/

/-!
# TPTP.FirstOrder: shared FOF/CNF terms and atoms

These types preserve the first-order syntax shared by FOF and CNF. Symbol spelling is
retained as source text so defined and system symbols remain forward-compatible.
-/

namespace TPTP.FirstOrder

structure Symbol where
  /-- The complete source spelling, including quotes when present. -/
  raw : String
  deriving BEq, Repr

def Symbol.render (symbol : Symbol) : String :=
  symbol.raw

instance : ToString Symbol where
  toString := Symbol.render

inductive Term where
  | variable (name : String)
  | constant (symbol : Symbol)
  | function (symbol : Symbol) (arguments : Array Term)
  deriving BEq, Repr

inductive Atom where
  | predicate (symbol : Symbol) (arguments : Array Term)
  | equality (left right : Term)
  | inequality (left right : Term)
  deriving BEq, Repr

end TPTP.FirstOrder
