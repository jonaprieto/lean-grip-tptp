/-
Copyright (c) 2026 Jonathan Prieto-Cubides. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonathan Prieto-Cubides
-/

import TPTP.FirstOrder

/-!
# TPTP.FirstOrder.Render: shared canonical term and atom rendering
-/

namespace TPTP.FirstOrder

def Term.render : Term → String
  | .variable name => name
  | .constant symbol => symbol.render
  | .function symbol arguments =>
      if arguments.isEmpty then
        symbol.render
      else
        s!"{symbol.render}({String.intercalate ", " (arguments.toList.map Term.render)})"
termination_by term => term
decreasing_by
  simp_wf
  apply Nat.lt_of_lt_of_le
    (Array.sizeOf_lt_of_mem (as := arguments) (by
      apply Array.mem_def.mpr
      assumption)) ?_
  simp +arith

instance : ToString Term where
  toString := Term.render

def Atom.render : Atom → String
  | .predicate symbol arguments =>
      if arguments.isEmpty then
        symbol.render
      else
        s!"{symbol.render}({String.intercalate ", " (arguments.toList.map Term.render)})"
  | .equality left right => s!"{left.render} = {right.render}"
  | .inequality left right => s!"{left.render} != {right.render}"

instance : ToString Atom where
  toString := Atom.render

end TPTP.FirstOrder
