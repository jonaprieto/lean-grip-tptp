/-
Copyright (c) 2026 Jonathan Prieto-Cubides. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonathan Prieto-Cubides
-/

import TPTP.CNF
import TPTP.FirstOrder.Render

/-!
# TPTP.CNF.Render: canonical clause rendering
-/

namespace TPTP.CNF

def Literal.render : Literal → String
  | .positive value => value.render
  | .negative value => s!"~({value.render})"

def Clause.render (clause : Clause) : String :=
  if clause.literals.isEmpty then
    "$false"
  else
    String.intercalate " | " (clause.literals.toList.map Literal.render)

instance : ToString Literal where
  toString := Literal.render

instance : ToString Clause where
  toString := Clause.render

end TPTP.CNF
