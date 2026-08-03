/-
Copyright (c) 2026 Jonathan Prieto-Cubides. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonathan Prieto-Cubides
-/

import TPTP.CNF
import TPTP.FOF.Validate

/-!
# TPTP.CNF.Validate: CNF symbol validation

CNF variables are implicitly universally quantified, so CNF validation only needs to check
the shared defined and system symbol rules. Binding validation belongs to FOF.
-/

namespace TPTP.CNF

def validate (clause : Clause) : Except FOF.ValidationError Unit :=
  do
    let _ ← clause.literals.toList.mapM fun literal =>
      match literal with
      | .positive atom | .negative atom => FOF.validateAtomSymbols atom
    pure ()

end TPTP.CNF
