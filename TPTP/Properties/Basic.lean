/-
Copyright (c) 2026 Jonathan Prieto-Cubides. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonathan Prieto-Cubides
-/

import TPTP

namespace TPTP.Properties

theorem bare_name_render (value : String) : Name.render (.bare value) = value := rfl

theorem quoted_name_render (value : String) : Name.render (.quoted value) = value := rfl

theorem known_kind_round_trip : (Kind.ofString "fof").render = "fof" := rfl

theorem known_role_round_trip : (Role.ofString "negated_conjecture").render =
    "negated_conjecture" := rfl

theorem empty_document_render : Document.render { items := #[] } = "" := rfl

end TPTP.Properties
