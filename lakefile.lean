import Lake
open Lake DSL

package «tptp» where
  version := v!"0.5.3"
  leanOptions := #[⟨`autoImplicit, false⟩, ⟨`relaxedAutoImplicit, false⟩]

require grip from git
  "https://github.com/jonaprieto/lean-grip.git"
  @ "v0.1.0"

@[default_target]
lean_lib «TPTP» where
  roots := #[`TPTP]
  globs := #[.andSubmodules `TPTP]

lean_lib «TPTP.Properties» where
  roots := #[`TPTP.Properties]
  globs := #[.andSubmodules `TPTP.Properties]

lean_exe «demo» where
  root := `Demo
  srcDir := "examples"

@[test_driver]
lean_exe «tests» where
  root := `Tests
  srcDir := "test"

lean_exe «conformance» where
  root := `Conformance
  srcDir := "test"

lean_exe «corpus» where
  root := `Corpus
  srcDir := "examples"
