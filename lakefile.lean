import Lake
open Lake DSL

package «tptp» where
  version := v!"0.2.0"
  leanOptions := #[⟨`autoImplicit, false⟩, ⟨`relaxedAutoImplicit, false⟩]

require grip from git
  "https://github.com/jonaprieto/lean-grip.git"
  @ "986b668d3da7919f24e2612770c227a2e8bb1fb5"

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

lean_exe «tests» where
  root := `Tests
  srcDir := "test"

lean_exe «corpus» where
  root := `Corpus
  srcDir := "examples"
