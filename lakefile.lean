import Lake
open Lake DSL

package «memo-nat» {
}

require std4 from git "https://github.com/leanprover/std4" @ "main"

@[default_target]
lean_lib «MemoNat» {
  globs := #[.andSubmodules `MemoNat]
}

