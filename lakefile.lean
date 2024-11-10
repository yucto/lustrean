import Lake
open Lake DSL

require batteries from git "https://github.com/leanprover-community/batteries" @ "v4.12.0"

require aesop from git "https://github.com/leanprover-community/aesop" @ "v4.12.0"

package "lustrean" where
  version := v!"0.1.0"

lean_lib Misc where
  leanOptions := #[
    ⟨`autoImplicit, false⟩
  ]

lean_lib Lustrean where
  leanOptions := #[
    ⟨`autoImplicit, false⟩
  ]

@[default_target]
lean_exe "lustrean" where
  root := `Main
