import Lake
open Lake DSL

package "lustrean" where
  version := v!"0.1.0"

lean_lib «Lustrean» where
  leanOptions := #[
    ⟨`autoImplicit, false⟩
  ]

@[default_target]
lean_exe "lustrean" where
  root := `Main
