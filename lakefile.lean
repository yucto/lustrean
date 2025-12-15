import Lake
open Lake DSL

require "leanprover-community" / "mathlib"

package "lustrean" where
  version := v!"0.1.0"

@[default_target]
lean_lib Lustrean where
  leanOptions := #[
    ⟨`autoImplicit, false⟩
  ]

lean_lib Misc where
  leanOptions := #[
    ⟨`autoImplicit, false⟩
  ]

/- If is stays named as `Test`, `lake test` somehow fails with:
error: no such file or directory (error code: 2)
  file: /home/belazy/Projects/lustrean/.lake/packages/plausible/Test/Output.lean
It looks like some conflict between this folder's name and the `Test` folder in `Plausible` is causing this ?
This is certainly a bug, but I can't be bothered to fix this
 -/
@[test_driver]
lean_lib Tests where
  leanOptions := #[
    ⟨`autoImplicit, false⟩
  ]
