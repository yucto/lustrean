import Lake
open Lake DSL

require "leanprover-community" / "batteries" @ git "v4.25.0"
require "leanprover-community" / "LeanSearchClient" @ git "3591c3f664ac3719c4c86e4483e21e228707bfa2"

package "lustrean" where
  version := v!"0.1.0"

lean_lib Misc where
  leanOptions := #[
    ⟨`autoImplicit, false⟩
  ]

@[default_target]
lean_lib Lustrean where
  leanOptions := #[
    ⟨`autoImplicit, false⟩
  ]
