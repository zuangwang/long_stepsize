import Lake

open Lake DSL

package "gd-formalization" where
  version := v!"0.1.0"
  leanOptions := #[
    ⟨`pp.unicode.fun, true⟩,
    ⟨`relaxedAutoImplicit, false⟩
  ]

require "leanprover-community" / "mathlib" @ git "v4.32.2"

@[default_target]
lean_lib «GD» where
