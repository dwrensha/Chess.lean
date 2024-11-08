import Lake
open Lake DSL

package "Chess" where
  leanOptions := #[
    ⟨`pp.unicode.fun, true⟩, -- pretty-prints `fun a ↦ b`
    ⟨`autoImplicit, false⟩,
    ⟨`relaxedAutoImplicit, false⟩
  ]

@[default_target]
lean_lib «Chess» where
  -- add library configuration options here

require mathlib from git "https://github.com/leanprover-community/mathlib4" @ "v4.13.0"
