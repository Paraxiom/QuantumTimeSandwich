import Lake
open Lake DSL

package SpectralGap where
  leanOptions := #[⟨`autoImplicit, false⟩]

@[default_target]
lean_lib SpectralGap where
  srcDir := "."

require mathlib from git
  "https://github.com/leanprover-community/mathlib4" @ "v4.27.0"
