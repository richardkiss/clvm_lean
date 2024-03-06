import Lake
open Lake DSL

package «lean-clvm» where
  -- Settings applied to both builds and interactive editing
  leanOptions := #[
    ⟨`pp.unicode.fun, true⟩, -- pretty-prints `fun a ↦ b`
    ⟨`pp.proofs.withType, false⟩
  ]
  -- add any additional package configuration options here

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git"


lean_lib «Clvm» where
  -- add any library configuration options here


@[default_target]
lean_exe «Main» where
  root := `Main
