import Lake
open Lake DSL

package mathport

-- Please ensure that `lean-toolchain` points to the same release of Lean 4
-- as this commit of mathlib4 uses.
require mathlib from git "https://github.com/leanprover-community/mathlib4"@"8b7a86a8c1a98511e706f54beb288ee1974f052f"

@[defaultTarget]
lean_exe mathport where
  root := `MathportApp
  supportInterpreter := true
