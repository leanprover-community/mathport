import Lake
open Lake DSL

package mathport

-- Please ensure that `lean-toolchain` points to the same release of Lean 4
-- as this commit of mathlib4 uses.
require mathlib from git "https://github.com/leanprover-community/mathlib4"@"58f072fdbfd5dd77c98d8393a489ed3eff383ac8"

@[defaultTarget]
lean_exe mathport where
  root := `MathportApp
  supportInterpreter := true
