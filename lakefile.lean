import Lake
open Lake DSL

package mathport

-- Please ensure that `lean-toolchain` points to the same release of Lean 4
-- as this commit of mathlib4 uses.
require mathlib from git "https://github.com/leanprover-community/mathlib4"@"c46f8b6aa0f6f19a50a536da61eee3945d2e7266"

@[defaultTarget]
lean_exe mathport where
  root := `MathportApp
  supportInterpreter := true
