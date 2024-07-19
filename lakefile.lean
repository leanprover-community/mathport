import Lake
open Lake DSL

package mathport

-- Please ensure that `lean-toolchain` points to the same release of Lean 4
-- as this commit of mathlib4 uses.
require mathlib from git "https://github.com/leanprover-community/mathlib4"@"v3-eol"

target ffi.o pkg : FilePath := do
  let oFile := pkg.buildDir / "c" / "ffi.o"
  let srcJob ← inputTextFile <| pkg.dir / "Mathport" / "FFI.cpp"
  let flags := #["-I", (← getLeanIncludeDir).toString, "-fPIC"]
  buildO oFile srcJob flags (compiler := "c++")

extern_lib libleanffi (pkg : NPackage `mathport) := do
  let name := nameToStaticLib "leanffi"
  let ffiO ← fetch <| pkg.target ``ffi.o
  buildStaticLib (pkg.nativeLibDir / name) #[ffiO]

lean_lib Mathport

@[default_target]
lean_exe mathport where
  root := `MathportApp
  supportInterpreter := true

@[default_target]
lean_exe printast where
  root := `PrintAST
