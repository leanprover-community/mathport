import Lake

open Lake DSL System

package mathport {
  dependencies := #[{
    name := "mathlib",
    src := Source.git "https://github.com/leanprover-community/mathlib4.git" "master" none,
    dir := FilePath.mk "."
  }],
  binRoot := `MathportApp
  moreLinkArgs :=
    if Platform.isWindows then
      #["-Wl,--export-all"]
    else
      #["-rdynamic"]
}
