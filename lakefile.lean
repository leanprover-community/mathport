import Lake

open Lake DSL System

package mathport {
  dependencies := #[{
    name := "mathlib",
    src := Source.git "https://github.com/semorrison/mathlib4.git" "lake" none,
    dir := FilePath.mk "."
  }],
  binRoot := `MathportApp
  moreLinkArgs := #["-rdynamic"]
}
