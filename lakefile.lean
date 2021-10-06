import Lake

open Lake DSL System

package mathport {
  dependencies := #[{
    name := "mathlib",
    src := Source.git "https://github.com/dselsam/mathlib4.git" "lake" none,
    dir := FilePath.mk "."
  }],
  binRoot := `MathportApp
  linkArgs := #["-rdynamic"]
}
