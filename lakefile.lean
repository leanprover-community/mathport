import Lake.Package

open Lake System

def package : Lake.PackageConfig := {
  name := "mathport"
  dependencies := [{
    name := "mathlib",
    src := Source.git "https://github.com/dselsam/mathlib4.git" "lake" none,
    dir := FilePath.mk "."
  }],
  binRoot := `MathportApp
  linkArgs := #["-rdynamic"]
}
