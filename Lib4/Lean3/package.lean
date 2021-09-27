import Lake.Package

open Lake System

def package : Lake.PackageConfig := {
  name := "Lean3"
  version := "0.1"
  libRoots := #[],
  libGlobs := #[],
  dependencies := [
  {
    name := "Mathlib",
    src := Source.git "https://github.com/dselsam/mathlib4.git" "lake" none,
    dir := FilePath.mk "."
  },
  {
    name := "Mathport",
    src := Source.git "https://github.com/leanprover/mathport.git" "master" none,
    dir := FilePath.mk "."
  }
  ]
}
