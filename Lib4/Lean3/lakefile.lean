import Lake.Package

open Lake System

def package : Lake.PackageConfig := {
  name := "lean3"
  libRoots := #[],
  libGlobs := #[],
  dependencies := [
  {
    name := "mathlib",
    src := Source.git "https://github.com/dselsam/mathlib4.git" "lake" none,
    dir := FilePath.mk "."
  },
  {
    name := "mathport",
    src := Source.git "https://github.com/leanprover/mathport.git" "master" none,
    dir := FilePath.mk "."
  }
  ]
}
