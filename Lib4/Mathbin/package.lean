import Lake.Package

open Lake System

def package : Lake.PackageConfig := {
  name := "Mathbin"
  version := "0.1"
  libRoots := #[],
  libGlobs := #[],
  dependencies := [{
    name := "Mathlib",
    src := Source.git "https://github.com/dselsam/mathlib4.git" "lake" none
  }, {
    name := "Mathport",
    src := Source.git "https://github.com/leanprover/mathport.git" "master" none
  }, {
    name := "Lean3",
    src := Source.path (FilePath.mk "../Lean3")
  }]
}
