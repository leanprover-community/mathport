import Lake.Package

open Lake System

def package : Lake.PackageConfig := {
  name := "Mathbin"
  version := "0.1"
  libRoots := #[],
  libGlobs := #[],
  dependencies := [{
    name := "Lean3",
    src := Source.path (FilePath.mk "../Lean3")
  }]
}
