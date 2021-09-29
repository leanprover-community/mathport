import Lake.Package

open Lake System

def package : Lake.PackageConfig := {
  name := "mathbin"
  libRoots := #[],
  libGlobs := #[],
  dependencies := [{
    name := "lean3",
    src := Source.path (FilePath.mk "../Lean3")
  }]
}
