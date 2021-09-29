import Lake.Package

open Lake System

def package : Lake.PackageConfig := {
  name := "mathbin"
  libRoots := #[],
  libGlobs := #[],
  dependencies := [{
    name := "leanbin",
    src := Source.path (FilePath.mk "../leanbin")
  }]
}
