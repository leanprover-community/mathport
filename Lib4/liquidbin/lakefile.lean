import Lake.Package

open Lake System

def package : Lake.PackageConfig := {
  name := "liquidbin"
  libRoots := #[],
  libGlobs := #[],
  dependencies := [{
    name := "mathbin",
    src := Source.path (FilePath.mk "../mathbin")
  }]
}
