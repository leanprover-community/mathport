import Lake.Package

open Lake System

def package : Lake.PackageConfig := {
  name := "MathportApp"
  version := "0.1"
  dependencies := [
    { name := "Mathport", src := Source.path (FilePath.mk "../Lib") }
  ]
  linkArgs := #["-rdynamic"]
}
