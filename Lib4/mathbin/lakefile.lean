import Lake

open Lake DSL System

package mathib {
  libRoots := #[],
  libGlobs := #[],
  dependencies := #[{
    name := "leanbin",
    src := Source.path (FilePath.mk "../leanbin")
  }]
}
