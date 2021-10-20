import Lake

open Lake DSL System

package mathbin {
  libRoots := #[],
  libGlobs := #[],
  dependencies := #[{
    name := "leanbin",
    src := Source.path (FilePath.mk "../leanbin")
  }]
}
