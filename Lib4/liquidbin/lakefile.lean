import Lake

open Lake DSL System

package liquidbin {
  libRoots := #[],
  libGlobs := #[],
  dependencies := #[{
    name := "mathbin",
    src := Source.path (FilePath.mk "../mathbin")
  }]
}
