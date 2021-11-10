import Lake

open Lake DSL System

package leanbin {
  libRoots := #[],
  libGlobs := #[],
  dependencies := #[
  {
    name := "mathport",
    src := Source.git "https://github.com/leanprover-community/mathport.git" "master" none,
    dir := FilePath.mk "."
  }
  ]
}
