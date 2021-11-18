import Lake

open Lake DSL System

package importMathbin where
  defaultFacet := PackageFacet.oleans
  dependencies := #[{
    name := "mathlib3port",
    src := Source.git "https://github.com/leanprover-community/mathlib3port.git" "master"
  }]
