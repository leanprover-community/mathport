import Lake

open Lake DSL System

package importMathbin where
  defaultFacet := PackageFacet.oleans
  dependencies := #[{
    name := "mathbin",
    src := Source.git "https://github.com/leanprover-community/mathport.git" "master",
    dir := "Lean4Packages/mathbin"
  }]
