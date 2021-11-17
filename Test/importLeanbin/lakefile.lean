import Lake

open Lake DSL System

package importLeanbin where
  defaultFacet := PackageFacet.oleans
  dependencies := #[{
    name := "leanbin",
    src := Source.git "https://github.com/leanprover-community/mathport.git" "master",
    dir := "Lean4Packages/leanbin"
  }]
