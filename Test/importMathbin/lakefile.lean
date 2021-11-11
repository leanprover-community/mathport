import Lake

open Lake DSL System

package importLeanbin where
  defaultFacet := PackageFacet.oleans
  dependencies := #[{
    name := "mathbin",
    src := Source.git "https://github.com/dselsam/mathport.git" "master",
    dir := "Lean4Packages/mathbin"
  }]
