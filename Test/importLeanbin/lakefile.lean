import Lake

open Lake DSL System

package importLeanbin where
  defaultFacet := PackageFacet.oleans
  dependencies := #[{
    name := "lean3port",
    src := Source.git "https://github.com/leanprover-community/lean3port.git" "master"
  }]
