import Lake

open Lake DSL System

package importLean where
  defaultFacet := PackageFacet.oleans

  dependencies := #[{
    name := "leanbin",
    src := Source.path (FilePath.mk "../../Lib4/leanbin")
  }]

