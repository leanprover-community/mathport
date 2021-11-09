import Lake

open Lake DSL System

package mathport {
  dependencies := #[{
    name := "mathlib",
    -- We point to a particular commit in mathlib4,
    -- as changes to tactics in mathlib4 may cause breakages here,
    src := Source.git "https://github.com/leanprover-community/mathlib4.git" "d4ec6b4717e21193fee95da3b94c089123a4bc3b",
    dir := FilePath.mk "."
  }],
  binRoot := `MathportApp
  moreLinkArgs := if Platform.isWindows then #[] else #["-rdynamic"]
}
