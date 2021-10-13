import Lake

open Lake DSL System

package mathport {
  dependencies := #[{
    name := "mathlib",
    -- FIXME use the main mathlib repository once it has a `lakefile.lean`.
    src := Source.git "https://github.com/semorrison/mathlib4.git" "lake" none,
    dir := FilePath.mk "."
  }],
  binRoot := `MathportApp
  moreLinkArgs :=
    if Platform.isWindows then
      #["-Wl,--export-all"]
    else
      #["-rdynamic"]
}
