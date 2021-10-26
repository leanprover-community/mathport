import Lake

open Lake DSL System

package mathport {
  dependencies := #[{
    name := "mathlib",
    -- We point to a particular commit in mathlib4,
    -- as changes to tactics in mathlib4 often cause breakages here,
    -- particularly in `Mathport/Syntax/Translate/Tactic/Mathlib.lean`.
    -- We'll need to keep updating that file, and bumping the commit here.
    src := Source.git "https://github.com/semorrison/mathlib4.git" "2a4bee350dcb2dfb0203974d7bc0b068199b60b0",
    dir := FilePath.mk "."
  }],
  binRoot := `MathportApp
  moreLinkArgs :=
    if Platform.isWindows then
      #["-Wl,--export-all"]
    else
      #["-rdynamic"]
}
