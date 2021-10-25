import Lake

open Lake DSL System

package mathport {
  dependencies := #[{
    name := "mathlib",
    -- We point to a particular commit in mathlib4,
    -- as changes to tactics in mathlib4 often cause breakages here,
    -- particularly in `Mathport/Syntax/Translate/Tactic/Mathlib.lean`.
    -- We'll need to keep updating that file, and bumping the commit here.
    src := Source.git "https://github.com/leanprover-community/mathlib4.git" "fad6b41b420d25d84e43c044e4433d6dced42a61",
    dir := FilePath.mk "."
  }],
  binRoot := `MathportApp
  moreLinkArgs :=
    if Platform.isWindows then
      #[]
    else
      #["-rdynamic"]
}
