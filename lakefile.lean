import Lake

open Lake DSL System

package mathport {
  dependencies := #[{
    name := "mathlib",
    -- We point to a particular commit in mathlib4,
    -- as changes to tactics in mathlib4 often cause breakages here,
    -- particularly in `Mathport/Syntax/Translate/Tactic/Mathlib.lean`.
    -- We'll need to keep updating that file, and bumping the commit here.
    -- TODO: this currently points to dselsam due to one tiny commit
     src := Source.git "https://github.com/dselsam/mathlib4.git" "5366ff9252f9001fc10e610795efd259fd4b8dc6"
  }],
  binRoot := `MathportApp
  moreLinkArgs := if Platform.isWindows then #[] else #["-rdynamic"]
}
