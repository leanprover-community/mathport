/-
Copyright (c) 2021 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Selsam
-/
import Lean
import Mathport.Util.Misc
import Mathport.Util.Json
import Mathport.Bridge.Path

namespace Mathport

open Lean Lean.Json

/-- Controls the way that translated definitions are displayed
when a lean 4 definition already exists. -/
inductive ReplacementStyle where
  /-- Completely skip the mathport output. Good for pruning an already ported file. -/
  | skip
  /-- Show a `#print` command pointing at the lean 4 declaration,
  and then print the mathport output in a comment. Useful when we want to recover
  the mathport output without re-running the program in case the alignment is erroneous. -/
  | comment
  /-- Ignore existing lean 4 definitions and just print all mathport outputs.
  Will cause redefinition errors. -/
  | keep
  deriving FromJson, Inhabited

structure Config where
  pathConfig         : Path.Config
  commitInfo         : Option String := none
  baseModules        : Array Name := #[`Mathlib]
  extraModules       : Array Name := #[]
  defEqConstructions : HashSet String := {}
  forceAbbrevs       : HashSet Name := {}
  stringsToKeep      : HashSet Name := {}
  disabledInstances  : HashSet Name := {}
  neverSorries       : HashSet Name := {}
  sorries            : HashSet Name := {}
  skipProofs         : Bool := false
  skipDefEq          : Bool := true
  error2warning      : Bool := false
  replacementStyle   : ReplacementStyle := .comment
  redundantAlign     : Bool := true
  deriving FromJson, Inhabited


end Mathport
