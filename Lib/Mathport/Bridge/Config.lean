/-
Copyright (c) 2021 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Selsam
-/
import Lean
import Std.Data.HashMap
import Std.Data.HashSet
import Std.Data.RBMap
import Mathport.Util.Misc
import Mathport.Util.Json
import Mathport.Bridge.Path

namespace Mathport

open Lean Lean.Json
open Std (HashMap HashSet)

structure Config where
  pathConfig         : Path.Config
  defEqConstructions : HashSet String := {}
  forceAbbrevs       : HashSet Name := {}
  stringsToKeep      : HashSet Name := {}
  disabledInstances  : HashSet Name := {}
  neverSorries       : HashSet Name := {}
  sorries            : HashSet Name := {}
  skipProofs         : Bool := false
  parallel           : Bool := true
  error2warning      : Bool := false
  deriving FromJson

end Mathport
