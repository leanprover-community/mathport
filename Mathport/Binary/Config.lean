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
import Mathport.Binary.Path

namespace Mathport.Binary

open Lean Lean.Json
open Std (HashMap HashSet)

structure Config where
  outRoot            : FilePath
  modules            : HashMap String FilePath := {}
  defEqConstructions : HashSet String := {}
  stringsToKeep      : HashSet Name := {}
  initialAlignments  : HashMap Name Name := {}
  disabledInstances  : HashSet Name := {}
  neverSorries       : HashSet Name := {}
  sorries            : HashSet Name := {}
  skipProofs         : Bool := false
  deriving FromJson

end Mathport.Binary
