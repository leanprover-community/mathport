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

namespace Mathport.Binary

open Lean Lean.Json
open Std (HashMap HashSet)

instance [FromJson β] : FromJson (Std.HashMap Name β) where
  fromJson? json := do
    let Structured.obj kvs ← fromJson? json | throw "JSON obj expected"
    kvs.foldM (init := {}) fun acc (k : String) v => do acc.insert k.toName (← fromJson? v)

structure Config where
  customAligns      : HashMap Name Name := {}
  disabledInstances : HashSet Name := {}
  sorries           : HashSet Name := {}
  neverSorries      : HashSet Name := {}
  skipProofs        : Bool := false
  deriving FromJson

end Mathport.Binary
