/-
Copyright (c) 2021 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Daniel Selsam
-/
import Mathport.Util

namespace Mathport

inductive Node3 where
  | node : Array Node3 → Node3
  deriving Inhabited, Repr

structure AST3 where
  asts     : Array Node3
  commands : Array Nat
  deriving Inhabited, Repr

end Mathport
