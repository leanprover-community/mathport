/-
Copyright (c) 2021 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Daniel Selsam
-/
import Mathport.Util

namespace Mathport

open Lean (Position)

structure Node3S (α : Type u) where
  start : Position
  end_ : Option Position
  kind  : α
  deriving Inhabited, Repr

def Node3S.map (f : α → β) : Node3S α → Node3S β
  | ⟨s, e, a⟩ => ⟨s, e, f a⟩

mutual

inductive Other3 : Type
  | mk : (kind : String) → (children : Array (Node3S Node3K)) → Other3
  deriving Inhabited, Repr

inductive Command3
  | «prelude» : Command3
  | other : Other3 → Command3
  deriving Inhabited, Repr

inductive Node3K
  | command : Command3 → Node3K
  | other : Other3 → Node3K
  deriving Inhabited, Repr

end

abbrev Node3 := Node3S Node3K

structure AST3 where
  commands : Array (Node3S Command3)
  deriving Inhabited, Repr

end Mathport
