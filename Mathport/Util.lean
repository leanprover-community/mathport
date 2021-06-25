/-
Copyright (c) 2021 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Daniel Selsam
-/
import Lean
import Std.Data.HashMap
import Std.Data.RBMap

namespace Lean

deriving instance Hashable for Position

instance : FromJson Position where
  fromJson?
  | Json.arr a => do
    unless a.size = 2 do throw "expected an array with two elements"
    pure ⟨← fromJson? a[0], ← fromJson? a[1]⟩
  | _ => throw "JSON array expected"

instance : FromJson Name where
  fromJson?
  | Json.null => Name.anonymous
  | Json.str s => s
  | Json.arr a => a.foldrM (init := Name.anonymous) fun
    | (i : Nat), n => n.mkNum i
    | (s : String), n => n.mkStr s
    | _, _ => throw "JSON string expected"
  | _ => throw "JSON array expected"

def dummyFileMap : FileMap := ⟨"", #[0], #[1]⟩

end Lean

export Std (HashSet HashMap RBMap RBNode)
export System (FilePath)

instance : MonadLift (Except String) IO where
  monadLift
  | _, Except.error err => throw $ IO.userError err
  | _, Except.ok x => pure x

@[macroInline] def assert {m : Type → Type v} [Pure m] [MonadExcept ε m]
  (p : Prop) [Decidable p] (e : ε) : m Unit :=
  if p then pure () else throw e

def Subarray.getOp {α : Type u} [Inhabited α] (self : Subarray α) (idx : Nat) : α :=
  let i := idx + self.start
  if i < self.stop then self.as[i] else arbitrary

@[inline] def Std.Format.parenPrec (p prec : Nat) (f : Format) :=
  if prec >= p then paren f else f

instance : Coe (Array α) (Subarray α) := ⟨(·[0:])⟩
