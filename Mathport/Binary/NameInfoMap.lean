/-
Copyright (c) 2021 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Selsam
-/
import Lean
import Mathport.Util.Import

namespace Mathport.Binary

open Lean
open Std (HashMap)

inductive ClashKind
  | foundDefEq : ClashKind
  | freshDecl  : ClashKind
  deriving Inhabited, Repr, BEq, FromJson, ToJson

structure NameInfo where
  name4     : Name
  clashKind : ClashKind
  deriving Inhabited, Repr, FromJson, ToJson

abbrev NameInfoMap := HashMap Name NameInfo

def NameInfoMap.insertPair (m : NameInfoMap) : Name × NameInfo → NameInfoMap
  | (n3, n4) => m.insert n3 n4

initialize mathportRenameExtension : SimplePersistentEnvExtension (Name × NameInfo) NameInfoMap ←
  registerSimplePersistentEnvExtension {
    name          := `Mathport.renameMapExtension
    addEntryFn    := NameInfoMap.insertPair
    addImportedFn := fun es => mkStateFromImportedEntries (NameInfoMap.insertPair) {} es
  }

def getNameInfoMap (env : Environment) : NameInfoMap := do
  mathportRenameExtension.getState env

def addNameAlignmentCore (n3 : Name) (n4 : NameInfo) : CoreM Unit := do
  modifyEnv fun env => mathportRenameExtension.addEntry env (n3, n4)

def loadInitialAlignments (env : Environment) : Environment := do
    let x : StateM Environment Unit := do
      alignName `quot                `Quot
      alignName `quot.mk             `Quot.mk
      alignName `quot.lift           `Quot.lift
      alignName `quot.ind            `Quot.ind

      alignName `nat.add._main       `Nat.add
      alignName `nat.sub._main       `Nat.sub
      alignName `nat.neg._main       `Nat.neg
      alignName `nat.mul._main       `Nat.mul
      alignName `nat.div._main       `Nat.div
      alignName `nat.pred._main      `Nat.pred

      alignName `heq                 `HEq
      alignName `punit               `PUnit
      alignName `pprod               `PProd

      alignName `has_add             `Add
      alignName `has_sub             `Sub
      alignName `has_mul             `Mul
      alignName `has_div             `Div
      alignName `has_neg             `Neg
      alignName `has_mod             `Mod

      alignName `has_le              `LE
      alignName `has_lt              `LT
      alignName `has_beq             `BEq
      alignName `has_append          `Append
      alignName `has_sizeof          `SizeOf
      alignName `has_pure            `Pure
      alignName `has_bind            `Bind
      alignName `has_seq             `Seq
      alignName `has_seq_left        `SeqLeft
      alignName `has_seq_right       `SeqRight

      alignName `int.negSuccOfNat    `Int.negSucc

      -- TODO: this is a HACK to workaround issues when mapping inductive n1 -> n2 when n1 appears in n2 (and n2.rec)
      alignName `module              `ModuleS   (clashKind := ClashKind.freshDecl)
      alignName `algebra             `AlgebraS  (clashKind := ClashKind.freshDecl)
      alignName `comm_ring           `CommRingS (clashKind := ClashKind.freshDecl)
      alignName `group               `GroupS    (clashKind := ClashKind.freshDecl)
      alignName `monoid              `Monoid   (clashKind := ClashKind.freshDecl)

      alignName `Module              `ModuleCat   (clashKind := ClashKind.freshDecl)
      alignName `Algebra             `AlgebraCat  (clashKind := ClashKind.freshDecl)
      alignName `CommRing            `CommRingCat (clashKind := ClashKind.freshDecl)
      alignName `Group               `GroupCat    (clashKind := ClashKind.freshDecl)
      alignName `Mon                 `MonoidCat   (clashKind := ClashKind.freshDecl)

    (do x; get : StateM Environment Environment).run' env

where
  alignName (n3 n4 : Name) (clashKind : ClashKind := ClashKind.foundDefEq)  : StateM Environment Unit := do
    modify fun env => mathportRenameExtension.addEntry env (n3, ⟨n4, clashKind⟩)

namespace RenameExt

syntax (name := alignName) "#alignName " ident ident : command

open Lean.Elab
open Lean.Elab.Command

@[commandElab alignName] def elabAlignName : CommandElab := fun stx => do
  -- TODO: always assume they are foundDefEq?
  -- At the very least, confirm that we are checking this somewhere.
  liftCoreM $ addNameAlignmentCore stx[1].getId ⟨stx[2].getId, ClashKind.foundDefEq⟩

end RenameExt
end Mathport.Binary
