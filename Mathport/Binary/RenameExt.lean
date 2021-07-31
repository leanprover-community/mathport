/-
Copyright (c) 2021 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Selsam
-/
import Lean
import Mathport.Util.Import
import Mathport.Util.Json
import Mathport.Util.Parse
import Mathport.Binary.Basic
import Mathport.Binary.Config

namespace Mathport.Binary

open Lean
open Std (HashMap)

abbrev RenameMap := HashMap Name Name

def RenameMap.insertPair (m : RenameMap) : Name × Name → RenameMap
  | (n3, n4) => m.insert n3 n4

initialize mathportRenameExtension : SimplePersistentEnvExtension (Name × Name) RenameMap ←
  registerSimplePersistentEnvExtension {
    name          := `Mathport.renameMapExtension
    addEntryFn    := RenameMap.insertPair
    addImportedFn := fun es => mkStateFromImportedEntries (RenameMap.insertPair) {} es
  }

def getRenameMap (env : Environment) : RenameMap := do
  mathportRenameExtension.getState env

def addNameAlignmentCore (n3 n4 : Name) : CoreM Unit := do
  modifyEnv fun env => mathportRenameExtension.addEntry env (n3, n4)

def addNameAlignment (n3 n4 : Name) : BinportM Unit := do
  liftCoreM <| addNameAlignmentCore n3 n4

def lookupNameExt (n3 : Name) : BinportM (Option Name) := do
  getRenameMap (← getEnv) |>.find? n3

def lookupNameExt! (n3 : Name) : BinportM Name := do
  match ← lookupNameExt n3 with
  | some n4 => pure n4
  | none    => throwError "name not found: '{n3}'"

def INITIAL_NAME_ALIGNMENTS_PATH : FilePath := ⟨"Config/initial_name_alignments.json"⟩

def addInitialNameAlignments (env : Environment) : IO Environment := do
  let alignments ← parseJsonFile (HashMap Name Name) INITIAL_NAME_ALIGNMENTS_PATH
  let x : StateM Environment Environment := do
    for (n3, n4) in alignments.toList do
      modify fun env => mathportRenameExtension.addEntry env (n3, n4)
    get
  pure $ x.run' env

namespace Translate

open Lean.Elab Lean.Elab.Command

syntax (name := translate) "#translate " ident : command

@[commandElab translate] def elabTranslate : CommandElab
  | `(#translate%$tk $id:ident) => do
    let name := id.getId
    match getRenameMap (← getEnv) |>.find? name with
    | none => logInfoAt tk "name `{name} not found"
    | some name4 => logInfoAt tk "`{name} ==> `{name4}"
  | _ => throwUnsupportedSyntax

end Translate

end Mathport.Binary
