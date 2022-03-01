/-
Copyright (c) 2021 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Selsam
-/
import Lean
import Mathlib.Mathport.Rename
import Mathport.Util.Misc
import Mathport.Util.Name
import Mathport.Util.String
import Mathport.Util.Import
import Mathport.Util.Json
import Mathport.Util.Parse

namespace Mathport

open Lean
open System (FilePath)
open Std (HashMap)
open Mathlib.Prelude.Rename

-- During synport, we need to guess how to capitalize a field name without knowing
-- the complete name. As a heuristic, we store a map from last-component-of-lean3-name
-- to all the lean4 names with that last component. When queried on a new field name,
-- if all in a bucket agree, we use that style for it.
abbrev FieldNameMap := HashMap String (List Name)

def FieldNameMap.insert (m : FieldNameMap) : Name × Name → FieldNameMap
  | ⟨n3, n4⟩ => if n3.isStr then m.insertWith List.append n3.getString! [n4] else m

initialize mathportFieldNameExtension : SimplePersistentEnvExtension (Name × Name) FieldNameMap ←
  registerSimplePersistentEnvExtension {
    name          := `Mathport.fieldNameExtension
    addEntryFn    := FieldNameMap.insert
    addImportedFn := fun es => mkStateFromImportedEntries FieldNameMap.insert {} es
  }

def getFieldNameMap (env : Environment) : FieldNameMap :=
  mathportFieldNameExtension.getState env

def addPossibleFieldName (n3 n4 : Name) : CoreM Unit := do
  modifyEnv fun env => mathportFieldNameExtension.addEntry env (n3, n4)

namespace Rename

variable (env : Environment)

-- For both binport and synport
def resolveIdent? (n3 : Name) (choices : Array Name := #[]) : Option Name :=
  if choices.isEmpty then
    getRenameMap env |>.find? n3
  else
    match getRenameMap env |>.find? choices[0] with
    | none => none
    | some target => clipLike target n3
where
  clipLike target n3 :=
    some <| componentsToName <| target.components.drop (target.getNumParts - n3.getNumParts)

  componentsToName
    | [] => Name.anonymous
    | (c::cs) => c ++ componentsToName cs

-- For both binport and synport
def resolveIdent! (n3 : Name) (choices : Array Name := #[]) : Name :=
  resolveIdent? env n3 choices |>.getD n3

-- For synport only
-- TODO: better heuristic/binport index?
partial def renameNamespace (ns3 : Name) : Name :=
  match resolveIdent? env ns3 with
  | some ns4 => ns4
  | none =>
    match ns3 with
    | Name.str p s .. => renameNamespace p |>.mkStr s.snake2pascal
    | Name.num p k .. => renameNamespace p |>.mkNum k
    | Name.anonymous  => Name.anonymous

-- For synport only
def renameAttr (n : Name) : Name :=
  n

-- For synport only
def renameField? (n : Name) : Option Name :=
  match n with
  | Name.str Name.anonymous s .. =>
    match getFieldNameMap env |>.find? s with
    | some (c::cs) => Name.mkSimple $ s.convertSnake c.getString!.getCapsKind
    | _ => none
  | _ => none

end Rename

end Mathport
