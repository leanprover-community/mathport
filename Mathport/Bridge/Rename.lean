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

export Mathlib.Prelude.Rename (binportTag)

namespace Rename

variable (env : Environment)

-- For both binport and synport
def resolveIdent? (n3 : Name) (removeX : Bool) (choices : Array Name := #[]) :
    Option ((String × Name) × Name) :=
  if h : choices.size > 0 then
    getRenameMap env |>.find? choices[0] |>.map fun target =>
      (target, clean' (clipLike target.2 n3 choices[0]))
  else
    getRenameMap env |>.find? n3 |>.map fun target => (target, clean' target.2)
where
  clipLike target n3 orig :=
    if orig.getNumParts == target.getNumParts then
      componentsToName <| target.components.drop (target.getNumParts - n3.getNumParts)
    else target

  clean' s := if removeX then clean s else s

  clean
    | .anonymous => .anonymous
    | .str p s =>
      let s := if s.contains 'ₓ' then
        s.foldl (fun acc c => if c = 'ₓ' then acc else acc.push c) ""
      else s
      .str (clean p) s
    | .num p n => .num (clean p) n

  componentsToName
    | [] => Name.anonymous
    | (c::cs) => c ++ componentsToName cs

-- For synport only
def resolveIdentCore! (n3 : Name) (removeX : Bool) (choices : Array Name := #[]) : (String × Name) × Name :=
  resolveIdent? env n3 removeX choices |>.getD (("", choices.getD 0 n3), n3)

-- For both binport and synport
def resolveIdent! (n3 : Name) (removeX : Bool) (choices : Array Name := #[]) : Name :=
  (resolveIdentCore! env n3 removeX choices).2

-- For synport only
def getClashes (n4 : Name) : Name × List Name :=
  (getRenameMap env).toLean3.findD n4 (n4, [])

-- For synport only
-- TODO: better heuristic/binport index?
partial def renameNamespace (ns3 : Name) : Name :=
  match resolveIdent? env ns3 true with
  | some (_, ns4) => ns4
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
    | some (c::_) => Name.mkSimple $ s.convertSnake c.getString!.getCapsKind
    | _ => none
  | _ => none

end Rename

end Mathport
