/-
Copyright (c) 2021 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Daniel Selsam
-/
import Lean
import Std.Data.RBMap
import Mathport.Util.String

open Lean Lean.Json
open System (FilePath)

instance : FromJson FilePath where
  fromJson? json := do
    let s : String ← fromJson? json
    pure ⟨s⟩

instance : FromJson Position where
  fromJson?
  | Json.arr a => do
    unless a.size = 2 do throw "expected an array with two elements"
    pure ⟨← fromJson? a[0], ← fromJson? a[1]⟩
  | _ => throw "JSON array expected"

instance : ToJson Name where
  toJson n :=
    let rec core
      | Name.str p s .. => toJson s :: core p
      | Name.num p k .. => toJson k :: core p
      | _ => []
    Json.arr (core n).toArray

instance : FromJson Name where
  fromJson?
  | Json.null => Name.anonymous
  | Json.str s => s.toName
  | Json.arr a => a.foldlM (init := Name.anonymous) fun
    | n, (i : Nat) => n.mkNum i
    | n, (s : String) => n.mkStr s
    | _, _ => throw "JSON string expected"
  | _ => throw "JSON array expected"

instance : FromJson Unit := ⟨fun _ => ()⟩

instance {α : Type u} {β : Type v} [FromJson α] [FromJson β] : FromJson (Sum α β) :=
  ⟨fun j => (fromJson? j).map Sum.inl <|> (@fromJson? β _ j).map Sum.inr⟩

open Lean.Json in
instance [FromJson α] [BEq α] [Hashable α] : FromJson (Std.HashSet α) where
  fromJson? json := do
    let Structured.arr elems ← fromJson? json | throw "JSON array expected"
    elems.foldlM (init := {}) fun acc x => do acc.insert (← fromJson? x)

open Lean.Json in
instance [FromJson β] : FromJson (Std.HashMap String β) where
  fromJson? json := do
    let Structured.obj kvs ← fromJson? json | throw "JSON array expected"
    kvs.foldM (init := {}) fun acc k v => do acc.insert k (← fromJson? v)

open Lean.Json in
instance [FromJson β] : FromJson (Std.HashMap Name β) where
  fromJson? json := do
    let Structured.obj kvs ← fromJson? json | throw "JSON obj expected"
    kvs.foldM (init := {}) fun acc (k : String) v => do acc.insert k.toName (← fromJson? v)

open Lean.Json in
open Std (RBNode) in
instance [ToJson β] : ToJson (Std.HashMap Name β) where
  toJson map := do
    let obj := Structured.obj $ map.fold (init := RBNode.leaf) fun kvs k v =>
      kvs.insert String.cmp (toString k) (toJson v)
    toJson obj
