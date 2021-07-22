/-
Copyright (c) 2021 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Daniel Selsam
-/
import Lean

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

instance : FromJson Name where
  fromJson?
  | Json.null => Name.anonymous
  | Json.str s => s
  | Json.arr a => a.foldrM (init := Name.anonymous) fun
    | (i : Nat), n => n.mkNum i
    | (s : String), n => n.mkStr s
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
