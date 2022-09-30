/-
Copyright (c) 2021 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Daniel Selsam
-/
import Lean
import Mathport.Util.String

open Lean Lean.Json
open System (FilePath)

instance : FromJson FilePath where
  fromJson? json := do
    let s : String ← fromJson? json
    pure ⟨s⟩

instance : FromJson Position where
  fromJson?
    | Json.arr #[line, col] => return ⟨← fromJson? line, ← fromJson? col⟩
    | _ => throw "expected array with two elements"

instance : FromJson Unit := ⟨fun _ => pure ()⟩

instance {α : Type u} {β : Type v} [FromJson α] [FromJson β] : FromJson (Sum α β) :=
  ⟨fun j => (fromJson? j).map Sum.inl <|> (@fromJson? β _ j).map Sum.inr⟩

open Lean.Json in
instance [FromJson α] [BEq α] [Hashable α] : FromJson (Lean.HashSet α) where
  fromJson? json := do
    let Structured.arr elems ← fromJson? json | throw "JSON array expected"
    elems.foldlM (init := {}) fun acc x => return acc.insert (← fromJson? x)

open Lean.Json in
instance [FromJson α] [BEq α] [Hashable α] [FromJson β] : FromJson (Lean.HashMap α β) where
   fromJson? json := do
    let Structured.obj kvs ← fromJson? json | throw "JSON obj expected"
    kvs.foldM (init := {}) fun acc (k : String) v =>
      return acc.insert (← fromJson? k) (← fromJson? v)
