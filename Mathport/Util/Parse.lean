/-
Copyright (c) 2021 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Selsam
-/
import Lean

def parseNat (s : String) : IO Nat :=
  match s.toNat? with
  | some k => pure k
  | none   => throw $ IO.userError s!"String '{s}' cannot be converted to Nat"

def parseBool (s : String) : IO Bool :=
  match s.toNat? with
  | some k =>
    if k == 1 then true
    else if k == 0 then false
    else throw $ IO.userError s!"String '{s}' cannot be converted to Bool"
  | none => throw $ IO.userError s!"String '{s}' cannot be converted to Bool"

open Lean Lean.Json in
open System (FilePath) in
def parseJsonFile (α : Type) [FromJson α] (filePath : FilePath) : IO α := do
  let s ← IO.FS.readFile filePath
  match Json.parse s with
  | Except.error err => throw $ IO.userError s!"Error parsing JSON: {err}"
  | Except.ok json   =>
    match fromJson? json with
    | Except.error err => throw $ IO.userError s!"Error decoding JSON: {err}"
    | Except.ok x      => pure x
