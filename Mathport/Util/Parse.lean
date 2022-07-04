/-
Copyright (c) 2021 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Selsam
-/
import Lean

open Lean
open System (FilePath)

def parseNat (s : String) : IO Nat :=
  match s.toNat? with
  | some k => pure k
  | none   => throw $ IO.userError s!"String '{s}' cannot be converted to Nat"

def parseBool (s : String) : IO Bool :=
  match s.toNat? with
  | some 1 => pure true
  | some 0 => pure false
  | _ => throw $ IO.userError s!"String '{s}' cannot be converted to Bool"

open Lean.Json in
def parseJsonFile (α : Type) [FromJson α] (filePath : FilePath) : IO α := do
  let s ← IO.FS.readFile filePath
  match Json.parse s with
  | Except.error err => throw $ IO.userError s!"Error parsing JSON: {err}"
  | Except.ok json   =>
    match fromJson? json with
    | Except.error err => throw $ IO.userError s!"Error decoding JSON: {err}"
    | Except.ok x      => pure x

def parseTLeanImports (tlean : FilePath) : IO (Array Name) := do
  let line ← IO.FS.withFile tlean IO.FS.Mode.read fun h => h.getLine
  let tokens := line.trim.splitOn " " |>.toArray
  let nImports := tokens[1]!.toNat!
  let mut paths := #[]
  for i in [:nImports] do
    if tokens[2+2*i+1]! ≠ "-1" then throw $ IO.userError "found relative import!"
    paths := paths.push $ tokens[2+2*i]!.toName
  return paths
