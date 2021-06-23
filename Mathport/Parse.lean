/-
Copyright (c) 2021 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Daniel Selsam
-/
import Mathport.Util
import Mathport.AST3

namespace Mathport

open Lean (Json FromJson Position Name)
open Lean.FromJson (fromJson?)

namespace Parse

abbrev AstId := Nat
abbrev Tag   := Option AstId

structure RawNode3 where
  start    : Position
  «end»    : Option Position
  kind     : String
  value    : Name
  children : Option (Array AstId)
  deriving FromJson, Repr

structure RawAST3 where
  ast      : Array (Option RawNode3)
  commands : Array AstId
  -- pexpr    : Array RawPExpr
  -- expr     : Array RawExpr
  deriving FromJson

abbrev M := ReaderT (Array (Option RawNode3)) $ StateT (HashMap AstId Node3) $ Except String

def getRaw (i : AstId) : M RawNode3 := do
  match (← read)[i] with
  | some a => a
  | none => throw "missing node"

def getRaw? (i : AstId) : M (Option RawNode3) := do
  if i = 0 then pure none else some <$> getRaw i

def withRaw'
  (mk : Node3 → α → M β)
  (f : α → Node3K) (g : Node3 → Option α)
  (m : String → Array AstId → M α)
  (i : AstId) : M β := do
  match (← get).find? i with
  | some n => match g n with
    | some k => mk n k
    | none => throw "type error"
  | none =>
    let r ← getRaw i
    let a ← m r.kind (r.children.getD #[])
    let n := { start := r.start, end_ := r.«end», kind := f a }
    modify fun s => s.insert i n
    mk n a

def withRawK (f : α → Node3K) (g : Node3K → Option α) (m : String → Array AstId → M α) (i : AstId) : M α := do
  withRaw' (fun _ => pure) f (fun n => g n.kind) m i

def withRaw (f : α → Node3K) (g : Node3K → Option α) (m : String → Array AstId → M α) (i : AstId) : M (Node3S α) := do
  withRaw' (fun n a => n.map fun _ => a) f (fun n => g n.kind) m i

mutual

partial def getNode (i : AstId) : M Node3 := do
  withRaw' (fun n _ => n) id (fun n => some n.kind) (fun k c => Node3K.other <$> mkOther k c) i

partial def mkOther (k : String) (c : Array AstId) : M Other3 := Other3.mk k <$> c.mapM getNode

end

open Command3 in
def getCommand : AstId → M (Node3S Command3) :=
  withRaw Node3K.command (fun | Node3K.command c => some c | _ => none) aux
where
  aux : String → Array AstId → M Command3
  | "prelude", _ => «prelude»
  | k, args => other <$> mkOther k args

def RawAST3.toAST3 : RawAST3 → Except String AST3
| ⟨ast, commands⟩ => commands.mapM getCommand |>.run ast |>.run' {} |>.map AST3.mk

end Parse

def parseAST3 (filename : System.FilePath) : IO AST3 := do
  println! "Reading {filename}..."
  let s ← IO.FS.readFile filename
  println! "Parsing Json..."
  let json ← Json.parse s
  println! "Decoding RawAST3..."
  let rawAST3 ← fromJson? json (α := Parse.RawAST3)
  println! "Converting RawAST3 to AST3..."
  rawAST3.toAST3
