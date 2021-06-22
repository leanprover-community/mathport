/-
Copyright (c) 2021 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Daniel Selsam
-/
import Mathport.Util
import Mathport.AST3

namespace Mathport

open Lean (Json FromJson Position)
open Lean.FromJson (fromJson?)

namespace Parse

abbrev AstId := Nat
abbrev Tag   := Option AstId

structure RawNode3 where
  id       : Nat
  start    : Position
  «end»    : Option Position
  kind     : String
  children : Array Nat
  deriving FromJson

structure RawAST3 where
  ast      : Array RawNode3
  commands : Array Nat
  -- pexpr    : Array RawPExpr
  -- expr     : Array RawExpr
  deriving FromJson

private def RawAST3.toAST3 (rast3 : RawAST3) : AST3 := do
  let ϕ (rnode3 : RawNode3) : StateM (HashMap AstId Node3) Node3 := do
    let s ← get
    let children ← rnode3.children.mapM fun id => s.find! id
    let node := Node3.node children
    modify fun s => s.insert rnode3.id node
    node
  let ψ : StateM (HashMap AstId Node3) AST3 := do
    let nodes ← rast3.ast.mapM ϕ
    pure { asts := nodes, commands := rast3.commands }
  ψ.run' {}

end Parse

def parseAST3 (filename : System.FilePath) : IO AST3 := do
  println! "Reading {filename}..."
  let s ← IO.FS.readFile filename
  println! "Parsing Json..."
  match Json.parse s with
  | Except.error err => throw $ IO.userError err
  | Except.ok json   =>
    println! "Decoding RawAST3..."
    match (fromJson? json : Except String Parse.RawAST3) with
    | Except.error err => throw $ IO.userError err
    | Except.ok rawAST3 =>
      println! "Converting RawAST3 to AST3..."
      let ast : AST3 := rawAST3.toAST3
      pure ast

end Mathport
