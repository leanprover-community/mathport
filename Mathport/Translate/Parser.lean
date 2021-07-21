/-
Copyright (c) 2021 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
import Std.Data.HashMap
import Mathport.Data4
import Mathport.AST3

open Std (HashMap)
open Lean Elab Tactic

namespace Mathport
namespace Translate

open AST3

namespace Parser

structure Context where
  cmds : Array Command
  arr : Array VMCall

abbrev ParserM := ReaderT Context $ StateT Nat OptionM

def next : ParserM VMCall := fun s i =>
  if h : i < s.arr.size then pure (s.arr.get ⟨i, h⟩, i+1) else failure

def ident : ParserM Name := do let VMCall.ident n ← next | failure; n

def smallNat : ParserM Nat := do let VMCall.nat n ← next | failure; n

def pExpr : (pat :_:= false) → ParserM AST3.Expr
  | false => do let VMCall.expr e ← next | failure; e
  | true => do let VMCall.pat e ← next | failure; e

def itactic : ParserM AST3.Block := do let VMCall.block bl ← next | failure; bl

def commandLike : ParserM AST3.Command := do
  let VMCall.command (some i) ← next | failure; (← read).cmds[i]

def tk (tk : String) : ParserM Unit := do
  let VMCall.token t ← next | failure
  guard (tk = t)

partial def many (x : ParserM α) : ParserM (List α) :=
  (do (← x) :: (← many x)) <|> pure []

local postfix "?" => optional
local postfix "*" => many

def sepBy (s : ParserM Unit) (p : ParserM α) : ParserM (List α) :=
  (do (← p) :: (← (s *> p)*)) <|> pure []

def brackets (l r) (p : ParserM α) := tk l *> p <* tk r
def listOf (p : ParserM α) := brackets "[" "]" $ sepBy (tk ",") p
def ident_ := ident <|> tk "_" *> `_
def usingIdent := (tk "using" *> ident)?
def withIdentList := (tk "with" *> ident_*) <|> pure []
def withoutIdentList := (tk "without" *> ident*) <|> pure []

def Lean.Elab.Tactic.Location.ofOption (l : List (Option Name)) : Location :=
  let (hs, ty) := l.foldl (init := (#[], false)) fun
    | (hs, ty), none => (hs, true)
    | (hs, ty), some n => (hs.push n, ty)
  Location.targets hs ty

open Lean.Elab.Tactic in
def location := (tk "at" *> (tk "*" *> pure Location.wildcard <|>
  (Location.ofOption <$> (((tk "⊢" <|> tk "|-") *> pure none) <|> some <$> ident)*))) <|>
  pure (Location.targets #[] true)

def pExprList := listOf pExpr
def optPExprList := listOf pExpr <|> pure []
def pExprListOrTExpr := listOf pExpr <|> (do [← pExpr])
def onlyFlag := (tk "only" *> true) <|> pure false

def parseBinders : ParserM Binders := do let VMCall.binders bis ← next | failure; bis

def inductiveDecl : ParserM InductiveCmd := do
  let VMCall.inductive i ← next | failure
  let Command.inductive c ← (← read).cmds[i] | failure
  c

end Parser
