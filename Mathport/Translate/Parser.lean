/-
Copyright (c) 2021 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
import Std.Data.HashMap
import Mathport.Syntax

open Std (HashMap)
open Lean hiding Expr
open Lean.Elab Tactic

namespace Mathport
namespace Translate

open AST3

namespace Parser

structure Context where
  cmds : Array Command
  arr : Array (Spanned VMCall)

abbrev ParserM := ReaderT Context $ StateT Nat OptionM

def next : ParserM VMCall := fun s i =>
  if h : i < s.arr.size then pure ((s.arr.get ⟨i, h⟩).kind, i+1) else failure

def ident : ParserM Name := do let VMCall.ident n ← next | failure; n

def smallNat : ParserM Nat := do let VMCall.nat n ← next | failure; n

def pExpr : (pat :_:= false) → ParserM Expr
  | false => do let VMCall.expr e ← next | failure; e
  | true => do let VMCall.pat e ← next | failure; e

def itactic : ParserM AST3.Block := do let VMCall.block bl ← next | failure; bl

def commandLike : ParserM AST3.Command := do
  let VMCall.command (some i) ← next | failure; (← read).cmds[i]

def tk (tk : String) : ParserM Unit := do
  let VMCall.token t ← next | failure
  guard (tk = t)

partial def manyList (x : ParserM α) : ParserM (List α) :=
  (do (← x) :: (← manyList x)) <|> pure []

def many (x : ParserM α) : ParserM (Array α) := List.toArray <$> manyList x

scoped postfix:max "?" => optional
scoped postfix:max "*" => many

def sepByList (s : ParserM Unit) (p : ParserM α) : ParserM (List α) :=
  (do (← p) :: (← manyList (s *> p))) <|> pure []

def sepBy (s : ParserM Unit) (p : ParserM α) : ParserM (Array α) := List.toArray <$> sepByList s p

def brackets (l r) (p : ParserM α) := tk l *> p <* tk r
def listOf (p : ParserM α) := brackets "[" "]" $ sepBy (tk ",") p
def maybeListOf (p : ParserM α) := listOf p <|> do #[← p]
def ident_ := ident <|> tk "_" *> `_
def usingIdent := (tk "using" *> ident)?
def withIdentList := (tk "with" *> ident_*) <|> pure #[]
def withoutIdentList := (tk "without" *> ident*) <|> pure #[]

def Lean.Elab.Tactic.Location.ofOption (l : Array (Option Name)) : Location :=
  let (hs, ty) := l.foldl (init := (#[], false)) fun
    | (hs, ty), none => (hs, true)
    | (hs, ty), some n => (hs.push n, ty)
  Location.targets hs ty

open Lean.Elab.Tactic in
def location := (tk "at" *> (tk "*" *> pure Location.wildcard <|>
  (Location.ofOption <$> (((tk "⊢" <|> tk "|-") *> pure none) <|> some <$> ident)*))) <|>
  pure (Location.targets #[] true)

def pExprList := listOf pExpr
def optPExprList := listOf pExpr <|> pure #[]
def pExprListOrTExpr := maybeListOf pExpr
def onlyFlag := (tk "only" *> true) <|> pure false

def parseBinders : ParserM Binders := do let VMCall.binders bis ← next | failure; bis

def inductiveDecl : ParserM InductiveCmd := do
  let VMCall.inductive i ← next | failure
  let Command.inductive c ← (← read).cmds[i] | failure
  c

def renameArg : ParserM (Name × Name) := do (← ident, ← (tk "->")? *> ident)

def renameArgs : ParserM (Array (Name × Name)) :=
  (do #[← renameArg]) <|> listOf renameArg

structure RwRule where
  symm : Bool
  rule : Expr

def rwRule : ParserM RwRule := do
  pure ⟨Option.isSome (← (tk "←" <|> tk "<-")?), ← pExpr⟩

def rwRules : ParserM (Array RwRule) := maybeListOf rwRule

def generalizeArg : ParserM (Expr × Name) := do
  let AST3.Expr.app e rhs ← (← pExpr).unparen | failure
  let AST3.Expr.app _ lhs ← e.kind.unparen | failure
  let AST3.Expr.ident x ← rhs.kind.unparen | failure
  (lhs.kind, x)

def casesArg : ParserM (Option Name × Expr) := do
  let t ← pExpr
  match t.unparen with
  | AST3.Expr.ident x => (some x, ← tk ":" *> pExpr)
  | _ => (none, t)

def caseArg : ParserM (Array Name × Array Name) := do
  (← ident_*, (← (tk ":" *> ident_*)?).getD #[])

def case : ParserM (Array (Array Name × Array Name)) := maybeListOf caseArg

inductive SimpArg
| allHyps
| except (n : Name)
| expr (e : Expr)
| symmExpr (e : Expr)

def simpArg : ParserM SimpArg :=
  (tk "*" *> SimpArg.allHyps) <|>
  (tk "-" *> do SimpArg.except (← ident)) <|>
  (tk "<-" *> do SimpArg.symmExpr (← pExpr)) <|>
  do SimpArg.expr (← pExpr)

def simpArgList : ParserM (Array SimpArg) :=
  (tk "*" *> #[SimpArg.allHyps]) <|> listOf simpArg <|> pure #[]

end Parser
