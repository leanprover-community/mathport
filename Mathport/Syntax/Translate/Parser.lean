/-
Copyright (c) 2021 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
import Std.Data.HashMap
import Mathport.Syntax.AST3
import Mathport.Syntax.Prelude

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

def withInput (p : ParserM α) : ParserM (α × Nat) := do
  let VMCall.withInput arr n ← next | failure
  fun c i => do ((← p { c with arr } |>.run' 0, n), i)

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
  let AST3.Expr.notation (Choice.one `«expr = ») #[⟨_, _, Arg.expr lhs⟩, ⟨_, _, Arg.expr rhs⟩]
    ← (← pExpr).unparen | failure
  let AST3.Expr.ident x ← rhs.unparen | failure
  (lhs, x)

def casesArg : ParserM (Option Name × Expr) := do
  let t ← pExpr
  match t.unparen with
  | AST3.Expr.ident x => (do (some x, ← tk ":" *> pExpr)) <|> do (none, t)
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

inductive RCasesPat : Type
  | one : Name → RCasesPat
  | clear : RCasesPat
  | typed : RCasesPat → AST3.Expr → RCasesPat
  | tuple : Array RCasesPat → RCasesPat
  | alts : Array RCasesPat → RCasesPat
  deriving Inhabited

def RCasesPat.alts' : Array RCasesPat → RCasesPat
| #[p] => p
| ps => alts ps

mutual

partial def rcasesPat : Bool → ParserM RCasesPat
| true =>
  (brackets "(" ")" (rcasesPat false)) <|>
  (RCasesPat.tuple <$> brackets "⟨" "⟩" (sepBy (tk ",") (rcasesPat false))) <|>
  (tk "-" *> RCasesPat.clear) <|>
  (RCasesPat.one <$> ident_)
| false => do
  let pat ← RCasesPat.alts' <$> rcasesPatList
  (tk ":" *> pat.typed <$> pExpr) <|> pure pat

partial def rcasesPatList (pats : Array RCasesPat := #[]) : ParserM (Array RCasesPat) := do
  pats.push (← rcasesPat true) |> rcasesPatListRest

partial def rcasesPatListRest (pats : Array RCasesPat) : ParserM (Array RCasesPat) :=
  (tk "|" *> rcasesPatList pats) <|>
  -- hack to support `-|-` patterns, because `|-` is a token
  (tk "|-" *> rcasesPatListRest (pats.push RCasesPat.clear)) <|>
  pure pats

end

inductive RCasesArgs
  | hint (tgt : Sum AST3.Expr (Array AST3.Expr)) (depth : Option ℕ)
  | rcases (name : Option Name) (tgt : AST3.Expr) (pat : RCasesPat)
  | rcasesMany (tgt : Array AST3.Expr) (pat : RCasesPat)

def rcasesArgs : ParserM RCasesArgs := do
  let hint ← (tk "?")?
  let p ← (Sum.inr <$> brackets "⟨" "⟩" (sepBy (tk ",") pExpr)) <|>
          (Sum.inl <$> pExpr)
  match hint with
  | none => do
    let p ← (do
      let Sum.inl t ← p | failure
      let AST3.Expr.ident h ← t.unparen | failure
      Sum.inl (h, ← tk ":" *> pExpr)) <|>
      pure (Sum.inr p)
    let ids ← (tk "with" *> rcasesPat false)?
    let ids := ids.getD (RCasesPat.tuple #[])
    pure $ match p with
    | Sum.inl (name, tgt) => RCasesArgs.rcases (some name) tgt ids
    | Sum.inr (Sum.inl tgt) => RCasesArgs.rcases none tgt ids
    | Sum.inr (Sum.inr tgts) => RCasesArgs.rcasesMany tgts ids
  | some _ => do
    let depth ← (tk ":" *> smallNat)?
    pure $ RCasesArgs.hint p depth


inductive RIntroPat : Type
  | one : RCasesPat → RIntroPat
  | binder : Array RIntroPat → Option AST3.Expr → RIntroPat
  | pat : RCasesPat → Option AST3.Expr → RIntroPat
  deriving Inhabited

mutual

partial def rintroPatHi : ParserM RIntroPat :=
  brackets "(" ")" rintroPat <|> RIntroPat.one <$> rcasesPat true

partial def rintroPat : ParserM RIntroPat := do
  let f ← match ← rintroPatHi* with
  | #[] => failure
  | #[RIntroPat.one pat] => do
    RIntroPat.pat $ RCasesPat.alts' (← rcasesPatListRest #[pat])
  | pats => RIntroPat.binder pats
  f $ ← (tk ":" *> pExpr)?

end

/-- Syntax for a `rintro` patern: `('?' (: n)?) | rintro_pat`. -/
def rintroArg : ParserM (Sum (Array RIntroPat × Option AST3.Expr) (Option ℕ)) :=
(tk "?" *> Sum.inr <$> (tk ":" *> smallNat)?) <|>
do Sum.inl (← rintroPatHi*, ← (tk ":" *> pExpr)?)

/-- Parses `patt? (: expr)? (:= expr)?`, the arguments for `obtain`.
 (This is almost the same as `rcasesPat false`,
but it allows the pattern part to be empty.) -/
def obtainArg :
  ParserM ((Option RCasesPat × Option AST3.Expr) × Option (Array AST3.Expr)) := do
  let (pat, tp) ←
    (do pure $ match ← rcasesPat false with
      | RCasesPat.typed pat tp => (some pat, some tp)
      | pat => (some pat, none)) <|>
    (do (none, ← (tk ":" *> pExpr)?))
  ((pat, tp), ← (tk ":=" *> do
    (guard tp.isNone *> brackets "⟨" "⟩" (sepBy (tk ",") pExpr)) <|>
    (do #[← pExpr]))?)

end Parser
