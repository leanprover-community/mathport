/-
Copyright (c) 2021 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
import Mathport.Syntax.AST3
import Mathlib.Mathport.Syntax

open Lean hiding Expr Command
open Lean.Elab Tactic

namespace Mathport
namespace Translate

open AST3

namespace Parser

structure Context where
  cmds : Array Command
  arr : Array (Spanned VMCall)

abbrev ParserM := ReaderT Context $ StateT Nat Option

def ParserM.run (p : ParserM α) (ctx : Context) : Except String α := do
  match (p ctx).run 0 with
  | none => Except.error "parse error"
  | some (a, i) => if i = ctx.arr.size then Except.ok a else Except.error "too many args"

def next : ParserM (Spanned VMCall) := fun s i =>
  if h : i < s.arr.size then pure ((s.arr.get ⟨i, h⟩), i+1) else failure

def ident : ParserM Name := do let ⟨_, VMCall.ident n⟩ ← next | {failure}; pure n

def smallNat : ParserM Nat := do let ⟨_, VMCall.nat n⟩ ← next | {failure}; pure n

def pExpr : (pat :_:= false) → ParserM (Spanned Expr)
  | false => do let ⟨m, VMCall.expr e⟩ ← next | {failure}; pure ⟨m, e⟩
  | true => do let ⟨m, VMCall.pat e⟩ ← next | {failure}; pure ⟨m, e⟩

def itactic : ParserM AST3.Block := do let ⟨_, VMCall.block bl⟩ ← next | {failure}; pure bl

def commandLike? : ParserM (Option (Spanned AST3.Command)) := do
  let ⟨m, VMCall.command i⟩ ← next | failure
  i.mapM fun i => return ⟨m, (← read).cmds[i]!⟩

def commandLike : ParserM (Spanned AST3.Command) := do
  let some i ← commandLike? | {failure}; pure i

def skipAll : ParserM Unit := do set (← read).arr.size

def withInput (p : ParserM α) : ParserM (α × Nat) := do
  let ⟨_, VMCall.withInput arr n⟩ ← next | failure
  fun c i => return ((← p { c with arr } |>.run' 0, n), i)

def emittedCommandHere : ParserM (Option Command) := return (← withInput commandLike?).1.map (·.kind)

partial def emittedCodeHere : ParserM (Array Command) := aux #[]
where
  aux (out : Array Command) : ParserM (Array Command) := do
    match ← emittedCommandHere <|> pure none with
    | none => pure out
    | some c => aux (out.push c)

def tk (tk : String) : ParserM Unit := do
  let ⟨_, VMCall.token t⟩ ← next | failure
  guard (tk = t)

partial def manyList (x : ParserM α) : ParserM (List α) :=
  (return (← x) :: (← manyList x)) <|> pure []

def many (x : ParserM α) : ParserM (Array α) := List.toArray <$> manyList x

scoped postfix:max "?" => optional
scoped postfix:max "*" => many

def sepByList (s : ParserM Unit) (p : ParserM α) : ParserM (List α) :=
  (return (← p) :: (← manyList (s *> p))) <|> pure []

def sepBy (s : ParserM Unit) (p : ParserM α) : ParserM (Array α) := List.toArray <$> sepByList s p

def brackets (l r) (p : ParserM α) := tk l *> p <* tk r
def listOf (p : ParserM α) := brackets "[" "]" $ sepBy (tk ",") p
def maybeListOf (p : ParserM α) := listOf p <|> return #[← p]
def ident_ := BinderName.ident <$> ident <|> tk "_" *> pure BinderName._
def usingIdent := (tk "using" *> ident)?
def withIdentList := (tk "with" *> ident_*) <|> pure #[]
def withoutIdentList := (tk "without" *> ident*) <|> pure #[]

open Lean.Elab.Tactic in
def Location.ofOption (l : Array (Option Name)) : Location :=
  let (hs, ty) := l.foldl (init := (#[], false)) fun
    | (hs, _), none => (hs, true)
    | (hs, ty), some n => (hs.push (mkIdent n), ty)
  Location.targets hs ty

open Lean.Elab.Tactic in
def location := (tk "at" *> (tk "*" *> pure Location.wildcard <|>
  (Location.ofOption <$> (((tk "⊢" <|> tk "|-") *> pure none) <|> some <$> ident)*))) <|>
  pure (Location.targets #[] true)

def pExprList := listOf pExpr
def optPExprList := listOf pExpr <|> pure #[]
def pExprListOrTExpr := maybeListOf pExpr
def onlyFlag := (tk "only" *> pure true) <|> pure false

def optTk (yes : Bool) : Option Syntax := if yes then some default else none

def parseBinders : ParserM Binders := do let ⟨_, VMCall.binders bis⟩ ← next | {failure}; pure bis

def inductiveDecl : ParserM InductiveCmd := do
  let ⟨_, VMCall.inductive i⟩ ← next | failure
  let Command.inductive c := (← read).cmds[i]! | failure
  pure c

def renameArg : ParserM (Name × Name) := return (← ident, ← (tk "->")? *> ident)

def renameArgs : ParserM (Array (Name × Name)) :=
  (return #[← renameArg]) <|> listOf renameArg

structure RwRule where
  symm : Bool
  rule : Spanned Expr

def rwRule : ParserM RwRule := do
  pure ⟨Option.isSome (← (tk "<-")?), ← pExpr⟩

def rwRules : ParserM (Array RwRule) := maybeListOf rwRule

def generalizeArg : ParserM (Spanned Expr × Name) := do
  let AST3.Expr.notation n args := (← pExpr).kind.unparen | failure
  let (`«expr = », #[⟨mlhs, Arg.expr lhs⟩, ⟨_, Arg.expr rhs⟩]) := (n.name, args) | failure
  let AST3.Expr.ident x := rhs.unparen | failure
  pure (⟨mlhs, lhs⟩, x)

def hGeneralizeArg : ParserM (Spanned Expr × Name) := do
  let AST3.Expr.notation n args := (← pExpr).kind.unparen | failure
  let (`«expr == », #[⟨mlhs, Arg.expr lhs⟩, ⟨_, Arg.expr rhs⟩]) := (n.name, args) | failure
  let AST3.Expr.ident x := rhs.unparen | failure
  pure (⟨mlhs, lhs⟩, x)

def generalizesArgEq (e : Spanned AST3.Expr) : ParserM (Spanned Expr × Name) := do
  let AST3.Expr.notation n args := e.kind.unparen | failure
  match n.name with | `«expr = » => pure () | `«expr == » => pure () | _ => failure
  let #[⟨mlhs, Arg.expr lhs⟩, ⟨_, Arg.expr rhs⟩] := args | failure
  let AST3.Expr.ident x := rhs.unparen | failure
  pure (⟨mlhs, lhs⟩, x)

def generalizesArg : ParserM (Option Name × Spanned Expr × Name) := do
  let t ← pExpr
  (tk ":" *> do
    let AST3.Expr.ident x := t.kind.unparen | failure
    pure (some x, ← generalizesArgEq (← pExpr))) <|>
  (return (none, ← generalizesArgEq t))

def casesArg : ParserM (Option Name × Spanned Expr) := do
  let t ← pExpr
  match t.kind.unparen with
  | AST3.Expr.ident x => (return (some x, ← tk ":" *> pExpr)) <|> return (none, t)
  | _ => pure (none, t)

def caseArg : ParserM (Array BinderName × Array BinderName) :=
  return (← ident_*, (← (tk ":" *> ident_*)?).getD #[])

def case : ParserM (Array (Array BinderName × Array BinderName)) := maybeListOf caseArg

inductive SimpArg
| allHyps
| except (n : Name)
| expr (sym : Bool) (e : Spanned Expr)

def simpArg : ParserM SimpArg :=
  (tk "*" *> pure SimpArg.allHyps) <|>
  (tk "-" *> SimpArg.except <$> ident) <|>
  (tk "<-" *> SimpArg.expr true <$> pExpr) <|>
  SimpArg.expr false <$> pExpr

def simpArgList : ParserM (Array SimpArg) :=
  (tk "*" *> pure #[SimpArg.allHyps]) <|> listOf simpArg <|> pure #[]

inductive RCasesPat : Type
  | one : BinderName → RCasesPat
  | clear : RCasesPat
  | explicit : RCasesPat → RCasesPat
  | typed : RCasesPat → Spanned AST3.Expr → RCasesPat
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
  (.tuple <$> brackets "⟨" "⟩" (sepBy (tk ",") (rcasesPat false))) <|>
  (tk "-" *> pure .clear) <|>
  (tk "@" *> .explicit <$> rcasesPat true) <|>
  (.one <$> ident_)
| false => do
  let pat ← .alts' <$> rcasesPatList
  (tk ":" *> pat.typed <$> pExpr) <|> pure pat

partial def rcasesPatList (pats : Array RCasesPat := #[]) : ParserM (Array RCasesPat) := do
  pats.push (← rcasesPat true) |> rcasesPatListRest

partial def rcasesPatListRest (pats : Array RCasesPat) : ParserM (Array RCasesPat) :=
  (tk "|" *> rcasesPatList pats) <|>
  -- hack to support `-|-` patterns, because `|-` is a token
  (tk "|-" *> rcasesPatListRest (pats.push .clear)) <|>
  pure pats

end

inductive RCasesArgs
  | hint (tgt : Sum (Spanned AST3.Expr) (Array (Spanned AST3.Expr))) (depth : Option ℕ)
  | rcases (name : Option Name) (tgt : Spanned AST3.Expr) (pat : RCasesPat)
  | rcasesMany (tgt : Array (Spanned AST3.Expr)) (pat : RCasesPat)

set_option linter.unusedVariables false in -- FIXME(Mario): spurious warning on let p ← ...
def rcasesArgs : ParserM RCasesArgs := do
  let hint ← (tk "?")?
  let p ← (Sum.inr <$> brackets "⟨" "⟩" (sepBy (tk ",") pExpr)) <|>
          (Sum.inl <$> pExpr)
  match hint with
  | none => do
    let p ← (do
      let Sum.inl t := p | failure
      let AST3.Expr.ident h := t.kind.unparen | failure
      return Sum.inl (h, ← tk ":" *> pExpr)) <|>
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
  | binder : Array RIntroPat → Option (Spanned AST3.Expr) → RIntroPat
  deriving Inhabited

mutual

partial def rintroPatHi : ParserM RIntroPat :=
  brackets "(" ")" rintroPat <|> RIntroPat.one <$> rcasesPat true

partial def rintroPat : ParserM RIntroPat := do
  match ← rintroPatHi* with
  | #[] => failure
  | #[RIntroPat.one pat] =>
    let pat1 := RCasesPat.alts' (← rcasesPatListRest #[pat])
    pure $ match ← (tk ":" *> pExpr)? with
    | none => RIntroPat.one pat1
    | some e => RIntroPat.one $ pat1.typed e
  | pats => RIntroPat.binder pats <$> (tk ":" *> pExpr)?

end

/-- Syntax for a `rintro` patern: `('?' (: n)?) | rintro_pat`. -/
def rintroArg : ParserM (Sum (Array RIntroPat × Option (Spanned AST3.Expr)) (Option ℕ)) :=
(tk "?" *> Sum.inr <$> (tk ":" *> smallNat)?) <|>
return Sum.inl (← rintroPatHi*, ← (tk ":" *> pExpr)?)

/-- Parses `patt? (: expr)? (:= expr)?`, the arguments for `obtain`.
 (This is almost the same as `rcasesPat false`,
but it allows the pattern part to be empty.) -/
def obtainArg :
  ParserM ((Option RCasesPat × Option (Spanned AST3.Expr)) × Option (Array (Spanned AST3.Expr))) := do
  let (pat, tp) ←
    (return match ← rcasesPat false with
      | RCasesPat.typed pat tp => (some pat, some tp)
      | pat => (some pat, none)) <|>
    (return (none, ← (tk ":" *> pExpr)?))
  pure ((pat, tp), ← (tk ":=" *> do
    (guard tp.isNone *> brackets "⟨" "⟩" (sepBy (tk ",") pExpr)) <|>
    (return #[← pExpr]))?)

inductive LintVerbosity | low | medium | high

def lintVerbosity : ParserM LintVerbosity :=
  (tk "-" *> pure LintVerbosity.low) <|>
  (tk "+" *> pure LintVerbosity.high) <|> pure LintVerbosity.medium

def lintOpts : ParserM (Bool × LintVerbosity) := do
  match ← lintVerbosity, (← (tk "*")?).isSome with
  | LintVerbosity.medium, fast => pure (fast, ← lintVerbosity)
  | v, fast => pure (fast, v)

def lintArgs : ParserM ((Bool × LintVerbosity) × Bool × Array Name) :=
  return (← lintOpts, ← onlyFlag, ← ident*)

inductive ExtParam | arrow | all | ident (n : Name)

def extParam : ParserM (Bool × ExtParam) :=
  return (
    (← (tk "-")?).isSome,
    ← (brackets "(" ")" (tk "->") *> pure ExtParam.arrow) <|>
      (tk "*" *> pure ExtParam.all) <|>
      (ExtParam.ident <$> ident))

def extParams : ParserM (Array (Bool × ExtParam)) :=
  (return #[← extParam]) <|> listOf extParam <|> pure #[]

def simpsRule : ParserM (Sum (Name × Name) Name × Bool) := do
  let lhs ← (return Sum.inl (← ident, ← tk "->" *> ident)) <|> (return Sum.inr (← tk "-" *> ident))
  return (lhs, (← (tk "as_prefix")?).isSome)

def simpsRules : ParserM (Array (Sum (Name × Name) Name × Bool)) :=
  brackets "(" ")" (sepBy (tk ",") simpsRule)

def structInst : ParserM Expr := do
  tk "{"
  let ls ← sepBy (tk ",") $
    Sum.inl <$> (tk ".." *> pExpr) <|>
    return Sum.inr (← ident <* tk ":=", ← pExpr)
  tk "}"
  let mut srcs := #[]
  let mut fields := #[]
  for l in ls do
    match l with
    | Sum.inl src => srcs := srcs.push src
    | Sum.inr (n, v) => fields := fields.push (Spanned.dummy n, v)
  pure $ Expr.structInst none none fields srcs false

end Parser
