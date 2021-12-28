/-
Copyright (c) 2021 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
import Mathport.Syntax.Translate.Tactic.Basic
import Mathport.Syntax.Translate.Tactic.Lean3

open Lean

namespace Mathport.Translate.Tactic
open Parser

-- # tactic.monotonicity

@[trUserAttr mono] def trMonoAttr : TacM Syntax := do
  match ← parse (ident)? with
  | some `left => `(attr| mono left)
  | some `right => `(attr| mono right)
  | some `both => `(attr| mono)
  | none => `(attr| mono)
  | _ => warn! "unsupported (impossible)"

@[trTactic mono] def trMono : TacM Syntax := do
  let star := mkOptionalNode' (← parse (tk "*")?) fun _ => #[mkAtom "*"]
  let side ← match ← parse (ident)? with
  | some `left => some (mkAtom "left")
  | some `right => some (mkAtom "right")
  | some `both => none
  | none => none
  | _ => warn! "unsupported (impossible)"
  let w ← match ← parse ((tk "with" *> pExprListOrTExpr) <|> pure #[]) with
  | #[] => none
  | w => liftM $ some <$> w.mapM trExpr
  let hs ← trSimpArgs (← parse ((tk "using" *> simpArgList) <|> pure #[]))
  mkNode ``Parser.Tactic.mono #[mkAtom "mono", star,
    mkOptionalNode' side fun side => #[mkNode ``Parser.Tactic.mono.side #[side]],
    mkOptionalNode' w fun w => #[mkAtom "with", (mkAtom ",").mkSep w],
    mkNullNode $ if hs.isEmpty then #[] else #[mkAtom "using", (mkAtom ",").mkSep hs]]

@[trTactic ac_mono] def trAcMono : TacM Syntax := do
  let arity ← parse $
    (tk "*" *> pure #[mkAtom "*"]) <|>
    (tk "^" *> do #[mkAtom "^", Quote.quote (← smallNat)]) <|> pure #[]
  let arg ← parse ((tk ":=" *> do (":=", ← pExpr)) <|> (tk ":" *> do (":", ← pExpr)))?
  let arg ← mkOptionalNodeM arg fun (s, e) => do #[mkAtom s, ← trExpr e]
  let cfg ← mkConfigStx $ ← liftM $ (← expr?).mapM trExpr
  mkNode ``Parser.Tactic.acMono #[mkAtom "ac_mono", mkNullNode arity, cfg, arg]
