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

@[tr_user_attr mono] def trMonoAttr : Parse1 Syntax.Attr :=
  parse1 (ident)? fun
  | some `left => `(attr| mono left)
  | some `right => `(attr| mono right)
  | some `both => `(attr| mono)
  | none => `(attr| mono)
  | _ => warn! "unsupported (impossible)"

@[tr_tactic mono] def trMono : TacM Syntax.Tactic := do
  let star := optTk (← parse (tk "*")?).isSome
  let side ← match ← parse (ident)? with
  | some `left => some <$> `(Lean.Parser.Tactic.mono.side| left)
  | some `right => some <$> `(Lean.Parser.Tactic.mono.side| right)
  | some `both => pure none
  | none => pure none
  | _ => warn! "unsupported (impossible)"
  let w := (← (← parse ((tk "with" *> pExprListOrTExpr) <|> pure #[])).mapM (trExpr ·)).asNonempty
  let hs := (← trSimpArgs (← parse ((tk "using" *> simpArgList) <|> pure #[]))).asNonempty
  `(tactic| mono $[*%$star]? $(side)? $[with $w,*]? $[using $hs,*]?)

open TSyntax.Compat in
private def mkConfigStx (stx : Option Syntax) : M Syntax :=
  mkOpt stx fun stx => `(Lean.Parser.Tactic.config| (config := $stx))

@[tr_tactic ac_mono] def trAcMono : TacM Syntax.Tactic := do
  let arity ← parse $
    (tk "*" *> pure #[mkAtom "*"]) <|>
    (tk "^" *> return #[mkAtom "^", Quote.quote (k := `term) (← smallNat)]) <|> pure #[]
  let arg ← parse ((tk ":=" *> return (":=", ← pExpr)) <|> (tk ":" *> return (":", ← pExpr)))?
  let arg ← mkOptionalNodeM arg fun (s, e) => return #[mkAtom s, ← trExpr e]
  let cfg ← mkConfigStx $ ← liftM $ (← expr?).mapM trExpr
  pure ⟨mkNode ``Parser.Tactic.acMono #[mkAtom "ac_mono", mkNullNode arity, cfg, arg]⟩
