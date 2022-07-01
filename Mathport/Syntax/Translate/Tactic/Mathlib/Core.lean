/-
Copyright (c) 2021 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
import Mathport.Syntax.Translate.Tactic.Basic
import Mathport.Syntax.Translate.Tactic.Lean3

open Lean

namespace Mathport.Translate.Tactic
open AST3 Parser

-- # tactic.core

@[trNITactic tactic.exact_dec_trivial] def trExactDecTrivial (_ : AST3.Expr) : M Syntax :=
  `(tactic| decide)

@[trTactic fsplit] def trFSplit : TacM Syntax := `(tactic| fconstructor)

@[trTactic injections_and_clear] def trInjectionsAndClear : TacM Syntax :=
  `(tactic| injections_and_clear)

@[trUserCmd «run_parser»] def trRunParser : TacM Syntax := do
  warn! "unsupported: run_parser" -- unattested

@[trNITactic tactic.classical] def trNIClassical (_ : AST3.Expr) : M Syntax :=
  `(tactic| classical)

@[trUserAttr higher_order] def trHigherOrderAttr : TacM Syntax := do
  `(attr| higher_order $(← liftM $ (← parse (ident)?).mapM mkIdentI)?)

@[trUserAttr interactive] def trInteractiveAttr : TacM Syntax :=
  parse_0 `(attr| interactive)

@[trUserCmd «setup_tactic_parser»] def trSetupTacticParser : TacM Syntax :=
  parse emittedCodeHere *> `(command| setup_tactic_parser)

open TSyntax.Compat in
def trInterpolatedStr' := trInterpolatedStr fun stx => `(← $stx)

@[trUserNota tactic.pformat_macro] def trPFormatMacro : TacM Syntax := do
  `(f! $(← trInterpolatedStr'))

@[trUserNota tactic.fail_macro] def trFailMacro : TacM Syntax := do
  `(throwError $(← trInterpolatedStr'))

@[trUserNota tactic.trace_macro] def trTraceMacro : TacM Syntax := do
  let stx ← trInterpolatedStr'; `(← do dbg_trace $stx)

@[trUserCmd «import_private»] def trImportPrivate : TacM Syntax := do
  let (n, fr) ← parse $ return (← ident, ← (tk "from" *> ident)?)
  `(open private $(← mkIdentF n) $[from $(← liftM $ fr.mapM mkIdentI)]?)

@[trUserCmd «mk_simp_attribute»] def trMkSimpAttribute : TacM Syntax := do
  let (n, d, withList) ← parse $ return (← ident, ← pExpr, ← (tk "with" *> ident*)?)
  let d ← match d.kind.unparen with
  | AST3.Expr.ident `none => pure $ none
  | AST3.Expr.string s => pure $ some (Syntax.mkStrLit s)
  | _ => warn! "unsupported: weird string"
  `(command| mk_simp_attribute $(mkIdent n) $[from $[$(withList.map (·.map mkIdent))]*]? $[:= $d]?)

