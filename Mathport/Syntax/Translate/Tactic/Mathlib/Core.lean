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
  `(tactic| injections)

@[trUserCmd «run_parser»] def trRunParser : Parse1 Syntax := parse0 do
  warn! "unsupported: run_parser" -- unattested

@[trNITactic tactic.classical] def trNIClassical (_ : AST3.Expr) : M Syntax :=
  `(tactic| classical)

@[trUserAttr higher_order] def trHigherOrderAttr : Parse1 Syntax :=
  parse1 (ident)? fun n => do
    `(attr| higher_order $(← liftM $ n.mapM mkIdentI)?)

@[trUserAttr interactive] def trInteractiveAttr : Parse1 Syntax :=
  parse0 `(attr| interactive)

@[trUserCmd «setup_tactic_parser»] def trSetupTacticParser : Parse1 Syntax :=
  parse1 emittedCodeHere fun _ => `(command| setup_tactic_parser)

open TSyntax.Compat in
def trInterpolatedStr' := trInterpolatedStr fun stx => `(← $stx)

@[trUserNota tactic.pformat_macro] def trPFormatMacro : TacM Syntax := do
  `(f! $(← trInterpolatedStr'))

@[trUserNota tactic.fail_macro] def trFailMacro : TacM Syntax := do
  `(throwError $(← trInterpolatedStr'))

@[trUserNota tactic.trace_macro] def trTraceMacro : TacM Syntax := do
  let stx ← trInterpolatedStr'; `(← do dbg_trace $stx)

@[trUserCmd «import_private»] def trImportPrivate : Parse1 Syntax :=
  parse1 (return (← ident, ← (tk "from" *> ident)?)) fun (n, fr) => do
  `(open private $(← mkIdentF n) $[from $(← liftM $ fr.mapM mkIdentI)]?)

@[trUserCmd «mk_simp_attribute»] def trMkSimpAttribute : Parse1 Unit :=
  parse1 (return (← ident, ← pExpr, ← (tk "with" *> ident*)?)) fun (n, d, withList) => do
  let descr ← match d.kind.unparen with
  | AST3.Expr.ident `none => pure s!"simp set for {n.toString}"
  | AST3.Expr.string s => pure s
  | _ => warn! "unsupported: weird string"
  let n := mkIdent n
  push (← `(command| $(trDocComment s!" {descr} "):docComment register_simp_attr $n))
  let withList := withList.getD #[]
  unless withList.isEmpty do
    logComment "[mathport] port note: move this to another file, it won't work here"
    push (← `(command| attribute [$n:ident] $(← liftM $ withList.mapM mkIdentI)*))
