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

@[tr_ni_tactic tactic.exact_dec_trivial] def trExactDecTrivial (_ : AST3.Expr) : M Syntax.Tactic :=
  `(tactic| decide)

@[tr_tactic fsplit] def trFSplit : TacM Syntax.Tactic := `(tactic| fconstructor)

@[tr_tactic injections_and_clear] def trInjectionsAndClear : TacM Syntax.Tactic :=
  `(tactic| injections)

@[tr_user_cmd «run_parser»] def trRunParser : Parse1 Syntax.Command := parse0 do
  warn! "unsupported: run_parser" -- unattested

@[tr_ni_tactic tactic.classical] def trNIClassical (_ : AST3.Expr) : M Syntax.Tactic :=
  return mkBlockTransform fun args => `(tactic| classical $args*)

@[tr_user_attr higher_order] def trHigherOrderAttr : Parse1 Syntax.Attr :=
  parse1 (ident)? fun n => do
    `(attr| higher_order $(← liftM $ n.mapM mkIdentI)?)

@[tr_user_attr interactive] def trInteractiveAttr : Parse1 Syntax.Attr :=
  parse0 `(attr| interactive)

@[tr_user_cmd «setup_tactic_parser»] def trSetupTacticParser : Parse1 Unit :=
  parse1 emittedCodeHere fun _ => warn! "unsupported: setup_tactic_parser"

open TSyntax.Compat in
def trInterpolatedStr' := trInterpolatedStr fun stx => `(← $stx)

@[tr_user_nota tactic.pformat_macro] def trPFormatMacro : TacM Syntax.Term := do
  `(f! $(← trInterpolatedStr'))

@[tr_user_nota tactic.fail_macro] def trFailMacro : TacM Syntax.Term := do
  let stx ← trInterpolatedStr'; `(throwError $stx)

@[tr_user_nota tactic.trace_macro] def trTraceMacro : TacM Syntax.Term := do
  let stx ← trInterpolatedStr'; `(← do dbg_trace $stx)

@[tr_user_cmd «import_private»] def trImportPrivate : Parse1 Syntax.Command :=
  parse1 (return (← ident, ← (tk "from" *> ident)?)) fun (n, fr) => do
  `(open private $(← mkIdentF n) $[from $(← liftM $ fr.mapM mkIdentI)]?)

@[tr_user_cmd «mk_simp_attribute»] def trMkSimpAttribute : Parse1 Unit :=
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
