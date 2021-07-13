/-
Copyright (c) 2021 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Daniel Selsam
-/
import Mathport.Util

namespace Mathport
open Lean

structure Data4 where
  commands : Array Syntax
  exprs    : HashMap Position Expr

end Mathport

syntax (name := hideCmd) "hide " ident+ : command
syntax (name := includeCmd) "include " ident+ : command
syntax (name := omitCmd) "omit " ident+ : command
syntax (name := parameterCmd) "parameter " bracketedBinder+ : command
syntax:lead (name := noMatch) "match " matchDiscr,* " with" "." : term
syntax (name := noFun) "fun" "." : term
syntax (name := noncomputableTheory) "noncomputable " "theory" : command
syntax "{" term,* "}" : term
syntax "{ " ident (" : " term)? " | " term " }" : term
syntax "{ " ident " ∈ " term " | " term " }" : term
syntax (priority := low) "{" term " | " bracketedBinder+ " }" : term

open Lean.Elab.Command Lean.Parser Lean

@[commandElab hideCmd] def elabHideCmd : CommandElab := fun stx => pure ()
@[commandElab includeCmd] def elabIncludeCmd : CommandElab := fun stx => pure ()
@[commandElab omitCmd] def elabOmitCmd : CommandElab := fun stx => pure ()

def calcLHS : Parser where
  fn c s :=
    let s := symbolFn "..." c s
    if s.hasError then s else
    let tables := (getCategory (parserExtension.getState c.env).categories `term).get!.tables
    trailingLoop tables c s
  info := ("..." >> termParser).info

open Lean.PrettyPrinter Lean.Elab.Term

@[combinatorFormatter calcLHS] def calcLHS.formatter : Formatter := pure ()
@[combinatorParenthesizer calcLHS] def calcLHS.parenthesizer : Parenthesizer := pure ()

syntax (name := calcTerm) "calc " term " : " term (calcLHS " : " term)* : term

@[macro calcTerm] def expandCalc : Macro := fun stx => `(sorry)
