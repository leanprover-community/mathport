/-
Copyright (c) 2021 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Daniel Selsam
-/
import Mathport.Util

namespace Mathport
open Lean

structure Data4 where
  module : Syntax
  exprs  : HashMap Position Expr
  deriving Inhabited

end Mathport

-- To fix upstream:
-- * bracketedExplicitBinders doesn't support optional types

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
notation "ℕ" => Nat
notation "ℤ" => Int

open Lean.Elab.Command Lean.Parser Lean

@[commandElab includeCmd] def elabIncludeCmd : CommandElab := fun stx => pure ()
@[commandElab omitCmd] def elabOmitCmd : CommandElab := fun stx => pure ()

namespace Lean
namespace Parser.Term

def calcDots := leading_parser symbol "..."
def calcLHS : Parser where
  fn c s :=
    let s := calcDots.fn c s
    if s.hasError then s else
    let tables := (getCategory (parserExtension.getState c.env).categories `term).get!.tables
    trailingLoop tables c s
  info := (calcDots >> termParser).info

open Lean.PrettyPrinter Lean.Elab.Term

@[combinatorFormatter Lean.Parser.Term.calcLHS] def calcLHS.formatter : Formatter := pure ()
@[combinatorParenthesizer Lean.Parser.Term.calcLHS] def calcLHS.parenthesizer : Parenthesizer := pure ()

syntax (name := «calc») "calc " term " : " term (calcLHS " : " term)* : term

end Parser.Term

namespace Parser.Command

-- Using /! as a workaround since /-! is not lexed properly
@[commandParser] def modDocComment := leading_parser ppDedent $ "/!" >> commentBody >> ppLine

end Parser.Command

namespace Elab.Term

@[macro Lean.Parser.Term.calc] def expandCalc : Macro := fun stx => `(sorry)

end Elab.Term

def ExistsUnique {α : Sort u} (p : α → Prop) := ∃ x, p x ∧ ∀ y, p y → y = x

macro "∃! " xs:explicitBinders ", " b:term : term => expandExplicitBinders ``ExistsUnique xs b
