/-
Copyright (c) 2021 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Daniel Selsam
-/
import Mathport.Util.Misc

namespace Mathport
open Lean

structure Data4 where
  fmt : Format
  exprs : HashMap Position Expr
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
syntax tactic " <;> " "[" tactic,* "]" : tactic
syntax "do " doSeq : tactic
syntax (name := Lean.Elab.Command.runCmd) "run_cmd " term : command

open Lean.Elab.Command Lean.Parser Lean Elab Meta

@[commandElab includeCmd] def elabIncludeCmd : CommandElab := fun stx => pure ()
@[commandElab omitCmd] def elabOmitCmd : CommandElab := fun stx => pure ()

unsafe def elabRunCmdUnsafe : CommandElab
  | `(run_cmd $term) =>
    let n := `_runCmd
    runTermElabM (some n) fun _ => do
      let e ← Term.elabTerm term none
      Term.synthesizeSyntheticMVarsNoPostponing
      let e ← withLocalDeclD `env (mkConst ``Lean.Environment) fun env =>
          withLocalDeclD `opts (mkConst ``Lean.Options) fun opts => do
            let e ← mkAppM ``Lean.runMetaEval #[env, opts, e]
            mkLambdaFVars #[env, opts] e
      let env ← getEnv
      let opts ← getOptions
      let act ← try
        let type ← inferType e
        let decl := Declaration.defnDecl {
          name        := n
          levelParams := []
          type        := type
          value       := e
          hints       := ReducibilityHints.opaque
          safety      := DefinitionSafety.unsafe }
        Term.ensureNoUnassignedMVars decl
        addAndCompile decl
        evalConst (Environment → Options → IO (String × Except IO.Error Environment)) n
      finally setEnv env
      match (← act env opts).2 with
      | Except.error e => throwError e.toString
      | Except.ok env  => do setEnv env; pure ()
  | _ => throwUnsupportedSyntax

@[implementedBy elabRunCmdUnsafe] constant elabRunCmd' : CommandElab
@[commandElab Lean.Elab.Command.runCmd] def elabRunCmd : CommandElab := elabRunCmd'

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

run_cmd show CoreM _ from
  modifyEnv fun env => addSyntaxNodeKind env ``calcDots

open Lean.PrettyPrinter Lean.Elab.Term

@[formatter Lean.Parser.Term.calcDots] def calcDots.formatter : Formatter :=
Formatter.visitArgs $ Parser.symbol.formatter "..."
@[parenthesizer Lean.Parser.Term.calcDots] def calcDots.parenthesizer : Parenthesizer :=
Parenthesizer.visitArgs $ Parser.symbol.parenthesizer "..."
@[combinatorFormatter Lean.Parser.Term.calcLHS] def calcLHS.formatter : Formatter := termParser.formatter
@[combinatorParenthesizer Lean.Parser.Term.calcLHS] def calcLHS.parenthesizer : Parenthesizer := termParser.parenthesizer

syntax calcFirst := ppLine term " : " term
syntax calcRest := ppLine calcLHS " : " term
syntax (name := «calc») "calc " calcFirst calcRest* : term

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
