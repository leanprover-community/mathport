import Lean.Elab.Command
import Lean.Elab.Quotation

-- To fix upstream:
-- * bracketedExplicitBinders doesn't support optional types

namespace Lean

namespace Parser.Term

syntax (name := cmdQuot) "`(command|" incQuotDepth(command) ")" : term

end Parser.Term

namespace Elab.Term

open Lean Elab Term Quotation in
@[termElab cmdQuot] def elabCmdQuot : TermElab := adaptExpander stxQuot.expand

end Elab.Term

namespace Parser.Command

syntax (name := include) "include " ident+ : command
syntax (name := omit) "omit " ident+ : command
syntax (name := parameter) "parameter " bracketedBinder+ : command
syntax (name := noncomputableTheory) (docComment)? "noncomputable " "theory" : command
syntax (name := runCmd) "run_cmd " term : command

syntax bindersItem := "(" "..." ")"

syntax identScope := ":" "(" "scoped " ident " => " term ")"

syntax notation3Item := strLit <|> bindersItem <|> (ident (identScope)?)

macro ak:Term.attrKind "notation3 "
  prec:optPrecedence name:optNamedName prio:optNamedPrio
  lits:((ppSpace notation3Item)+) " => " val:term : command => do
  let args ← lits.getArgs.mapM fun lit =>
    let k := lit[0].getKind
    if k == strLitKind then `(macroArg| $(lit[0]):strLit)
    else if k == ``bindersItem then withFreshMacroScope `(macroArg| bi:explicitBinders)
    else withFreshMacroScope `(macroArg| $(lit[0]):ident:term)
  `(command| $ak:attrKind macro
    $[$(prec.getOptional?):precedence]?
    $[$(name.getOptional?):namedName]?
    $[$(prio.getOptional?):namedPrio]?
    $(args[0]):macroArg $[$(args[1:].toArray):macroArg]* : term =>
    `(sorry))

-- Using /! as a workaround since /-! is not lexed properly
@[commandParser] def modDocComment := leading_parser
  ppDedent $ "/!" >> commentBody >> ppLine

end Parser.Command

namespace Elab.Command

@[commandElab Parser.Command.include]
def elabIncludeCmd : CommandElab := fun _ => pure ()

@[commandElab Parser.Command.omit]
def elabOmitCmd : CommandElab := fun _ => pure ()

@[commandElab Parser.Command.modDocComment]
def Elab.Command.elabModDocComment : CommandElab := fun _ => pure ()

open Meta in
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

-- TODO(Mario): Why is the extra indirection needed?
@[implementedBy elabRunCmdUnsafe] constant elabRunCmd' : CommandElab
@[commandElab runCmd] def elabRunCmd : CommandElab := elabRunCmd'

end Elab.Command

namespace Parser.Term

syntax:lead (name := noMatch) "match " matchDiscr,* " with" "." : term
syntax (name := noFun) "fun" "." : term
syntax "{" term,* "}" : term
syntax "{ " ident (" : " term)? " | " term " }" : term
syntax "{ " ident " ∈ " term " | " term " }" : term
syntax (priority := low) "{" term " | " bracketedBinder+ " }" : term
syntax "quote " term : term
syntax "pquote " term : term
syntax "ppquote " term : term
syntax "%%" term : term

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

@[formatter Lean.Parser.Term.calcDots]
def calcDots.formatter : Formatter :=
  Formatter.visitArgs $ Parser.symbol.formatter "..."

@[parenthesizer Lean.Parser.Term.calcDots]
def calcDots.parenthesizer : Parenthesizer :=
  Parenthesizer.visitArgs $ Parser.symbol.parenthesizer "..."

@[combinatorFormatter Lean.Parser.Term.calcLHS]
def calcLHS.formatter : Formatter := termParser.formatter

@[combinatorParenthesizer Lean.Parser.Term.calcLHS]
def calcLHS.parenthesizer : Parenthesizer := termParser.parenthesizer

syntax calcFirst := ppLine term " : " term
syntax calcRest := ppLine calcLHS " : " term
syntax (name := «calc») "calc " calcFirst calcRest* : term

end Term

namespace Tactic

syntax tactic " <;> " "[" tactic,* "]" : tactic
syntax "do " doSeq : tactic

end Tactic

notation "ℕ" => Nat
notation "ℤ" => Int

end Parser

def ExistsUnique {α : Sort u} (p : α → Prop) := ∃ x, p x ∧ ∀ y, p y → y = x

notation3 "∃! " (...) ", " x:(scoped f => ExistsUnique f) => x

namespace Parser.Tactic

syntax "propagateTags " tacticSeq : tactic
syntax "introv " ident* : tactic
syntax renameArg := ident " => " ident
syntax "rename' " renameArg,* : tactic
syntax "fapply " term : tactic
syntax "eapply " term : tactic
syntax "apply " term " with " term : tactic
syntax "mapply " term : tactic
syntax "exacts" "[" term,* "]" : tactic
syntax "toExpr' " term : tactic
syntax (name := _root_.Lean.Parser.Tactic.rwSeq)
  "rwa " Parser.Tactic.rwRuleSeq (Parser.Tactic.location)? : tactic
syntax "withCases " tacticSeq : tactic
syntax (name := induction') "induction' " Parser.Tactic.casesTarget,+ (" using " ident)?
  (" with " ident+)? (" generalizing " ident+)? : tactic
syntax caseArg := ident,+ " : " (ident <|> "_")*
syntax (name := case') "case' " (("[" caseArg,* "]") <|> caseArg) " => " tacticSeq : tactic
syntax "destruct " term : tactic
syntax (name := cases') "cases' " Parser.Tactic.casesTarget,+ (" using " ident)?
  (" with " ident+)? : tactic
syntax (name := casesM) "casesM" "*"? ppSpace term,* : tactic
syntax (name := casesType) "casesType" "!"? "*"? ppSpace ident* : tactic
syntax (name := «sorry») "sorry" : tactic
syntax (name := iterate) "iterate " (num)? tacticSeq : tactic
syntax (name := repeat') "repeat' " tacticSeq : tactic
syntax (name := abstract) "abstract " (ident)? tacticSeq : tactic
syntax (name := anyGoals) "anyGoals " tacticSeq : tactic
syntax (name := have'') "have " Parser.Term.haveIdLhs : tactic
syntax (name := let'') "let " Parser.Term.haveIdLhs : tactic
syntax (name := suffices') "suffices " Parser.Term.haveIdLhs : tactic
syntax (name := trace) "trace " term : tactic
syntax (name := existsi) "exists " term,* : tactic
syntax (name := eConstructor) "econstructor" : tactic
syntax (name := left) "left" : tactic
syntax (name := right) "right" : tactic
syntax (name := split) "split" : tactic
syntax (name := constructorM) "constructorM" "*"? ppSpace term,* : tactic
syntax (name := exFalso) "exFalso" : tactic
syntax (name := injections) "injections " (" with " (colGt (ident <|> "_"))+)? : tactic
syntax (name := simpIntro) "simpIntro " ("(" &"config" " := " term ")")? ident* (&"only ")?
  ("[" (Parser.Tactic.simpErase <|> Parser.Tactic.simpLemma),* "]")? : tactic
syntax (name := dSimp) "dsimp " ("(" &"config" " := " term ")")? (&"only ")?
  ("[" (Parser.Tactic.simpErase <|> Parser.Tactic.simpLemma),* "]")?
  (Parser.Tactic.location)? : tactic
syntax (name := symm) "symm" : tactic
syntax (name := trans) "trans" (term)? : tactic
syntax (name := acRfl) "acRfl" : tactic
syntax (name := cc) "cc" : tactic
syntax (name := substVars) "substVars" : tactic
syntax (name := dUnfold) "dunfold" ("(" &"config" " := " term ")")?
  ident* (Parser.Tactic.location)? : tactic
syntax (name := delta) "delta" ident* (Parser.Tactic.location)? : tactic
syntax (name := unfoldProjs) "unfoldProjs" ("(" &"config" " := " term ")")?
  (Parser.Tactic.location)? : tactic
syntax (name := unfold) "unfold" ("(" &"config" " := " term ")")?
  ident* (Parser.Tactic.location)? : tactic
syntax (name := unfold1) "unfold1" ("(" &"config" " := " term ")")?
  ident* (Parser.Tactic.location)? : tactic
syntax (name := inferOptParam) "inferOptParam" : tactic
syntax (name := inferAutoParam) "inferAutoParam" : tactic
syntax (name := guardExprEq) "guardExprEq " term " := " term : tactic
syntax (name := guardTarget) "guardTarget " term : tactic
syntax (name := guardHyp) "guardHyp " ident (" : " term)? (" := " term)? : tactic
syntax (name := matchTarget) "matchTarget " term : tactic
syntax (name := byCases) "byCases " (ident " : ")? term : tactic
syntax (name := funext) "funext " (colGt (ident <|> "_"))* : tactic
syntax (name := byContra) "byContra " (colGt ident)? : tactic
syntax (name := typeCheck) "typeCheck " term : tactic
syntax (name := specialize) "specialize " ident (colGt term:arg)+ : tactic
syntax (name := congr) "congr " (colGt num)? : tactic
syntax (name := rsimp) "rsimp" : tactic
syntax (name := compVal) "compVal" : tactic
syntax (name := async) "async " tacticSeq : tactic

declare_syntax_cat rcasesPat
syntax rcasesPatMed := rcasesPat (" | " rcasesPat)*
syntax rcasesPatLo := rcasesPatMed (" : " term)?
syntax (name := rcasesPat.one) ident : rcasesPat
syntax (name := rcasesPat.ignore) "_" : rcasesPat
syntax (name := rcasesPat.clear) "-" : rcasesPat
syntax (name := rcasesPat.tuple) "⟨" rcasesPatLo,* "⟩" : rcasesPat
syntax (name := rcasesPat.paren) "(" rcasesPatLo ")" : rcasesPat
syntax (name := rcasesHint) "rcases?" Parser.Tactic.casesTarget,* (" : " num)? : tactic
syntax (name := rcases) "rcases" Parser.Tactic.casesTarget,* (" with " rcasesPat)? : tactic
syntax (name := obtain) "obtain" (ppSpace rcasesPat)? (" : " term)? (" := " term,+)? : tactic

declare_syntax_cat rintroPat
syntax (name := rintroPat.one) rcasesPat : rintroPat
syntax (name := rintroPat.binder) "(" (rintroPat+ <|> rcasesPatMed) (" : " term)? ")" : rintroPat
syntax (name := rintroHint) "rintro?" (" : " num)? : tactic
syntax (name := rintro) "rintro" (ppSpace rintroPat)* (" : " term)? : tactic
