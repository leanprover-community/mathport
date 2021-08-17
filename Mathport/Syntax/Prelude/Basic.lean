import Lean.Elab.Command
import Lean.Elab.Quotation

-- To fix upstream:
-- * bracketedExplicitBinders doesn't support optional types

namespace Lean

namespace Parser.Term

@[termParser default+1] def Command.quot : Parser :=
  leading_parser "`(command|" >> incQuotDepth commandParser >> ")"

end Parser.Term

namespace Elab.Term

open Lean Elab Term Quotation in
@[termElab Command.quot] def elabCommandQuot : TermElab := adaptExpander stxQuot.expand

end Elab.Term

namespace Parser.Command

syntax (name := include) "include " ident+ : command
syntax (name := omit) "omit " ident+ : command
syntax (name := parameter) "parameter " bracketedBinder+ : command
syntax (name := noncomputableTheory) (docComment)? "noncomputable " "theory" : command
syntax (name := runCmd) "run_cmd " doSeq : command

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
unsafe def elabRunCmdUnsafe : CommandElab := fun stx => do
  let name := stx[1].getOptional?
  let e ← `((do $(stx[1]) : CoreM Unit))
  let n := `_runCmd
  runTermElabM (some n) fun _ => do
    let e ← Term.elabTerm e (← Term.elabTerm (← `(CoreM Unit)) none)
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

run_cmd modifyEnv fun env => addSyntaxNodeKind env ``calcDots

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

namespace Parser.Tactic

syntax (name := propagateTags) "propagateTags " tacticSeq : tactic
syntax (name := introv) "introv " binderIdent* : tactic
syntax renameArg := ident " => " ident
syntax (name := rename') "rename' " renameArg,* : tactic
syntax (name := fapply) "fapply " term : tactic
syntax (name := eapply) "eapply " term : tactic
syntax (name := applyWith) "apply " term " with " term : tactic
syntax (name := mapply) "mapply " term : tactic
syntax (name := exacts) "exacts" "[" term,* "]" : tactic
syntax (name := toExpr') "toExpr' " term : tactic

syntax (name := rwa) "rwa " rwRuleSeq (location)? : tactic
syntax (name := withCases) "withCases " tacticSeq : tactic
syntax (name := induction') "induction' " casesTarget,+ (" using " ident)?
  (" with " binderIdent+)? (" generalizing " ident+)? : tactic
syntax caseArg := ident,+ " : " (ident <|> "_")*
syntax (name := case') "case' " (("[" caseArg,* "]") <|> caseArg) " => " tacticSeq : tactic
syntax "destruct " term : tactic
syntax (name := cases') "cases' " casesTarget,+ (" using " ident)?
  (" with " binderIdent+)? : tactic
syntax (name := casesM) "casesM" "*"? ppSpace term,* : tactic
syntax (name := casesType) "casesType" "*"? ppSpace ident* : tactic
syntax (name := casesType!) "casesType!" "*"? ppSpace ident* : tactic
syntax (name := «sorry») "sorry" : tactic
syntax (name := iterate) "iterate " (num)? tacticSeq : tactic
syntax (name := repeat') "repeat' " tacticSeq : tactic
syntax (name := abstract) "abstract " (ident)? tacticSeq : tactic
syntax (name := anyGoals) "anyGoals " tacticSeq : tactic
syntax (name := have'') "have " Term.haveIdLhs : tactic
syntax (name := let'') "let " Term.haveIdLhs : tactic
syntax (name := suffices') "suffices " Term.haveIdLhs : tactic
syntax (name := trace) "trace " term : tactic
syntax (name := existsi) "exists " term,* : tactic
syntax (name := eConstructor) "econstructor" : tactic
syntax (name := left) "left" : tactic
syntax (name := right) "right" : tactic
syntax (name := split) "split" : tactic
syntax (name := constructorM) "constructorM" "*"? ppSpace term,* : tactic
syntax (name := exFalso) "exFalso" : tactic
syntax (name := injections) "injections " (" with " (colGt (ident <|> "_"))+)? : tactic
syntax simpArg := simpErase <|> ("← "? simpLemma) <|> "*"
syntax (name := simp') "simp'" "*"? ppSpace ("(" &"config" " := " term ")")? (&"only ")?
  ("[" simpArg,* "]")? (" with " ident+)? (location)? : tactic
syntax (name := simpIntro) "simpIntro " ("(" &"config" " := " term ")")?
  (colGt (ident <|> "_"))* (&"only ")? ("[" simpArg,* "]")? (" with " ident+)? : tactic
syntax (name := dsimp) "dsimp " ("(" &"config" " := " term ")")? (&"only ")?
  ("[" simpArg,* "]")? (" with " ident+)? (location)? : tactic
syntax (name := symm) "symm" : tactic
syntax (name := trans) "trans" (term)? : tactic
syntax (name := acRfl) "acRfl" : tactic
syntax (name := cc) "cc" : tactic
syntax (name := substVars) "substVars" : tactic
syntax (name := dUnfold) "dunfold" ("(" &"config" " := " term ")")? ident* (location)? : tactic
syntax (name := delta) "delta" ident* (location)? : tactic
syntax (name := unfoldProjs) "unfoldProjs" ("(" &"config" " := " term ")")? (location)? : tactic
syntax (name := unfold) "unfold" ("(" &"config" " := " term ")")? ident* (location)? : tactic
syntax (name := unfold1) "unfold1" ("(" &"config" " := " term ")")? ident* (location)? : tactic
syntax (name := inferOptParam) "inferOptParam" : tactic
syntax (name := inferAutoParam) "inferAutoParam" : tactic
syntax (name := guardExprEq) "guardExpr " term:51 " =ₐ " term : tactic
syntax (name := guardTarget) "guardTarget" " =ₐ " term : tactic
syntax (name := guardHyp) "guardHyp " ident ((" : " <|> " :ₐ ") term)? ((" := " <|> " :=ₐ ") term)? : tactic
syntax (name := matchTarget) "matchTarget " term : tactic
syntax (name := byCases) "byCases " (ident " : ")? term : tactic
syntax (name := byContra) "byContra " (colGt ident)? : tactic
syntax (name := typeCheck) "typeCheck " term : tactic
syntax (name := specialize) "specialize " ident (colGt term:arg)+ : tactic
syntax (name := rsimp) "rsimp" : tactic
syntax (name := compVal) "compVal" : tactic
syntax (name := async) "async " tacticSeq : tactic

syntax (name := unfreezingI) "unfreezingI " tacticSeq : tactic
syntax (name := resetI) "resetI" : tactic
syntax (name := substI) "substI " term : tactic
syntax (name := casesI) "casesI " casesTarget,+ (" using " ident)?
  (" with " binderIdent+)? : tactic
syntax (name := introI) "introI " (colGt (ident <|> "_"))* : tactic
syntax (name := introsI) "introsI " (colGt (ident <|> "_"))* : tactic
syntax (name := haveI) "haveI " Term.haveDecl : tactic
syntax (name := haveI') "haveI " Term.haveIdLhs : tactic
syntax (name := letI) "letI " Term.letDecl : tactic
syntax (name := letI') "letI " Term.haveIdLhs : tactic
syntax (name := exactI) "exactI " term : tactic

declare_syntax_cat rcasesPat
syntax rcasesPatMed := rcasesPat (" | " rcasesPat)*
syntax rcasesPatLo := rcasesPatMed (" : " term)?
syntax (name := rcasesPat.one) ident : rcasesPat
syntax (name := rcasesPat.ignore) "_" : rcasesPat
syntax (name := rcasesPat.clear) "-" : rcasesPat
syntax (name := rcasesPat.tuple) "⟨" rcasesPatLo,* "⟩" : rcasesPat
syntax (name := rcasesPat.paren) "(" rcasesPatLo ")" : rcasesPat
syntax (name := rcases?) "rcases?" casesTarget,* (" : " num)? : tactic
syntax (name := rcases) "rcases" casesTarget,* (" with " rcasesPat)? : tactic
syntax (name := obtain) "obtain" (ppSpace rcasesPat)? (" : " term)? (" := " term,+)? : tactic

declare_syntax_cat rintroPat
syntax (name := rintroPat.one) rcasesPat : rintroPat
syntax (name := rintroPat.binder) "(" (rintroPat+ <|> rcasesPatMed) (" : " term)? ")" : rintroPat
syntax (name := rintro?) "rintro?" (" : " num)? : tactic
syntax (name := rintro) "rintro" (ppSpace rintroPat)* (" : " term)? : tactic

syntax (name := ext1) "ext1 " rcasesPat* : tactic
syntax (name := ext1?) "ext1? " rcasesPat* : tactic
syntax (name := ext) "ext " rcasesPat* (":" num)? : tactic
syntax (name := ext?) "ext? " rcasesPat* (":" num)? : tactic

syntax (name := apply') "apply' " term : tactic
syntax (name := fapply') "fapply' " term : tactic
syntax (name := eapply') "eapply' " term : tactic
syntax (name := applyWith') "applyWith' " ("(" &"config" " := " term ")")? term : tactic
syntax (name := mapply') "mapply' " term : tactic
syntax (name := rfl') "rfl'" : tactic
syntax (name := symm') "symm'" (location)? : tactic
syntax (name := trans') "trans'" (term)? : tactic

syntax (name := fsplit) "fsplit" : tactic
syntax (name := injectionsAndClear) "injectionsAndClear" : tactic

syntax (name := fconstructor) "fconstructor" : tactic
syntax (name := tryFor) "tryFor " term:max tacticSeq : tactic
syntax (name := substs) "substs " ident* : tactic
syntax (name := unfoldCoes) "unfoldCoes " (location)? : tactic
syntax (name := unfoldWf) "unfoldWf" : tactic
syntax (name := unfoldAux) "unfoldAux" : tactic
syntax (name := recover) "recover" : tactic
syntax (name := «continue») "continue " tacticSeq : tactic
syntax (name := workOnGoal) "workOnGoal " num tacticSeq : tactic
syntax (name := swap) "swap " (num)? : tactic
syntax (name := rotate) "rotate " (num)? : tactic
syntax (name := clear_) "clear_" : tactic
syntax (name := replace) "replace " Term.haveDecl : tactic
syntax (name := replace') "replace " Term.haveIdLhs : tactic
syntax (name := classical) "classical" : tactic
syntax (name := generalizeHyp) "generalize " atomic(ident " : ")? term:51 " = " ident
  location : tactic
syntax (name := clean) "clean " term : tactic
syntax (name := refineStruct) "refineStruct " term : tactic
syntax (name := matchHyp) "matchHyp " ("(" &"m" " := " term ")")? ident " : " term : tactic
syntax (name := guardExprStrict) "guardExpr " term:51 " == " term : tactic
syntax (name := guardTargetStrict) "guardTarget" " == " term : tactic
syntax (name := guardHypNums) "guardHypNums " num : tactic
syntax (name := guardTags) "guardTags " ident* : tactic
syntax (name := guardProofTerm) "guardProofTerm " tactic:51 " => " term : tactic
syntax (name := failIfSuccess?) "failIfSuccess? " str tacticSeq : tactic
syntax (name := field) "field " ident " => " tacticSeq : tactic
syntax (name := haveField) "haveField" : tactic
syntax (name := applyField) "applyField" : tactic
syntax (name := applyRules) "applyRules" ("(" &"config" " := " term ")")?
  "[" term,* "]" (num)? : tactic
syntax (name := hGeneralize) "hGeneralize " atomic(binderIdent " : ")? term:51 " = " ident
  (" with " binderIdent)? : tactic
syntax (name := hGeneralize!) "hGeneralize! " atomic(binderIdent " : ")? term:51 " = " ident
  (" with " binderIdent)? : tactic
syntax (name := guardExprEq') "guardExpr " term:51 " = " term : tactic
syntax (name := guardTarget') "guardTarget" " = " term : tactic
syntax (name := triv) "triv" : tactic
syntax (name := use) "use " term,+ : tactic
syntax (name := clearAuxDecl) "clearAuxDecl" : tactic
syntax (name := set) "set " ident (" : " term)? " := " term (" with " "←"? ident)? : tactic
syntax (name := set!) "set! " ident (" : " term)? " := " term (" with " "←"? ident)? : tactic
syntax (name := clearExcept) "clear" "*" " - " ident* : tactic
syntax (name := extractGoal) "extractGoal " (ident)? (" with " ident*)? : tactic
syntax (name := extractGoal!) "extractGoal! " (ident)? (" with " ident*)? : tactic
syntax (name := inhabit) "inhabit " atomic(ident " : ")? term : tactic
syntax (name := revertDeps) "revertDeps " ident* : tactic
syntax (name := revertAfter) "revertAfter " ident : tactic
syntax (name := revertTargetDeps) "revertTargetDeps" : tactic
syntax (name := clearValue) "clearValue " ident* : tactic

syntax (name := applyAssumption) "applyAssumption" : tactic
syntax (name := solveByElim) "solveByElim" "*"? ppSpace ("(" &"config" " := " term ")")?
  (&"only ")? ("[" simpArg,* "]")? (" with " ident+)? : tactic

syntax (name := hint) "hint" : tactic

syntax (name := clear!) "clear! " ident* : tactic

syntax (name := choose) "choose " ident+ (" using " term)? : tactic
syntax (name := choose!) "choose! " ident+ (" using " term)? : tactic

syntax (name := congr) "congr " (colGt num)? (" with " (colGt rcasesPat)* (" : " num)?)? : tactic
syntax (name := rcongr) "rcongr " (colGt rcasesPat)* : tactic
syntax (name := convert) "convert " "← "? term (" using " num)? : tactic
syntax (name := convertTo) "convertTo " term (" using " num)? : tactic
syntax (name := acChange) "acChange " term (" using " num)? : tactic

syntax (name := decide!) "decide!" : tactic

syntax (name := deltaInstance) "deltaInstance " ident* : tactic

syntax (name := elide) "elide " num (location)? : tactic
syntax (name := unelide) "unelide " (location)? : tactic

syntax (name := clarify) "clarify " ("(" &"config" " := " term ")")?
  ("[" Parser.Tactic.simpArg,* "]")? (" using " term,+)? : tactic
syntax (name := safe) "safe " ("(" &"config" " := " term ")")?
  ("[" Parser.Tactic.simpArg,* "]")? (" using " term,+)? : tactic
syntax (name := finish) "finish " ("(" &"config" " := " term ")")?
  ("[" Parser.Tactic.simpArg,* "]")? (" using " term,+)? : tactic

syntax generalizesArg := (ident " : ")? term:51 " = " ident
syntax (name := generalizes) "generalizes " "[" generalizesArg,* "]" : tactic

syntax (name := generalizeProofs) "generalizeProofs " (colGt binderIdent)* (location)? : tactic

syntax (name := itauto) "itauto" : tactic

syntax (name := lift) "lift " term " to " term
  (" using " term)? (" with " binderIdent+)? : tactic

syntax (name := pushCast) "pushCast "
  ("[" Parser.Tactic.simpArg,* "]")? (location)? : tactic
syntax (name := normCast) "normCast " (location)? : tactic
syntax (name := rwModCast) "rwModCast " rwRuleSeq (location)? : tactic
syntax (name := exactModCast) "exactModCast " term : tactic
syntax (name := applyModCast) "applyModCast " term : tactic
syntax (name := assumptionModCast) "assumptionModCast" : tactic

syntax (name := prettyCases) "prettyCases" : tactic

syntax (name := pushNeg) "pushNeg " (location)? : tactic

syntax (name := contrapose) "contrapose " (ident (" with " ident)?)? : tactic
syntax (name := contrapose!) "contrapose! " (ident (" with " ident)?)? : tactic

syntax (name := renameVar) "renameVar " ident " → " ident (location)? : tactic

syntax (name := assocRw) "assocRw " rwRuleSeq (location)? : tactic

syntax (name := showTerm) "showTerm " tacticSeq : tactic

syntax (name := simpRw) "simpRw " rwRuleSeq (location)? : tactic

syntax (name := dsimpResult) "dsimpResult " (&"only ")? ("[" Tactic.simpArg,* "]")?
  (" with " ident+)? " => " tacticSeq : tactic
syntax (name := simpResult) "simpResult " (&"only ")? ("[" Tactic.simpArg,* "]")?
  (" with " ident+)? " => " tacticSeq : tactic

syntax (name := simpa) "simpa " ("(" &"config" " := " term ")")? (&"only ")?
  ("[" Tactic.simpArg,* "]")? (" with " (colGt ident)+)? (" using " term)? : tactic
syntax (name := simpa!) "simpa! " ("(" &"config" " := " term ")")? (&"only ")?
  ("[" Tactic.simpArg,* "]")? (" with " (colGt ident)+)? (" using " term)? : tactic
syntax (name := simpa?) "simpa? " ("(" &"config" " := " term ")")? (&"only ")?
  ("[" Tactic.simpArg,* "]")? (" with " (colGt ident)+)? (" using " term)? : tactic
syntax (name := simpa!?) "simpa!? " ("(" &"config" " := " term ")")? (&"only ")?
  ("[" Tactic.simpArg,* "]")? (" with " (colGt ident)+)? (" using " term)? : tactic

syntax (name := splitIfs) "splitIfs " (location)? (" with " binderIdent+)? : tactic

syntax (name := squeezeScope) "squeezeScope " tacticSeq : tactic
syntax (name := squeezeSimp) "squeezeSimp " ("(" &"config" " := " term ")")? (&"only ")?
  ("[" simpArg,* "]")? (" with " (colGt ident)+)? (location)? : tactic
syntax (name := squeezeSimp?) "squeezeSimp? " ("(" &"config" " := " term ")")? (&"only ")?
  ("[" simpArg,* "]")? (" with " (colGt ident)+)? (location)? : tactic
syntax (name := squeezeSimp!) "squeezeSimp! " ("(" &"config" " := " term ")")? (&"only ")?
  ("[" simpArg,* "]")? (" with " (colGt ident)+)? (location)? : tactic
syntax (name := squeezeSimp?!) "squeezeSimp?! " ("(" &"config" " := " term ")")? (&"only ")?
  ("[" simpArg,* "]")? (" with " (colGt ident)+)? (location)? : tactic
syntax (name := squeezeSimpa) "squeezeSimpa " ("(" &"config" " := " term ")")? (&"only ")?
  ("[" simpArg,* "]")? (" with " (colGt ident)+)? (" using " term)? : tactic
syntax (name := squeezeSimpa?) "squeezeSimpa? " ("(" &"config" " := " term ")")? (&"only ")?
  ("[" simpArg,* "]")? (" with " (colGt ident)+)? (" using " term)? : tactic
syntax (name := squeezeSimpa!) "squeezeSimpa! " ("(" &"config" " := " term ")")? (&"only ")?
  ("[" simpArg,* "]")? (" with " (colGt ident)+)? (" using " term)? : tactic
syntax (name := squeezeSimpa?!) "squeezeSimpa?! " ("(" &"config" " := " term ")")? (&"only ")?
  ("[" simpArg,* "]")? (" with " (colGt ident)+)? (" using " term)? : tactic
syntax (name := squeezeDSimp) "squeezeDSimp " ("(" &"config" " := " term ")")? (&"only ")?
  ("[" simpArg,* "]")? (" with " (colGt ident)+)? (location)? : tactic
syntax (name := squeezeDSimp?) "squeezeDSimp? " ("(" &"config" " := " term ")")? (&"only ")?
  ("[" simpArg,* "]")? (" with " (colGt ident)+)? (location)? : tactic
syntax (name := squeezeDSimp!) "squeezeDSimp! " ("(" &"config" " := " term ")")? (&"only ")?
  ("[" simpArg,* "]")? (" with " (colGt ident)+)? (location)? : tactic
syntax (name := squeezeDSimp?!) "squeezeDSimp?! " ("(" &"config" " := " term ")")? (&"only ")?
  ("[" simpArg,* "]")? (" with " (colGt ident)+)? (location)? : tactic

syntax (name := suggest) "suggest " ("(" &"config" " := " term ")")? (num)?
  ("[" simpArg,* "]")? (" with " (colGt ident)+)? : tactic
syntax (name := librarySearch) "librarySearch " ("(" &"config" " := " term ")")?
  ("[" simpArg,* "]")? (" with " (colGt ident)+)? : tactic
syntax (name := librarySearch!) "librarySearch! " ("(" &"config" " := " term ")")?
  ("[" simpArg,* "]")? (" with " (colGt ident)+)? : tactic

syntax (name := tauto) "tauto " ("(" &"config" " := " term ")")? : tactic
syntax (name := tauto!) "tauto! " ("(" &"config" " := " term ")")? : tactic

syntax (name := truncCases) "truncCases " term (" with " (colGt ident)+)? : tactic

syntax (name := normNum1) "normNum1 " (location)? : tactic
syntax (name := normNum) "normNum " ("[" simpArg,* "]")? (location)? : tactic
syntax (name := applyNormed) "applyNormed " term : tactic

syntax (name := abel1) "abel1" : tactic
syntax (name := abel) "abel " (&"raw" <|> &"term")? (location)? : tactic

syntax (name := ring1) "ring1" : tactic
syntax (name := ring1!) "ring1!" : tactic

syntax ringMode := &"SOP" <|> &"raw" <|> &"horner"
syntax (name := ringNF) "ringNF" (ringMode)? (location)? : tactic
syntax (name := ringNF!) "ringNF!" (ringMode)? (location)? : tactic
syntax (name := ring) "ring" : tactic
syntax (name := ring!) "ring!" : tactic

syntax (name := ringExpEq) "ringExpEq" : tactic
syntax (name := ringExpEq!) "ringExpEq!" : tactic
syntax (name := ringExp) "ringExp" (location)? : tactic
syntax (name := ringExp!) "ringExp!" (location)? : tactic

syntax (name := noncommRing) "noncommRing" : tactic

syntax (name := linarith) "linarith " ("(" &"config" " := " term ")")?
  (&"only ")? ("[" term,* "]")? : tactic
syntax (name := linarith!) "linarith! " ("(" &"config" " := " term ")")?
  (&"only ")? ("[" term,* "]")? : tactic
syntax (name := nlinarith) "nlinarith " ("(" &"config" " := " term ")")?
  (&"only ")? ("[" term,* "]")? : tactic
syntax (name := nlinarith!) "nlinarith! " ("(" &"config" " := " term ")")?
  (&"only ")? ("[" term,* "]")? : tactic

syntax (name := omega) "omega" (&" manual")? (&" nat" <|> &" int")? : tactic

end Tactic

namespace Attr

syntax (name := intro) "intro" : attr
syntax (name := intro!) "intro!" : attr

syntax (name := nolint) "nolint " ident* : attr

syntax extParam.arrow := "(" "·" " → " "·" ")"
syntax extParam := "-"? (extParam.arrow <|> "*" <|> ident)
syntax (name := ext) "ext " (extParam <|> "[" extParam,* "]")? : tactic

syntax (name := higherOrder) "higherOrder " (ident)? : attr
syntax (name := interactive) "interactive" : attr

syntax (name := mkIff) "mkIff " (ident)? : attr

syntax (name := normCast) "normCast " (&"elim" <|> &"move" <|> &"squash")? : attr

syntax (name := protectProj) "protectProj " (&"without" ident+)? : attr

syntax (name := notationClass) "notationClass " "*"? (ident)? : attr

syntax (name := simps) "simps " ("(" &"config" " := " term ")")? ident* : attr
syntax (name := simps?) "simps? " ("(" &"config" " := " term ")")? ident* : attr

end Attr

namespace Command

namespace Lint

syntax verbosity := "-" <|> "+"
syntax opts := (verbosity "*"?) <|> ("*"? (verbosity)?)
syntax args := opts " only"? ident*

end Lint

syntax (name := lint) "#lint" Lint.args : command
syntax (name := lintMathlib) "#lint_mathlib" Lint.args : command
syntax (name := lintAll) "#lint_all" Lint.args : command
syntax (name := listLinters) "#list_linters" : command

syntax (name := copyDocString) "copy_doc_string " ident " → " ident* : command
syntax (name := libraryNote) docComment "library_note " str : command
syntax (name := addTacticDoc) (docComment)? "add_tactic_doc " term : command
syntax (name := addDeclDoc) docComment "add_decl_doc " ident : command

syntax (name := setupTacticParser) "setup_tactic_parser" : command
syntax (name := importPrivate) "import_private " ident ("from " ident)? : command
syntax (name := mkSimpAttribute) "mk_simp_attribute " ident
  ("from " ident+)? (" := " str)? : command

syntax (name := addHintTactic) "add_hint_tactic " tactic : command
syntax (name := alias) "alias " ident " ← " ident* : command
syntax (name := aliasLR) "alias " ident " ↔ " (".." <|> (binderIdent binderIdent)) : command

syntax (name := explode) "#explode " ident : command

syntax (name := find) "#find " term : command

syntax (name := listUnusedDecls) "#list_unused_decls" : command
syntax (name := mkIffOfInductiveProp) "mk_iff_of_inductive_prop" ident ident : command

syntax (name := defReplacer) "def_replacer " ident Term.optType : command

syntax (name := restateAxiom) "restate_axiom " ident (ident)? : command

syntax (name := simp) "#simp " (&"only ")? ("[" Tactic.simpArg,* "]")?
  (" with " ident+)? " : "? term : tactic

syntax simpsRule.rename := ident " → " ident
syntax simpsRule.erase := "-" ident
syntax simpsRule := (simpsRule.rename <|> simpsRule.erase) " as_prefix"
syntax (name := initializeSimpsProjections) "initialize_simps_projections "
  (ident ("(" simpsRule,+ ")")?)* : tactic
syntax (name := initializeSimpsProjections?) "initialize_simps_projections? "
  (ident ("(" simpsRule,+ ")")?)* : tactic

syntax (name := «where») "#where" : command

end Command
