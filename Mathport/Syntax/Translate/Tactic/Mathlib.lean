/-
Copyright (c) 2021 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
import Mathport.Syntax.Translate.Tactic.Basic
import Mathport.Syntax.Translate.Tactic.Lean3

open Lean
open Lean.Elab.Tactic (Location)

namespace Mathport.Translate.Tactic
open AST3 Parser

-- # tactic.cache

@[trTactic unfreezingI] def trUnfreezingI : TacM Syntax := do
  `(tactic| unfreezingI $(← trBlock (← itactic)):tacticSeq)

@[trTactic resetI] def trResetI : TacM Syntax := `(tactic| resetI)

@[trTactic substI] def trSubstI : TacM Syntax := do
  `(tactic| substI $(← trExpr (← parse pExpr)))

@[trTactic casesI] def trCasesI : TacM Syntax := do
  let (hp, e) ← parse casesArg
  let e ← trExpr e
  let ids ← parse withIdentList
  match ids with
  | #[] => `(tactic| casesI $[$(hp.map mkIdent) :]? $e)
  | _ => `(tactic| casesI $[$(hp.map mkIdent) :]? $e with $[$(ids.map trBinderIdent)]*)

@[trTactic introI] def trIntroI : TacM Syntax := do
  match ← parse ident_ ? with
  | some (BinderName.ident h) => `(tactic| introI $(mkIdent h):ident)
  | _ => `(tactic| introI)

@[trTactic introsI] def trIntrosI : TacM Syntax := do
  match ← parse ident_* with
  | #[] => `(tactic| introsI)
  | hs => `(tactic| introI $(hs.map trIdent_)*)

@[trTactic haveI] def trHaveI : TacM Syntax := do
  let h ← parse (ident)?
  let h := mkNullNode $ match h with | none => #[] | some h => #[mkIdent h, mkNullNode]
  let ty := mkOptionalNode $ ← trOptType (← parse (tk ":" *> pExpr)?)
  match ← parse (tk ":=" *> pExpr)? with
  | some pr =>
    let haveId := mkNode ``Parser.Term.haveIdDecl #[h, ty, mkAtom ":=", ← trExpr pr]
    `(tactic| haveI $haveId:haveIdDecl)
  | none => mkNode ``Parser.Tactic.haveI' #[mkAtom "haveI", h, ty]

@[trTactic letI] def trLetI : TacM Syntax := do
  let h ← parse (ident)?
  let ty := mkOptionalNode $ ← trOptType (← parse (tk ":" *> pExpr)?)
  match ← parse (tk ":=" *> pExpr)? with
  | some pr =>
    let letId := mkNode ``Parser.Term.letIdDecl #[
      mkIdent (h.getD `this), ty, mkAtom ":=", ← trExpr pr]
    `(tactic| letI $letId:letIdDecl)
  | none =>
    let h := mkNullNode $ match h with | none => #[] | some h => #[mkIdent h, mkNullNode]
    mkNode ``Parser.Tactic.letI' #[mkAtom "letI", h, ty]

@[trTactic exactI] def trExactI : TacM Syntax := do
  `(tactic| exactI $(← trExpr (← parse pExpr)))

-- # tactic.lint

@[trUserAttr nolint] def trNolintAttr : TacM Syntax := do
  `(attr| nolint $[$((← parse ident*).map mkIdent)]*)

@[trUserAttr linter] def trLinterAttr : TacM Syntax := parse () *> `(attr| linter)

def trLintFast (fast : Bool) : Syntax := mkNullNode (if fast then #[mkAtom "*"] else #[])

def trLintVerb : LintVerbosity → Option Syntax
  | LintVerbosity.medium => none
  | LintVerbosity.low => some $ mkNode ``Parser.Command.Lint.verbosity #[mkAtom "-"]
  | LintVerbosity.high => some $ mkNode ``Parser.Command.Lint.verbosity #[mkAtom "+"]

def trLintOpts : Bool × LintVerbosity → Syntax
  | (fast, verb) => match trLintVerb verb with
    | none => mkNode ``Parser.Command.Lint.opts #[trLintFast fast, mkNullNode]
    | some v => mkNode ``Parser.Command.Lint.opts #[v, trLintFast fast]

def trLintArgs : (Bool × LintVerbosity) × Bool × Array Name → Syntax
  | (opts, use_only, extra) =>
    mkNode ``Parser.Command.Lint.args #[
      trLintOpts opts,
      mkNullNode $ if use_only then #[mkAtom "only"] else #[],
      mkNullNode $ extra.map mkIdent]

@[trUserCmd «#lint»] def trLintCmd : TacM Syntax := do
  `(command| #lint $(trLintArgs $ ← parse lintArgs))

@[trUserCmd «#lint_mathlib»] def trLintMathlibCmd : TacM Syntax := do
  `(command| #lint_mathlib $(trLintArgs $ ← parse lintArgs))

@[trUserCmd «#lint_all»] def trLintAllCmd : TacM Syntax := do
  `(command| #lint_all $(trLintArgs $ ← parse lintArgs))

@[trUserCmd «#list_linters»] def trListLintersCmd : TacM Syntax :=
  parse () *> `(command| #list_linters)

-- # tactic.doc_commands

@[trUserCmd «copy_doc_string»] def trCopyDocString : TacM Syntax := do
  let (fr, to) ← parse $ do (← ident, ← tk "→" *> ident*)
  `(command| copy_doc_string $(← mkIdentI fr) → $(← liftM $ to.mapM mkIdentI)*)

@[trUserCmd «library_note»] def trLibraryNote (doc : Option String) : TacM Syntax := do
  let Expr.string s ← parse pExpr | throw! "unsupported: weird string"
  `(command| $(trDocComment doc.get!):docComment library_note $(Syntax.mkStrLit s))

@[trUserCmd «add_tactic_doc»] def trAddTacticDoc (doc : Option String) : TacM Syntax := do
  `(command| $[$(doc.map trDocComment)]? add_tactic_doc $(← trExpr (← parse pExpr)))

@[trUserCmd «add_decl_doc»] def trAddDeclDoc (doc : Option String) : TacM Syntax := do
  `(command| $(trDocComment doc.get!):docComment add_decl_doc $(← mkIdentI (← parse ident)))

-- # tactic.rcases

mutual

partial def trRCasesPat : RCasesPat → M Syntax
  | RCasesPat.one BinderName._ => `(rcasesPat| _)
  | RCasesPat.one (BinderName.ident x) => `(rcasesPat| $(mkIdent x):ident)
  | RCasesPat.clear => do `(rcasesPat| -)
  | RCasesPat.tuple pats => do `(rcasesPat| ⟨$(← pats.mapM trRCasesPatLo),*⟩)
  | RCasesPat.alts #[pat] => trRCasesPat pat
  | pat => do `(rcasesPat| ($(← trRCasesPatLo pat)))

partial def trRCasesPatMed (pat : RCasesPat) : M Syntax := do
  let (fst, rest) ← match pat with
  | RCasesPat.alts pats =>
      (pats[0], ← pats[1:].toArray.mapM fun pat => do
        mkNullNode #[mkAtom "|", ← trRCasesPat pat])
  | pat => (pat, #[])
  mkNode ``Parser.Tactic.rcasesPatMed #[← trRCasesPat fst, mkNullNode rest]

partial def trRCasesPatLo (pat : RCasesPat) : M Syntax := do
  let (pat, ty) ← match pat with
  | RCasesPat.typed pat ty => (pat, mkNullNode #[mkAtom ":", ← trExpr ty])
  | _ => (pat, mkNullNode)
  Syntax.node ``Parser.Tactic.rcasesPatLo #[← trRCasesPatMed pat, ty]

end

@[trTactic rcases] def trRCases : TacM Syntax := do
  match ← parse rcasesArgs with
  | RCasesArgs.hint es depth => do
    let es := match es with | Sum.inl e => #[e] | Sum.inr es => es
    `(tactic| rcases? $[$(← liftM $ es.mapM trExpr):term],*
      $[: $(depth.map fun n => Syntax.mkNumLit (toString n))]?)
  | RCasesArgs.rcases n e pat => do
    `(tactic| rcases $[$(n.map mkIdent):ident :]? $(← trExpr e):term
              with $(← trRCasesPat pat):rcasesPat)
  | RCasesArgs.rcasesMany es pat => liftM $ show M _ from do
    `(tactic| rcases $[$(← es.mapM trExpr):term],* with $(← trRCasesPat pat):rcasesPat)

@[trTactic obtain] def trObtain : TacM Syntax := do
  let ((pat, tp), vals) ← parse obtainArg
  liftM $ show M _ from do
    `(tactic| obtain $[$(← pat.mapM trRCasesPat)]? $[: $(← tp.mapM trExpr)]?
      $[:= $[$(← vals.mapM (·.mapM trExpr))],*]?)

partial def trRIntroPat : RIntroPat → M Syntax
  | RIntroPat.one pat => do `(rintroPat| $(← trRCasesPat pat):rcasesPat)
  | RIntroPat.binder pats ty => do
    `(rintroPat| ($[$(← pats.mapM trRIntroPat):rintroPat]* $[: $(← ty.mapM trExpr)]?))
  | RIntroPat.pat pat ty => do
    mkNode ``Parser.Tactic.rintroPat.binder #[mkAtom "(", ← trRCasesPatMed pat,
      mkNullNode (← match ty with | none => #[] | some ty => do #[mkAtom ":", ← trExpr ty]),
      mkAtom ")"]

@[trTactic rintro rintros] def trRIntro : TacM Syntax := do
  liftM $ match ← parse rintroArg with
  | Sum.inr depth => `(tactic| rintro? $[: $(depth.map fun n => Syntax.mkNumLit (toString n))]?)
  | Sum.inl (pats, ty) => show M _ from do
    `(tactic| rintro $[$(← pats.mapM trRIntroPat):rintroPat]* $[: $(← ty.mapM trExpr)]?)

-- # tactic.ext

def trExtParam' : ExtParam → M Syntax
  | ExtParam.arrow => mkNode ``Parser.Attr.extParam.arrow #[
    mkAtom "(", mkAtom "·", mkAtom "→", mkAtom "·", mkAtom ")"]
  | ExtParam.all => mkAtom "*"
  | ExtParam.ident n => mkIdentI n

def trExtParam : Bool × ExtParam → M Syntax
  | (sym, p) => do
    mkNode ``Parser.Attr.extParam #[
      mkNullNode (if sym then #[mkAtom "-"] else #[]), ← trExtParam' p]

def trExtParams : Array (Bool × ExtParam) → M Syntax
  | #[] => mkNullNode
  | #[p] => do mkNullNode #[← trExtParam p]
  | ps => do mkNullNode #[mkAtom "[", mkNullNode (← ps.mapM trExtParam), mkAtom "]"]

@[trUserAttr ext] def trExtAttr : TacM Syntax := do
  mkNode ``Parser.Attr.ext #[mkAtom "ext", ← trExtParams (← parse extParams)]

@[trTactic ext1] def trExt1 : TacM Syntax := do
  let hint ← parse (tk "?")?
  let pats ← liftM $ (← parse (rcasesPat true)*).mapM trRCasesPat
  match hint with
  | none => `(tactic| ext1 $pats*)
  | some _ => `(tactic| ext1? $pats*)

@[trTactic ext] def trExt : TacM Syntax := do
  let hint ← parse (tk "?")?
  let pats ← liftM $ (← parse (rcasesPat true)*).mapM trRCasesPat
  let depth := (← parse (tk ":" *> smallNat)?).map fun n => Syntax.mkNumLit (toString n)
  match hint with
  | none => `(tactic| ext $pats* $[: $depth]?)
  | some _ => `(tactic| ext? $pats* $[: $depth]?)

-- # tactic.apply

@[trTactic apply'] def trApply' : TacM Syntax := do
  `(tactic| apply' $(← trExpr (← parse pExpr)))

@[trTactic fapply'] def trFApply' : TacM Syntax := do
  `(tactic| fapply' $(← trExpr (← parse pExpr)))

@[trTactic eapply'] def trEApply' : TacM Syntax := do
  `(tactic| eapply' $(← trExpr (← parse pExpr)))

@[trTactic apply_with'] def trApplyWith' : TacM Syntax := do
  `(tactic| applyWith' $(← trExpr (← parse pExpr)))

@[trTactic mapply'] def trMApply' : TacM Syntax := do
  `(tactic| mapply' $(← trExpr (← parse pExpr)))

@[trTactic reflexivity' refl'] def trRefl' : TacM Syntax := `(tactic| rfl')

@[trTactic symmetry'] def trSymmetry' : TacM Syntax := `(tactic| symm')

@[trTactic transitivity'] def trTransitivity' : TacM Syntax := do
  `(tactic| trans' $[$(← liftM $ (← parse (pExpr)?).mapM trExpr)]?)

-- # tactic.core

@[trTactic fsplit] def trFSplit : TacM Syntax := `(tactic| fsplit)

@[trTactic injections_and_clear] def trInjectionsAndClear : TacM Syntax :=
  `(tactic| injectionsAndClear)

@[trUserCmd «run_parser»] def trRunParser : TacM Syntax := do
  throw! "unsupported: run_parser" -- unattested

@[trUserAttr higher_order] def trHigherOrderAttr : TacM Syntax := do
  `(attr| higherOrder $(← liftM $ (← parse (ident)?).mapM mkIdentI)?)

@[trUserAttr interactive] def trInteractiveAttr : TacM Syntax :=
  parse () *> `(attr| interactive)

@[trUserCmd «setup_tactic_parser»] def trSetupTacticParser : TacM Syntax :=
  parse () *> `(command| setup_tactic_parser)

def trInterpolatedStr' := trInterpolatedStr fun stx => `(← $stx)

@[trUserNota tactic.pformat_macro] def trPFormatMacro : TacM Syntax := do
  `(f! $(← trInterpolatedStr'))

@[trUserNota tactic.fail_macro] def trFailMacro : TacM Syntax := do
  `(throwError $(← trInterpolatedStr'))

@[trUserNota tactic.trace_macro] def trTraceMacro : TacM Syntax := do
  let stx ← trInterpolatedStr'; `(← do dbg_trace $stx)

@[trUserCmd «import_private»] def trImportPrivate : TacM Syntax := do
  let (n, fr) ← parse $ do (← ident, ← (tk "from" *> ident)?)
  `(import_private $(← mkIdentF n) $[from $(← liftM $ fr.mapM mkIdentI)]?)

-- FIXME: don't use with_ident_list here in mathlib
@[trUserCmd «mk_simp_attribute»] def trMkSimpAttribute : TacM Syntax := do
  let (n, d, withList) ← parse $ do (← ident, ← pExpr, ← (tk "with" *> ident*)?)
  let d ← match d.unparen with
  | AST3.Expr.const _ ⟨_, _, `none⟩ _ => pure $ none
  | AST3.Expr.string s => pure $ some (Syntax.mkStrLit s)
  | _ => throw! "unsupported: weird string"
  `(command| mk_simp_attribute $(mkIdent n) $[from $(withList.map (·.map mkIdent))*]? $[:= $d]?)

-- # tactic.interactive

@[trTactic fconstructor] def trFConstructor : TacM Syntax := `(tactic| fconstructor)

@[trTactic try_for] def trTryFor : TacM Syntax := do
  `(tactic| tryFor $(← trExpr (← parse pExpr)) $(← trBlock (← itactic)):tacticSeq)

@[trTactic substs] def trSubsts : TacM Syntax := do
  `(tactic| substs $((← parse ident*).map mkIdent)*)

@[trTactic unfold_coes] def trUnfoldCoes : TacM Syntax := do
  `(tactic| unfoldCoes $(← trLoc (← parse location))?)

@[trTactic unfold_wf] def trUnfoldWf : TacM Syntax := `(tactic| unfoldWf)

@[trTactic unfold_aux] def trUnfoldAux : TacM Syntax := `(tactic| unfoldAux)

@[trTactic recover] def trRecover : TacM Syntax := `(tactic| recover)

@[trTactic «continue»] def trContinue : TacM Syntax := do
  `(tactic| continue $(← trBlock (← itactic)):tacticSeq)

@[trTactic id] def trId : TacM Syntax := do trIdTactic (← itactic)

@[trTactic work_on_goal] def trWorkOnGoal : TacM Syntax := do
  `(tactic| workOnGoal
    $(Syntax.mkNumLit (toString (← parse smallNat)))
    $(← trBlock (← itactic)):tacticSeq)

@[trTactic swap] def trSwap : TacM Syntax := do
  let e ← (← expr?).mapM fun
  | AST3.Expr.nat n => Syntax.mkNumLit (toString n)
  | _ => throw! "unsupported: weird nat"
  `(tactic| swap $(e)?)

@[trTactic rotate] def trRotate : TacM Syntax := do
  let e ← (← expr?).mapM fun
  | AST3.Expr.nat n => Syntax.mkNumLit (toString n)
  | _ => throw! "unsupported: weird nat"
  `(tactic| rotate $(e)?)

@[trTactic clear_] def trClear_ : TacM Syntax := `(tactic| clear_)

@[trTactic replace] def trReplace : TacM Syntax := do
  let h ← parse (ident)?
  let h := mkNullNode $ match h with | none => #[] | some h => #[mkIdent h, mkNullNode]
  let ty := mkOptionalNode $ ← trOptType (← parse (tk ":" *> pExpr)?)
  match ← parse (tk ":=" *> pExpr)? with
  | some pr =>
    let haveId := mkNode ``Parser.Term.haveIdDecl #[h, ty, mkAtom ":=", ← trExpr pr]
    `(tactic| replace $haveId:haveIdDecl)
  | none => mkNode ``Parser.Tactic.replace' #[mkAtom "replace", h, ty]

@[trTactic classical] def trClassical : TacM Syntax := `(tactic| classical)

@[trTactic generalize_hyp] def trGeneralizeHyp : TacM Syntax := do
  let h := (← parse (ident)?).map mkIdent
  parse (tk ":")
  let (e, x) ← parse generalizeArg
  let e ← trExpr e; let x := mkIdent x
  match ← trLoc (← parse location) with
  | none => `(tactic| generalize $[$h :]? $e = $x)
  | some loc => `(tactic| generalize $[$h :]? $e = $x $loc)

@[trTactic clean] def trClean : TacM Syntax := do
  `(tactic| clean $(← trExpr (← parse pExpr)))

@[trTactic refine_struct] def trRefineStruct : TacM Syntax := do
  `(tactic| refineStruct $(← trExpr (← parse pExpr)))

@[trTactic guard_hyp'] def trGuardHyp' : TacM Syntax := do
  `(tactic| guardHyp $(mkIdent (← parse ident)) : $(← trExpr (← parse (tk ":" *> pExpr))))

@[trTactic match_hyp] def trMatchHyp : TacM Syntax := do
  let h := mkIdent (← parse ident)
  let ty ← trExpr (← parse (tk ":" *> pExpr))
  let m ← liftM $ (← expr?).mapM trExpr
  `(tactic| matchHyp $[(m := $m)]? $h : $ty)

@[trTactic guard_expr_strict] def trGuardExprStrict : TacM Syntax := do
  let t ← expr!
  let p ← parse (tk ":=" *> pExpr)
  `(tactic| guardExpr $(← trExpr t) == $(← trExpr p))

@[trTactic guard_target_strict] def trGuardTargetStrict : TacM Syntax := do
  `(tactic| guardTarget == $(← trExpr (← parse pExpr)))

@[trTactic guard_hyp_strict] def trGuardHypStrict : TacM Syntax := do
  `(tactic| guardHyp $(mkIdent (← parse ident)) : $(← trExpr (← parse (tk ":" *> pExpr))))

@[trTactic guard_hyp_nums] def trGuardHypNums : TacM Syntax := do
  match (← expr!).unparen with
  | AST3.Expr.nat n => `(tactic| guardHypNums $(Syntax.mkNumLit (toString n)))
  | _ => throw! "unsupported: weird nat"

@[trTactic guard_tags] def trGuardTags : TacM Syntax := do
  `(tactic| guardTags $((← parse ident*).map mkIdent)*)

@[trTactic guard_proof_term] def trGuardProofTerm : TacM Syntax := do
  `(tactic| guardProofTerm $(← trIdTactic (← itactic)) => $(← trExpr (← parse pExpr)))

@[trTactic success_if_fail_with_msg] def trSuccessIfFailWithMsg : TacM Syntax := do
  let t ← trBlock (← itactic)
  match (← expr!).unparen with
  | AST3.Expr.string s => `(tactic| failIfSuccess? $(Syntax.mkStrLit s) $t:tacticSeq)
  | _ => throw! "unsupported: weird string"

@[trTactic field] def trField : TacM Syntax := do
  `(tactic| field $(mkIdent (← parse ident)) => $(← trBlock (← itactic)):tacticSeq)

@[trTactic have_field] def trHaveField : TacM Syntax := `(tactic| haveField)

@[trTactic apply_field] def trApplyField : TacM Syntax := `(tactic| applyField)

@[trTactic apply_rules] def trApplyRules : TacM Syntax := do
  let hs ← liftM $ (← parse pExprListOrTExpr).mapM trExpr
  let n ← (← expr?).mapM fun
  | AST3.Expr.nat n => Syntax.mkNumLit (toString n)
  | _ => throw! "unsupported: weird nat"
  let cfg ← liftM $ (← expr?).mapM trExpr
  `(tactic| applyRules $[(config := $cfg)]? [$hs,*] $(n)?)

@[trTactic h_generalize] def trHGeneralize : TacM Syntax := do
  let rev ← parse (tk "!")?
  let h := (← parse (ident_)?).map trBinderIdent
  let (e, x) ← parse (tk ":") *> parse hGeneralizeArg
  let e ← trExpr e; let x := mkIdent x
  let eqsH := (← parse (tk "with" *> ident_)?).map trBinderIdent
  match rev with
  | none => `(tactic| hGeneralize $[$h :]? $e = $x $[with $eqsH]?)
  | some _ => `(tactic| hGeneralize! $[$h :]? $e = $x $[with $eqsH]?)

@[trTactic guard_expr_eq'] def trGuardExprEq' : TacM Syntax := do
  `(tactic| guardExpr $(← trExpr (← expr!)) = $(← trExpr (← parse (tk ":=" *> pExpr))))

@[trTactic guard_target'] def trGuardTarget' : TacM Syntax := do
  `(tactic| guardTarget = $(← trExpr (← parse pExpr)))

@[trTactic triv] def trTriv : TacM Syntax := `(tactic| triv)

@[trTactic use] def trUse : TacM Syntax := do
  `(tactic| use $(← liftM $ (← parse pExprListOrTExpr).mapM trExpr),*)

@[trTactic clear_aux_decl] def trClearAuxDecl : TacM Syntax := `(tactic| clearAuxDecl)

attribute [trTactic change'] trChange

@[trTactic set] def trSet : TacM Syntax := do
  let hSimp := (← parse (tk "!")?).isSome
  let a ← parse ident
  let ty ← parse (tk ":" *> pExpr)?
  let val ← parse (tk ":=") *> parse pExpr
  let revName := match ← parse (tk "with" *> do (← (tk "←")?, ← ident))? with
    | none => #[]
    | some (flip, id) => #[mkAtom "with",
        mkNullNode $ if flip.isSome then #[mkAtom "←"] else #[], mkIdent id]
  let (tac, s) := if hSimp then (``Parser.Tactic.set!, "set!") else (``Parser.Tactic.set, "set")
  mkNode tac #[mkAtom s, mkIdent a,
    mkNullNode $ ← match ty with | none => #[] | some ty => do #[mkAtom ":", ← trExpr ty],
    mkAtom ":=", ← trExpr val, mkNullNode revName]

@[trTactic clear_except] def trClearExcept : TacM Syntax := do
  `(tactic| clear* - $((← parse ident*).map mkIdent)*)

-- FIXME: don't use with_ident_list here in mathlib
@[trTactic extract_goal] def trExtractGoal : TacM Syntax := do
  let hSimp ← parse (tk "!")?
  let n := (← parse (ident)?).map mkIdent
  let vs := (← parse (tk "with" *> ident*)?).map (·.map mkIdent)
  match hSimp with
  | none => `(tactic| extractGoal $[$n:ident]? $[with $vs*]?)
  | some _ => `(tactic| extractGoal! $[$n:ident]? $[with $vs*]?)

@[trTactic inhabit] def trInhabit : TacM Syntax := do
  let t ← trExpr (← parse pExpr)
  `(tactic| inhabit $[$((← parse (ident)?).map mkIdent) :]? $t)

@[trTactic revert_deps] def trRevertDeps : TacM Syntax := do
  `(tactic| revertDeps $((← parse ident*).map mkIdent)*)

@[trTactic revert_after] def trRevertAfter : TacM Syntax := do
  `(tactic| revertAfter $(mkIdent (← parse ident)))

@[trTactic revert_target_deps] def trRevertTargetDeps : TacM Syntax := `(tactic| revertTargetDeps)

@[trTactic clear_value] def trClearValue : TacM Syntax := do
  `(tactic| clearValue $((← parse ident*).map mkIdent)*)

attribute [trTactic generalize'] trGeneralize

attribute [trTactic subst'] trSubst

-- # tactic.solve_by_elim
@[trTactic apply_assumption] def trApplyAssumption : TacM Syntax := do
  throw! "unsupported tactic apply_assumption"
@[trTactic solve_by_elim] def trSolveByElim : TacM Syntax := do
  throw! "unsupported tactic solve_by_elim"

-- # tactic.hint
@[trUserAttr hint_tactic] def trHintAttr : TacM Syntax := do
  parse () *> throw! "unsupported user attr hint_tactic"
@[trUserCmd «add_hint_tactic»] def trAddHintTactic : TacM Syntax := do
  parse () *> throw! "unsupported user command add_hint_tactic"
@[trTactic hint] def trHint : TacM Syntax := do
  throw! "unsupported tactic hint" -- unattested

-- # tactic.alias
@[trUserCmd «alias»] def trAlias (doc : Option String) : TacM Syntax := do
  parse () *> throw! "unsupported user command alias"

-- # tactic.clear
@[trTactic clear'] def trClear' : TacM Syntax := do
  throw! "unsupported tactic clear'" -- unattested
@[trTactic clear_dependent] def trClearDependent : TacM Syntax := do
  throw! "unsupported tactic clear_dependent"

-- # tactic.choose
@[trTactic choose] def trChoose : TacM Syntax := do
  throw! "unsupported tactic choose"

-- # tactic.converter.apply_congr
@[trTactic apply_congr] def trApplyCongr : TacM Syntax := do
  throw! "unsupported tactic apply_congr" -- unattested

-- # tactic.congr
@[trTactic rcongr] def trRCongr : TacM Syntax := do
  throw! "unsupported tactic rcongr"
@[trTactic congr'] def trCongr' : TacM Syntax := do
  throw! "unsupported tactic congr'"
@[trTactic convert] def trConvert : TacM Syntax := do
  throw! "unsupported tactic convert"
@[trTactic convert_to] def trConvertTo : TacM Syntax := do
  throw! "unsupported tactic convert_to"
@[trTactic ac_change] def trAcChange : TacM Syntax := do
  throw! "unsupported tactic ac_change" -- unattested

-- # tactic.dec_trivial
@[trTactic dec_trivial] def trDecTrivial : TacM Syntax := do
  throw! "unsupported tactic dec_trivial"

-- # tactic.delta_instance
@[trTactic delta_instance] def trDeltaInstance : TacM Syntax := do
  throw! "unsupported tactic delta_instance" -- unattested

-- # tactic.elide
@[trTactic elide] def trElide : TacM Syntax := do
  throw! "unsupported tactic elide" -- unattested
@[trTactic unelide] def trUnelide : TacM Syntax := do
  throw! "unsupported tactic unelide" -- unattested

-- # tactic.explode
@[trUserCmd «#explode»] def trExplode : TacM Syntax := do
  parse () *> throw! "unsupported user cmd #explode" -- unattested

-- # tactic.find
@[trUserCmd «#find»] def trFindCmd : TacM Syntax := do
  parse () *> throw! "unsupported user cmd #find" -- unattested

-- # tactic.find_unused
@[trUserAttr main_declaration] def trMainDeclaration : TacM Syntax := do
  parse () *> throw! "unsupported user attr main_declaration" -- unattested
@[trUserCmd «#list_unused_decls»] def trListUnusedDecls : TacM Syntax := do
  parse () *> throw! "unsupported user cmd #list_unused_decls" -- unattested

-- # tactic.finish
@[trTactic clarify] def trClarify : TacM Syntax := do
  throw! "unsupported tactic clarify" -- unattested
@[trTactic safe] def trSafe : TacM Syntax := do
  throw! "unsupported tactic safe"
@[trTactic finish] def trFinish : TacM Syntax := do
  throw! "unsupported tactic finish"

-- # tactic.generalizes
@[trTactic generalizes] def trGeneralizes : TacM Syntax := do
  throw! "unsupported tactic generalizes" -- unattested

-- # tactic.generalize_proofs
@[trTactic generalize_proofs] def trGeneralizeProofs : TacM Syntax := do
  throw! "unsupported tactic generalize_proofs"

-- # tactic.itauto
@[trTactic itauto] def trITauto : TacM Syntax := do
  throw! "unsupported tactic itauto" -- unattested

-- # tactic.lift
@[trTactic lift] def trLift : TacM Syntax := do
  throw! "unsupported tactic lift"

-- # tactic.lift

-- # tactic.localized
@[trUserCmd «open_locale»] def trOpenLocale : TacM Syntax := do
  parse () *> throw! "unsupported user command open_locale"
@[trUserCmd «localized»] def trLocalized : TacM Syntax := do
  parse () *> throw! "unsupported user command localized"

-- # tactic.mk_iff_of_inductive_prop
@[trUserCmd «mk_iff_of_inductive_prop»] def trMkIffOfInductiveProp : TacM Syntax := do
  parse () *> throw! "unsupported user command mk_iff_of_inductive_prop"
@[trUserAttr mk_iff] def trMkIffAttr : TacM Syntax := do
  parse () *> throw! "unsupported user attr mk_iff"

-- # tactic.converter.interactive
@[trTactic old_conv] def trOldConv : TacM Syntax := do
  throw! "unsupported tactic old_conv" -- unattested
@[trTactic find] def trFindTac : TacM Syntax := do
  throw! "unsupported tactic find" -- unattested
@[trTactic conv_rhs] def trConvRhs : TacM Syntax := do
  throw! "unsupported tactic conv_rhs"
@[trTactic conv_lhs] def trConvLhs : TacM Syntax := do
  throw! "unsupported tactic conv_lhs"

-- # tactic.norm_cast
@[trUserAttr norm_cast] def trNormCastAttr : TacM Syntax := do
  parse () *> throw! "unsupported user attr norm_cast"
@[trTactic push_cast] def trPushCast : TacM Syntax := do
  throw! "unsupported tactic push_cast"
@[trTactic norm_cast] def trNormCast : TacM Syntax := do
  throw! "unsupported tactic norm_cast"
@[trTactic rw_mod_cast] def trRwModCast : TacM Syntax := do
  throw! "unsupported tactic rw_mod_cast"
@[trTactic exact_mod_cast] def trExactModCast : TacM Syntax := do
  throw! "unsupported tactic exact_mod_cast"
@[trTactic apply_mod_cast] def trApplyModCast : TacM Syntax := do
  throw! "unsupported tactic apply_mod_cast"
@[trTactic assumption_mod_cast] def trAssumptionModCast : TacM Syntax := do
  throw! "unsupported tactic assumption_mod_cast"

-- # tactic.obviously
@[trUserAttr obviously] def trObviouslyAttr : TacM Syntax := do
  parse () *> throw! "unsupported user attr obviously"

-- # tactic.pretty_cases
@[trTactic pretty_cases] def trPrettyCases : TacM Syntax := do
  throw! "unsupported tactic pretty_cases" -- unattested

-- # tactic.protected
@[trUserAttr «protected»] def trProtectedAttr : TacM Syntax := do
  parse () *> throw! "unsupported user attr protected"
@[trUserAttr protect_proj] def trProtectProjAttr : TacM Syntax := do
  parse () *> throw! "unsupported user attr protect_proj"

-- # tactic.push_neg
@[trTactic push_neg] def trPushNeg : TacM Syntax := do
  throw! "unsupported tactic push_neg"
@[trTactic contrapose] def trContrapose : TacM Syntax := do
  throw! "unsupported tactic contrapose"

-- # tactic.replacer
@[trUserCmd «def_replacer»] def trDefReplacer : TacM Syntax := do
  parse () *> throw! "unsupported user command def_replacer"
@[trUserAttr replaceable] def trReplaceableAttr : TacM Syntax := do
  parse () *> throw! "unsupported tactic replaceable" -- unattested

-- # tactic.rename_var
@[trTactic rename_var] def trRenameVar : TacM Syntax := do
  throw! "unsupported tactic rename_var" -- unattested

-- # tactic.restate_axiom
@[trUserCmd «restate_axiom»] def trRestateAxiom : TacM Syntax := do
  parse () *> throw! "unsupported user command restate_axiom"

-- # tactic.rewrite
@[trTactic assoc_rewrite assoc_rw] def trAssocRw : TacM Syntax := do
  throw! "unsupported tactic assoc_rw"

-- # tactic.show_term
@[trTactic show_term] def trShowTerm : TacM Syntax := do
  throw! "unsupported tactic show_term" -- unattested

-- # tactic.simp_rw
@[trTactic simp_rw] def trSimpRw : TacM Syntax := do
  throw! "unsupported tactic simp_rw"

-- # tactic.simp_command
@[trUserCmd «#simp»] def trSimpCmd : TacM Syntax := do
  parse () *> throw! "unsupported user command #simp" -- unattested

-- # tactic.simp_result
@[trTactic dsimp_result] def trDSimpResult : TacM Syntax := do
  throw! "unsupported tactic dsimp_result" -- unattested
@[trTactic simp_result] def trSimpResult : TacM Syntax := do
  throw! "unsupported tactic simp_result" -- unattested

-- # tactic.simpa
@[trTactic simpa] def trSimpa : TacM Syntax := do
  throw! "unsupported tactic simpa"

-- # tactic.simps
@[trUserAttr notation_class] def trNotationClassAttr : TacM Syntax := do
  parse () *> throw! "unsupported user attr notation_class"
@[trUserCmd «initialize_simps_projections»] def trInitializeSimpsProjections : TacM Syntax := do
  parse () *> throw! "unsupported user command initialize_simps_projections"
@[trUserAttr simps] def trSimpsAttr : TacM Syntax := do
  parse () *> throw! "unsupported user attr simps"

-- # tactic.split_ifs
@[trTactic split_ifs] def trSplitIfs : TacM Syntax := do
  throw! "unsupported tactic split_ifs"

-- # tactic.squeeze
@[trTactic squeeze_scope] def trSqueezeScope : TacM Syntax := do
  throw! "unsupported tactic squeeze_scope" -- unattested
@[trTactic squeeze_simp] def trSqueezeSimp : TacM Syntax := do
  throw! "unsupported tactic squeeze_simp" -- unattested
@[trTactic squeeze_simpa] def trSqueezeSimpa : TacM Syntax := do
  throw! "unsupported tactic squeeze_simpa" -- unattested
@[trTactic squeeze_dsimp] def trSqueezeDSimp : TacM Syntax := do
  throw! "unsupported tactic squeeze_dsimp" -- unattested

-- # tactic.suggest
@[trTactic suggest] def trSuggest : TacM Syntax := do
  throw! "unsupported tactic suggest" -- unattested
@[trTactic library_search] def trLibrarySearch : TacM Syntax := do
  throw! "unsupported tactic library_search" -- unattested

-- # tactic.tauto
@[trTactic tauto tautology] def trTauto : TacM Syntax := do
  throw! "unsupported tactic tauto"

-- # tactic.trunc_cases
@[trTactic trunc_cases] def trTruncCases : TacM Syntax := do
  throw! "unsupported tactic trunc_cases"

-- # tactic.unify_equations
@[trTactic unify_equations] def trUnifyEquations : TacM Syntax := do
  throw! "unsupported tactic unify_equations" -- unattested

-- # tactic.where
@[trUserCmd «#where»] def trWhereCmd : TacM Syntax := do
  parse () *> throw! "unsupported user command #where" -- unattested

-- # tactic.norm_num
@[trUserAttr norm_num] def trNormNumAttr : TacM Syntax := do
  parse () *> throw! "unsupported user attr norm_num"
@[trTactic norm_num1] def trNormNum1 : TacM Syntax := do
  throw! "unsupported tactic norm_num1"
@[trTactic norm_num] def trNormNum : TacM Syntax := do
  throw! "unsupported tactic norm_num"
@[trTactic apply_normed] def trApplyNormed : TacM Syntax := do
  throw! "unsupported tactic apply_normed"

-- # tactic.abel
@[trTactic abel1] def trAbel1 : TacM Syntax := do
  throw! "unsupported tactic abel1" -- unattested
@[trTactic abel] def trAbel : TacM Syntax := do
  throw! "unsupported tactic abel"

-- # tactic.ring
@[trTactic ring1] def trRing1 : TacM Syntax := do
  throw! "unsupported tactic ring1" -- unattested
@[trTactic ring_nf] def trRingNf : TacM Syntax := do
  throw! "unsupported tactic ring_nf"
@[trTactic ring] def trRing : TacM Syntax := do
  throw! "unsupported tactic ring"

-- # tactic.ring_exp
@[trTactic ring_exp_eq] def trRingExpEq : TacM Syntax := do
  throw! "unsupported tactic ring_exp_eq" -- unattested
@[trTactic ring_exp] def trRingExp : TacM Syntax := do
  throw! "unsupported tactic ring_exp"

-- # tactic.noncomm_ring
@[trTactic noncomm_ring] def trNoncommRing : TacM Syntax := do
  throw! "unsupported tactic noncomm_ring"

-- # tactic.linarith
@[trTactic linarith] def trLinarith : TacM Syntax := do
  throw! "unsupported tactic linarith"
@[trTactic nlinarith] def trNLinarith : TacM Syntax := do
  throw! "unsupported tactic nlinarith"

-- # tactic.omega
@[trTactic omega] def trOmega : TacM Syntax := do
  throw! "unsupported tactic omega" -- unattested

-- # tactic.tfae
@[trTactic tfae_have] def trTfaeHave : TacM Syntax := do
  throw! "unsupported tactic tfae_have"
@[trTactic tfae_finish] def trTfaeFinish : TacM Syntax := do
  throw! "unsupported tactic tfae_finish"

-- # tactic.monotonicity
@[trUserAttr mono] def trMonoAttr : TacM Syntax := do
  parse () *> throw! "unsupported user attr mono"
@[trTactic mono] def trMono : TacM Syntax := do
  throw! "unsupported tactic mono"
@[trTactic ac_mono] def trAcMono : TacM Syntax := do
  throw! "unsupported tactic ac_mono" -- unattested

-- # tactic.apply_fun
@[trTactic apply_fun] def trApplyFun : TacM Syntax := do
  throw! "unsupported tactic apply_fun"

-- # tactic.fin_cases
@[trTactic fin_cases] def trFinCases : TacM Syntax := do
  throw! "unsupported tactic fin_cases"

-- # tactic.interval_cases
@[trTactic interval_cases] def trIntervalCases : TacM Syntax := do
  throw! "unsupported tactic interval_cases"

-- # tactic.reassoc_axiom
@[trUserAttr reassoc] def trReassocAttr : TacM Syntax := do
  parse () *> throw! "unsupported user attr reassoc"
@[trTactic reassoc] def trReassoc : TacM Syntax := do
  throw! "unsupported tactic reassoc" -- unattested
@[trUserCmd «reassoc_axiom»] def trReassocAxiom : TacM Syntax := do
  parse () *> throw! "unsupported user cmd reassoc_axiom" -- unattested

-- # tactic.slice
@[trTactic slice_lhs] def trSliceLhs : TacM Syntax := do
  throw! "unsupported tactic slice_lhs"
@[trTactic slice_rhs] def trSliceRhs : TacM Syntax := do
  throw! "unsupported tactic slice_rhs"

-- # tactic.subtype_instance
@[trTactic subtype_instance] def trSubtypeInstance : TacM Syntax := do
  throw! "unsupported tactic subtype_instance" -- unattested

-- # tactic.derive_fintype

-- # tactic.group
@[trTactic group] def trGroup : TacM Syntax := do
  throw! "unsupported tactic group"

-- # tactic.cancel_denoms
@[trTactic cancel_denoms] def trCancelDenoms : TacM Syntax := do
  throw! "unsupported tactic cancel_denoms"

-- # tactic.zify
@[trUserAttr zify] def trZifyAttr : TacM Syntax := do
  parse () *> throw! "unsupported user attr zify"

-- # tactic.transport
@[trTactic transport] def trTransport : TacM Syntax := do
  throw! "unsupported tactic transport" -- unattested

-- # tactic.unfold_cases
@[trTactic unfold_cases] def trUnfoldCases : TacM Syntax := do
  throw! "unsupported tactic unfold_cases" -- unattested

-- # tactic.field_simp
@[trTactic field_simp] def trFieldSimp : TacM Syntax := do
  throw! "unsupported tactic field_simp"

-- # tactic.equiv_rw
@[trTactic equiv_rw] def trEquivRw : TacM Syntax := do
  throw! "unsupported tactic equiv_rw"
@[trTactic equiv_rw_type] def trEquivRwType : TacM Syntax := do
  throw! "unsupported tactic equiv_rw_type" -- unattested

-- # tactic.nth_rewrite
@[trTactic nth_rewrite] def trNthRewrite : TacM Syntax := do
  throw! "unsupported tactic nth_rewrite"
@[trTactic nth_rewrite_lhs] def trNthRewriteLhs : TacM Syntax := do
  throw! "unsupported tactic nth_rewrite_lhs" -- unattested
@[trTactic nth_rewrite_rhs] def trNthRewriteRhs : TacM Syntax := do
  throw! "unsupported tactic nth_rewrite_rhs"

-- # tactic.rewrite_search
@[trUserAttr rewrite] def trRewriteAttr : TacM Syntax := do
  parse () *> throw! "unsupported user attr rewrite" -- unattested
@[trTactic rewrite_search] def trRewriteSearch : TacM Syntax := do
  throw! "unsupported tactic rewrite_search" -- unattested

-- # tactic.pi_instances
@[trTactic pi_instance_derive_field] def trPiInstanceDeriveField : TacM Syntax := do
  throw! "unsupported tactic pi_instance_derive_field" -- unattested
@[trTactic pi_instance] def trPiInstance : TacM Syntax := do
  throw! "unsupported tactic pi_instance"

-- # tactic.tidy
@[trUserAttr tidy] def trTidyAttr : TacM Syntax := do
  parse () *> throw! "unsupported user attr tidy"
@[trTactic tidy] def trTidy : TacM Syntax := do
  throw! "unsupported tactic tidy"

-- # tactic.wlog
@[trTactic wlog] def trWlog : TacM Syntax := do
  throw! "unsupported tactic wlog"

-- # tactic.algebra
@[trUserAttr ancestor] def trAncestorAttr : TacM Syntax := do
  parse () *> throw! "unsupported user attr ancestor"

-- # tactic.elementwise
@[trUserAttr elementwise] def trElementwiseAttr : TacM Syntax := do
  parse () *> throw! "unsupported user attr elementwise"

-- # algebra.group.to_additive
@[trUserAttr to_additive_ignore_args] def trToAdditiveIgnoreArgsAttr : TacM Syntax := do
  parse () *> throw! "unsupported user attr to_additive_ignore_args"
@[trUserAttr to_additive_reorder] def trToAdditiveReorderAttr : TacM Syntax := do
  parse () *> throw! "unsupported user attr to_additive_reorder"
@[trUserAttr to_additive] def trToAdditiveAttr : TacM Syntax := do
  parse () *> throw! "unsupported user attr to_additive"

-- # meta.coinductive_predicates
@[trUserAttr monotonicity] def trMonotonicityAttr : TacM Syntax := do
  parse () *> throw! "unsupported user attr monotonicity"
@[trUserCmd «coinductive_predicate»] def trCoinductivePredicate
  (mods : Modifiers) : TacM Syntax := do
  parse () *> throw! "unsupported user cmd coinductive_predicate" -- unattested

-- # testing.slim_check.sampleable
@[trUserCmd «#sample»] def trSampleCmd : TacM Syntax := do
  parse () *> throw! "unsupported user cmd #sample" -- unattested

-- # logic.nontrivial
@[trTactic nontriviality] def trNontriviality : TacM Syntax := do
  throw! "unsupported tactic nontriviality"

-- # order.filter.basic
@[trTactic filter_upwards] def trFilterUpwards : TacM Syntax := do
  throw! "unsupported tactic filter_upwards"

-- # data.opposite
@[trTactic op_induction] def trOpInduction : TacM Syntax := do
  throw! "unsupported tactic op_induction"

-- # data.qpf.multivariate.constructions.cofix
@[trTactic mv_bisim] def trMvBisim : TacM Syntax := do
  throw! "unsupported tactic mv_bisim"

-- # topology.tactic
@[trUserAttr continuity] def trContinuityAttr : TacM Syntax := do
  parse () *> throw! "unsupported user attr continuity"
@[trTactic continuity] def trContinuity : TacM Syntax := do
  throw! "unsupported tactic continuity"

-- # topology.unit_interval
@[trTactic unit_interval] def trUnitInterval : TacM Syntax := do
  throw! "unsupported tactic unit_interval"

-- # data.equiv.local_equiv
@[trTactic mfld_set_tac] def trMfldSetTac : TacM Syntax := do
  throw! "unsupported tactic mfld_set_tac"

-- # measure_theory.tactic
@[trUserAttr measurability] def trMeasurabilityAttr : TacM Syntax := do
  parse () *> throw! "unsupported user attr measurability"
@[trTactic measurability] def trMeasurability : TacM Syntax := do
  throw! "unsupported tactic measurability"
@[trTactic measurability'] def trMeasurability' : TacM Syntax := do
  throw! "unsupported tactic measurability'"

-- # number_theory.padics.padic_numbers
@[trTactic padic_index_simp] def trPadicIndexSimp : TacM Syntax := do
  throw! "unsupported tactic padic_index_simp"

-- # ring_theory.witt_vector
@[trTactic ghost_fun_tac] def trGhostFunTac : TacM Syntax := do
  throw! "unsupported tactic ghost_fun_tac"
@[trTactic ghost_calc] def trGhostCalc : TacM Syntax := do
  throw! "unsupported tactic ghost_calc"
@[trTactic init_ring] def trInitRing : TacM Syntax := do
  throw! "unsupported tactic init_ring"
@[trTactic ghost_simp] def trGhostSimp : TacM Syntax := do
  throw! "unsupported tactic ghost_simp"
@[trTactic witt_truncate_fun_tac] def trWittTruncateFunTac : TacM Syntax := do
  throw! "unsupported tactic witt_truncate_fun_tac"
@[trUserAttr is_poly] def trIsPolyAttr : TacM Syntax := do
  parse () *> throw! "unsupported user attr is_poly"
