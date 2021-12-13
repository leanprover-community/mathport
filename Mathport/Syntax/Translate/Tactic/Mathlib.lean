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
  `(tactic| ($(← trBlock (← itactic)):tacticSeq))

@[trTactic resetI] def trResetI : TacM Syntax := `(tactic| skip)

@[trTactic substI] def trSubstI : TacM Syntax := do
  `(tactic| subst $(← trExpr (← parse pExpr)))

def trWithIdentList : Array BinderName → Option (Array Syntax)
  | #[] => none
  | ids => some (ids.map trBinderIdent)

@[trTactic casesI] def trCasesI : TacM Syntax := do
  let (hp, e) ← parse casesArg
  `(tactic| cases' $[$(hp.map mkIdent) :]?
    $(← trExpr e) $[with $(trWithIdentList (← parse withIdentList))*]?)

@[trTactic introI] def trIntroI : TacM Syntax := do
  match ← parse ident_ ? with
  | some (BinderName.ident h) => `(tactic| intro $(mkIdent h):ident)
  | _ => `(tactic| intro)

@[trTactic introsI] def trIntrosI : TacM Syntax := do
  match ← parse ident_* with
  | #[] => `(tactic| intros)
  | hs => `(tactic| intros $(hs.map trIdent_)*)

@[trTactic haveI] def trHaveI : TacM Syntax := do
  let h := (← parse (ident)?).map mkIdent
  let ty ← (← parse (tk ":" *> pExpr)?).mapM (trExpr ·)
  match ← parse (tk ":=" *> pExpr)? with
  | some pr => `(tactic| have $[$h:ident]? $[: $ty:term]? := $(← trExpr pr))
  | none => `(tactic| have $[$h:ident]? $[: $ty:term]?)

@[trTactic letI] def trLetI : TacM Syntax := do
  let h ← parse (ident)?
  let ty ← (← parse (tk ":" *> pExpr)?).mapM (trExpr ·)
  match ← parse (tk ":=" *> pExpr)? with
  | some pr =>
    -- FIXME: this is a keyword now
    `(tactic| let $(mkIdent <| h.getD `this') $[: $ty:term]? := $(← trExpr pr))
  | none =>
    `(tactic| let $[$(h.map mkIdent):ident]? $[: $ty:term]?)

@[trTactic exactI] def trExactI : TacM Syntax := do
  `(tactic| exact $(← trExpr (← parse pExpr)))

-- # tactic.lint

@[trUserAttr nolint] def trNolintAttr : TacM Syntax := do
  `(attr| nolint $((← parse ident*).map mkIdent)*)

@[trUserAttr linter] def trLinterAttr := tagAttr `linter

@[trUserCmd «#lint»] def trLintCmd : TacM Syntax := do
  let ((fast, verb), use_only, extra) ← parse lintArgs
  -- TODO: translate (hard because syntax quotation is tricky)
  `(#lint)

@[trUserCmd «#lint_mathlib»] def trLintMathlibCmd : TacM Syntax := do
  let ((fast, verb), use_only, extra) ← parse lintArgs
  -- TODO: translate (hard because syntax quotation is tricky)
  `(#lint mathlib)

@[trUserCmd «#lint_all»] def trLintAllCmd : TacM Syntax := do
  let ((fast, verb), use_only, extra) ← parse lintArgs
  -- TODO: translate (hard because syntax quotation is tricky)
  `(#lint all)

@[trUserCmd «#list_linters»] def trListLintersCmd : TacM Syntax :=
  parse () *> `(command| #list_linters)

-- # tactic.doc_commands

@[trUserCmd «copy_doc_string»] def trCopyDocString : TacM Syntax := do
  let (fr, to_) ← parse $ do (← ident, ← tk "->" *> ident*)
  `(command| copy_doc_string $(← mkIdentI fr) → $(← liftM $ to_.mapM mkIdentI)*)

@[trUserCmd «library_note»] def trLibraryNote (doc : Option String) : TacM Syntax := do
  let Expr.string s ← parse pExpr | warn! "unsupported: weird string"
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
  let pats := match pat with | RCasesPat.alts pats => pats | pat => #[pat]
  mkNode ``Parser.Tactic.rcasesPatMed #[(mkAtom "|").mkSep $ ← pats.mapM trRCasesPat]

partial def trRCasesPatLo (pat : RCasesPat) : M Syntax := do
  let (pat, ty) ← match pat with
  | RCasesPat.typed pat ty => (pat, mkNullNode #[mkAtom ":", ← trExpr ty])
  | _ => (pat, mkNullNode)
  Syntax.node SourceInfo.none ``Parser.Tactic.rcasesPatLo #[← trRCasesPatMed pat, ty]

end

@[trTactic rcases] def trRCases : TacM Syntax := do
  match ← parse rcasesArgs with
  | RCasesArgs.hint es depth => do
    let es := match es with | Sum.inl e => #[e] | Sum.inr es => es
    `(tactic| rcases? $[$(← liftM $ es.mapM trExpr):term],*
      $[: $(depth.map Quote.quote)]?)
  | RCasesArgs.rcases n e pat => do
    `(tactic| rcases $[$(n.map mkIdent):ident :]? $(← trExpr e):term
              with $(← trRCasesPat pat):rcasesPat)
  | RCasesArgs.rcasesMany es pat => liftM $ show M _ from do
    `(tactic| rcases $[$(← es.mapM trExpr):term],* with $(← trRCasesPat pat):rcasesPat)

@[trTactic obtain] def trObtain : TacM Syntax := do
  let ((pat, ty), vals) ← parse obtainArg
  liftM $ show M _ from do
    mkNode ``Parser.Tactic.obtain #[mkAtom "obtain",
      mkOptionalNode (← pat.mapM trRCasesPatMed),
      ← mkOptionalNodeM ty fun ty => do #[mkAtom ":", ← trExpr ty],
      ← mkOptionalNodeM vals fun vals => do
        #[mkAtom ":=", (mkAtom ",").mkSep $ ← vals.mapM trExpr]]

partial def trRIntroPat : RIntroPat → M Syntax
  | RIntroPat.one pat => do `(rintroPat| $(← trRCasesPat pat):rcasesPat)
  | RIntroPat.binder pats ty => do
    `(rintroPat| ($[$(← pats.mapM trRIntroPat):rintroPat]* $[: $(← ty.mapM trExpr)]?))

@[trTactic rintro rintros] def trRIntro : TacM Syntax := do
  liftM $ match ← parse rintroArg with
  | Sum.inr depth => `(tactic| rintro? $[: $(depth.map Quote.quote)]?)
  | Sum.inl (pats, ty) => show M _ from do
    `(tactic| rintro $[$(← pats.mapM trRIntroPat):rintroPat]* $[: $(← ty.mapM trExpr)]?)

-- # tactic.ext

@[trUserAttr ext] def trExtAttr : TacM Syntax := do
  `(attr| ext $(← liftM $ (← parse (ident)?).mapM mkIdentI)?)

@[trTactic ext1] def trExt1 : TacM Syntax := do
  let hint ← parse (tk "?")?
  let pats ← liftM $ (← parse (rcasesPat true)*).mapM trRCasesPat
  match hint with
  | none => `(tactic| ext1 $pats*)
  | some _ => `(tactic| ext1? $pats*)

@[trTactic ext] def trExt : TacM Syntax := do
  let hint ← parse (tk "?")?
  let pats ← liftM $ (← parse (rcasesPat true)*).mapM trRCasesPat
  let depth := (← parse (tk ":" *> smallNat)?).map Quote.quote
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

@[trTactic symmetry'] def trSymmetry' : TacM Syntax := do
  `(tactic| symm' $(← trLoc (← parse location))?)

@[trTactic transitivity'] def trTransitivity' : TacM Syntax := do
  `(tactic| trans' $[$(← liftM $ (← parse (pExpr)?).mapM trExpr)]?)

-- # tactic.core

@[trNITactic tactic.exact_dec_trivial] def trExactDecTrivial (_ : AST3.Expr) : M Syntax :=
  `(tactic| decide)

@[trTactic fsplit] def trFSplit : TacM Syntax := `(tactic| fconstructor)

@[trTactic injections_and_clear] def trInjectionsAndClear : TacM Syntax :=
  `(tactic| injectionsAndClear)

@[trUserCmd «run_parser»] def trRunParser : TacM Syntax := do
  warn! "unsupported: run_parser" -- unattested

@[trNITactic tactic.classical] def trNIClassical (_ : AST3.Expr) : M Syntax :=
  `(tactic| classical)

@[trUserAttr higher_order] def trHigherOrderAttr : TacM Syntax := do
  `(attr| higherOrder $(← liftM $ (← parse (ident)?).mapM mkIdentI)?)

@[trUserAttr interactive] def trInteractiveAttr : TacM Syntax :=
  parse () *> `(attr| interactive)

@[trUserCmd «setup_tactic_parser»] def trSetupTacticParser : TacM Syntax :=
  parse emittedCodeHere *> `(command| setup_tactic_parser)

def trInterpolatedStr' := trInterpolatedStr fun stx => `(← $stx)

@[trUserNota tactic.pformat_macro] def trPFormatMacro : TacM Syntax := do
  `(f! $(← trInterpolatedStr'))

@[trUserNota tactic.fail_macro] def trFailMacro : TacM Syntax := do
  `(throwError $(← trInterpolatedStr'))

@[trUserNota tactic.trace_macro] def trTraceMacro : TacM Syntax := do
  let stx ← trInterpolatedStr'; `(← do dbg_trace $stx)

@[trUserCmd «import_private»] def trImportPrivate : TacM Syntax := do
  let (n, fr) ← parse $ do (← ident, ← (tk "from" *> ident)?)
  `(open private $(← mkIdentF n) $[from $(← liftM $ fr.mapM mkIdentI)]?)

@[trUserCmd «mk_simp_attribute»] def trMkSimpAttribute : TacM Syntax := do
  let (n, d, withList) ← parse $ do (← ident, ← pExpr, ← (tk "with" *> ident*)?)
  let d ← match d.unparen with
  | AST3.Expr.ident `none => pure $ none
  | AST3.Expr.string s => pure $ some (Syntax.mkStrLit s)
  | _ => warn! "unsupported: weird string"
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
    $(Quote.quote (← parse smallNat))
    $(← trBlock (← itactic)):tacticSeq)

@[trTactic swap] def trSwap : TacM Syntax := do
  let e ← (← expr?).mapM fun
  | AST3.Expr.nat n => Quote.quote n
  | _ => warn! "unsupported: weird nat"
  `(tactic| swap $(e)?)

@[trTactic rotate] def trRotate : TacM Syntax := do
  let e ← (← expr?).mapM fun
  | AST3.Expr.nat n => Quote.quote n
  | _ => warn! "unsupported: weird nat"
  `(tactic| rotate $(e)?)

@[trTactic clear_] def trClear_ : TacM Syntax := `(tactic| clear_)

@[trTactic replace] def trReplace : TacM Syntax := do
  let h ← parse (ident)?
  let h := mkOptionalNode' h fun h => #[mkIdent h, mkNullNode]
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
  `(tactic| guardExpr $(← trExpr t):term == $(← trExpr p):term)

@[trTactic guard_target_strict] def trGuardTargetStrict : TacM Syntax := do
  `(tactic| guardTarget == $(← trExpr (← parse pExpr)))

@[trTactic guard_hyp_strict] def trGuardHypStrict : TacM Syntax := do
  `(tactic| guardHyp $(mkIdent (← parse ident)) : $(← trExpr (← parse (tk ":" *> pExpr))))

@[trTactic guard_hyp_nums] def trGuardHypNums : TacM Syntax := do
  match (← expr!).unparen with
  | AST3.Expr.nat n => `(tactic| guardHypNums $(Quote.quote n))
  | _ => warn! "unsupported: weird nat"

@[trTactic guard_tags] def trGuardTags : TacM Syntax := do
  `(tactic| guardTags $((← parse ident*).map mkIdent)*)

@[trTactic guard_proof_term] def trGuardProofTerm : TacM Syntax := do
  `(tactic| guardProofTerm $(← trIdTactic (← itactic)) => $(← trExpr (← parse pExpr)))

@[trTactic success_if_fail_with_msg] def trSuccessIfFailWithMsg : TacM Syntax := do
  let t ← trBlock (← itactic)
  match (← expr!).unparen with
  | AST3.Expr.string s => `(tactic| failIfSuccess? $(Syntax.mkStrLit s) $t:tacticSeq)
  | _ => warn! "unsupported: weird string"

@[trTactic field] def trField : TacM Syntax := do
  `(tactic| field $(mkIdent (← parse ident)) => $(← trBlock (← itactic)):tacticSeq)

@[trTactic have_field] def trHaveField : TacM Syntax := `(tactic| haveField)

@[trTactic apply_field] def trApplyField : TacM Syntax := `(tactic| applyField)

@[trTactic apply_rules] def trApplyRules : TacM Syntax := do
  let hs ← liftM $ (← parse pExprListOrTExpr).mapM trExpr
  let n ← (← expr?).mapM fun
  | AST3.Expr.nat n => Quote.quote n
  | _ => warn! "unsupported: weird nat"
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
  let revName ← parse (tk "with" *> do (← (tk "<-")?, ← ident))?
  let revName := mkOptionalNode' revName fun (flip, id) =>
    #[mkAtom "with", mkOptionalNode' flip fun _ => #[mkAtom "←"], mkIdent id]
  let (tac, s) := if hSimp then (``Parser.Tactic.set!, "set!") else (``Parser.Tactic.set, "set")
  mkNode tac #[mkAtom s, mkIdent a,
    ← mkOptionalNodeM ty fun ty => do #[mkAtom ":", ← trExpr ty],
    mkAtom ":=", ← trExpr val, revName]

@[trTactic clear_except] def trClearExcept : TacM Syntax := do
  `(tactic| clear* - $((← parse ident*).map mkIdent)*)

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
  match ← expr?, ← expr?, ← expr? with
  | none, none, none => `(tactic| applyAssumption)
  | _, _, _ => warn! "unsupported: apply_assumption arguments" -- unattested

@[trTactic solve_by_elim] def trSolveByElim : TacM Syntax := do
  let star := mkOptionalNode $ (← parse (tk "*")?).map fun _ => mkAtom "*"
  let o := if ← parse onlyFlag then mkNullNode #[mkAtom "only"] else mkNullNode
  let hs := trSimpList (← trSimpArgs (← parse simpArgList))
  let attrs := (← parse (tk "with" *> ident*)?).getD #[]
  let cfg ← liftM $ (← expr?).mapM trExpr
  mkNode ``Lean.Meta.solveByElim #[mkAtom "solveByElim",
    star, mkConfigStx cfg, o, hs, trSimpAttrs attrs]

-- # tactic.hint

@[trUserAttr hint_tactic] def trHintAttr : TacM Syntax := tagAttr `hintTactic

@[trUserCmd «add_hint_tactic»] def trAddHintTactic : TacM Syntax := do
  let tac ← match (← parse $ pExpr *> withInput pExpr).1 with
  | Expr.«`[]» tacs => trIdTactic ⟨false, none, none, tacs⟩
  | _ => warn! "unsupported (impossible)"
  `(command| add_hint_tactic $tac)

@[trTactic hint] def trHint : TacM Syntax := `(tactic| hint)

-- # tactic.alias

@[trUserCmd «alias»] def trAlias (doc : Option String) : TacM Syntax := do
  let (old, args) ← parse $ do (← ident, ←
    do { tk "<-"; Sum.inl $ ← ident* } <|>
    do { tk "↔" <|> tk "<->"; Sum.inr $ ←
      (tk "." *> tk "." *> pure none) <|>
      do some (← ident_, ← ident_) })
  let old ← mkIdentI old
  match args with
  | Sum.inl ns => `(command| alias $old ← $(← liftM $ ns.mapM mkIdentI)*)
  | Sum.inr none => `(command| alias $old ↔ ..)
  | Sum.inr (some (l, r)) => do
    `(command| alias $old ↔ $(← trBinderIdentI l) $(← trBinderIdentI r))

-- # tactic.clear

attribute [trTactic clear'] trClear

@[trTactic clear_dependent] def trClearDependent : TacM Syntax := do
  `(tactic| clear! $((← parse ident*).map mkIdent)*)

-- # tactic.choose

@[trTactic choose] def trChoose : TacM Syntax := do
  let nondep ← parse (tk "!")?
  let ns := (#[← parse ident] ++ (← parse ident*)).map mkIdent
  let tgt ← liftM $ (← parse (tk "using" *> pExpr)?).mapM trExpr
  match nondep with
  | none => `(tactic| choose $ns* $[using $tgt]?)
  | some _ => `(tactic| choose! $ns* $[using $tgt]?)

-- # tactic.converter

@[trTactic old_conv] def trOldConv : TacM Syntax := do
  warn! "unsupported tactic old_conv" -- unattested

@[trTactic find] def trFindTac : TacM Syntax := do
  warn! "unsupported tactic find" -- unattested

@[trTactic conv_lhs] def trConvLHS : TacM Syntax := do
  `(tactic| convLHS
    $[at $((← parse (tk "at" *> ident)?).map mkIdent)]?
    $[in $(← liftM $ (← parse (tk "in" *> pExpr)?).mapM trExpr)]?
    => $(← trConvBlock (← itactic)):convSeq)

@[trTactic conv_rhs] def trConvRHS : TacM Syntax := do
  `(tactic| convRHS
    $[at $((← parse (tk "at" *> ident)?).map mkIdent)]?
    $[in $(← liftM $ (← parse (tk "in" *> pExpr)?).mapM trExpr)]?
    => $(← trConvBlock (← itactic)):convSeq)

@[trConv erw] def trERwConv : TacM Syntax := do
  let q ← liftM $ (← parse rwRules).mapM trRwRule
  if let some cfg ← expr? then
    warn! "warning: unsupported: erw with cfg: {repr cfg}"
  `(conv| erw [$q,*])

@[trConv apply_congr] def trApplyCongr : TacM Syntax := do
  `(conv| applyCongr $[$(← liftM $ (← parse (pExpr)?).mapM trExpr)]?)

-- # tactic.congr
@[trTactic congr'] def trCongr' : TacM Syntax := do
  let n := mkOptionalNode $ (← parse (smallNat)?).map Quote.quote
  let args ← parse (tk "with" *> do (← (rcasesPat true)*, ← (tk ":" *> smallNat)?))?
  let args ← mkOptionalNodeM args fun (pats, n) => do
    #[mkAtom "with", mkNullNode $ ← liftM $ pats.mapM trRCasesPat,
      mkOptionalNode' n fun n => #[mkAtom ":", Quote.quote n]]
  mkNode ``Parser.Tactic.congr #[mkAtom "congr", n, args]

@[trTactic rcongr] def trRCongr : TacM Syntax := do
  let pats ← liftM $ (← parse (rcasesPat true)*).mapM trRCasesPat
  `(tactic| rcongr $pats*)

@[trTactic convert] def trConvert : TacM Syntax := do
  let sym := mkOptionalNode' (← parse (tk "<-")?) fun _ => #[mkAtom "←"]
  let r ← trExpr (← parse pExpr)
  let n := mkOptionalNode' (← parse (tk "using" *> smallNat)?) fun n =>
    #[mkAtom "using", Quote.quote n]
  mkNode ``Parser.Tactic.convert #[mkAtom "convert", sym, r, n]

@[trTactic convert_to] def trConvertTo : TacM Syntax := do
  `(tactic| convertTo $(← trExpr (← parse pExpr))
    $[using $((← parse (tk "using" *> smallNat)?).map Quote.quote)]?)

@[trTactic ac_change] def trAcChange : TacM Syntax := do
  `(tactic| acChange $(← trExpr (← parse pExpr))
    $[using $((← parse (tk "using" *> smallNat)?).map Quote.quote)]?)

-- # tactic.dec_trivial
@[trTactic dec_trivial] def trDecTrivial : TacM Syntax := do
  match ← parse (tk "!")? with
  | none => `(tactic| decide)
  | some _ => `(tactic| decide!)

-- # tactic.delta_instance
@[trTactic delta_instance] def trDeltaInstance : TacM Syntax := do
  `(tactic| deltaInstance $((← parse ident*).map mkIdent)*)

-- # tactic.elide
@[trTactic elide] def trElide : TacM Syntax := do
  `(tactic| elide $(Quote.quote (← parse smallNat)) $(← trLoc (← parse location))?)

@[trTactic unelide] def trUnelide : TacM Syntax := do
  `(tactic| unelide $(← trLoc (← parse location))?)

-- # tactic.explode
@[trUserCmd «#explode»] def trExplode : TacM Syntax := do
  `(command| #explode $(← mkIdentI (← parse ident)))

-- # tactic.find
@[trUserCmd «#find»] def trFindCmd : TacM Syntax := do
  `(command| #find $(← trExpr (← parse pExpr)))

-- # tactic.find_unused

@[trUserAttr main_declaration] def trMainDeclaration := tagAttr `mainDeclaration

@[trUserCmd «#list_unused_decls»] def trListUnusedDecls : TacM Syntax :=
  parse () *> `(command| #list_unused_decls)

-- # tactic.finish

def trUsingList (args : Array AST3.Expr) : M Syntax :=
  @mkNullNode <$> match args with
  | #[] => #[]
  | args => do #[mkAtom "using", (mkAtom ",").mkSep $ ← args.mapM trExpr]

@[trTactic clarify] def trClarify : TacM Syntax := do
  let hs := trSimpList (← trSimpArgs (← parse simpArgList))
  let ps ← trUsingList $ (← parse (tk "using" *> pExprListOrTExpr)?).getD #[]
  let cfg ← liftM $ (← expr?).mapM trExpr
  mkNode ``Parser.Tactic.clarify #[mkAtom "clarify", mkConfigStx cfg, hs, ps]

@[trTactic safe] def trSafe : TacM Syntax := do
  let hs := trSimpList (← trSimpArgs (← parse simpArgList))
  let ps ← trUsingList $ (← parse (tk "using" *> pExprListOrTExpr)?).getD #[]
  let cfg ← liftM $ (← expr?).mapM trExpr
  mkNode ``Parser.Tactic.safe #[mkAtom "safe", mkConfigStx cfg, hs, ps]

@[trTactic finish] def trFinish : TacM Syntax := do
  let hs := trSimpList (← trSimpArgs (← parse simpArgList))
  let ps ← trUsingList $ (← parse (tk "using" *> pExprListOrTExpr)?).getD #[]
  let cfg ← liftM $ (← expr?).mapM trExpr
  mkNode ``Parser.Tactic.finish #[mkAtom "finish", mkConfigStx cfg, hs, ps]

-- # tactic.generalizes

@[trTactic generalizes] def trGeneralizes : TacM Syntax := do
  let args ← (← parse (listOf generalizesArg)).mapM fun (h, t, x) => do
    mkNode ``Parser.Tactic.generalizesArg #[
      mkOptionalNode' h fun h => #[mkIdent h, mkAtom ":"],
      ← trExpr t, mkAtom "=", mkIdent x]
  `(tactic| generalizes [$args,*])

-- # tactic.generalize_proofs
@[trTactic generalize_proofs] def trGeneralizeProofs : TacM Syntax := do
  `(tactic| generalizeProofs
    $((← parse (ident_)*).map trBinderIdent)*
    $[$(← trLoc (← parse location))]?)

-- # tactic.itauto
@[trTactic itauto] def trITauto : TacM Syntax := `(tactic| itauto)

-- # tactic.lift
@[trTactic lift] def trLift : TacM Syntax := do
  `(tactic| lift $(← trExpr (← parse pExpr))
    to $(← trExpr (← parse (tk "to" *> pExpr)))
    $[using $(← liftM $ (← parse (tk "using" *> pExpr)?).mapM trExpr)]?
    $[with $(trWithIdentList (← parse withIdentList))*]?)

-- # tactic.lift

-- # tactic.localized

@[trUserCmd «open_locale»] def trOpenLocale : TacM Syntax := do
  `(command| open_locale $(← liftM $ (← parse (ident* <* skipAll)).mapM mkIdentN)*)

@[trUserCmd «localized»] def trLocalized : TacM Unit := do
  let (#[cmd], loc) ← parse $ do (← pExpr *> emittedCodeHere, ← tk "in" *> ident)
    | warn! "unsupported: multiple localized"
  let loc ← mkIdentN loc
  let pushL stx := pushM `(command| localized [$loc] $stx)
  let cmd ← match cmd with
  | Command.attribute true mods attrs ns => trAttributeCmd false attrs ns pushL
  | Command.notation (true, res) attrs n => trNotationCmd (false, res) attrs n pushL
  | _ => warn! "unsupported: unusual localized"

-- # tactic.mk_iff_of_inductive_prop
@[trUserCmd «mk_iff_of_inductive_prop»] def trMkIffOfInductiveProp : TacM Syntax := do
  let (i, r) ← parse $ do (← ident, ← ident)
  `(command| mk_iff_of_inductive_prop $(← mkIdentI i) $(← mkIdentI r))

@[trUserAttr mk_iff] def trMkIffAttr : TacM Syntax := do
  `(attr| mkIff $(← liftM $ (← parse (ident)?).mapM mkIdentI)?)

-- # tactic.norm_cast

@[trUserAttr norm_cast] def trNormCastAttr : TacM Syntax := do
  match ← parse (ident)? with
  | some `elim => `(attr| normCast elim)
  | some `move => `(attr| normCast move)
  | some `squash => `(attr| normCast squash)
  | none => `(attr| normCast)
  | _ => warn! "unsupported (impossible)"

@[trTactic push_cast] def trPushCast : TacM Syntax := do
  let hs := trSimpList (← trSimpArgs (← parse simpArgList))
  mkNode ``Parser.Tactic.pushCast #[mkAtom "pushCast",
    hs, mkOptionalNode $ ← trLoc (← parse location)]

@[trTactic norm_cast] def trNormCast : TacM Syntax := do
  `(tactic| normCast $(← trLoc (← parse location))?)

@[trTactic rw_mod_cast] def trRwModCast : TacM Syntax := do
  `(tactic| rwModCast
    [$(← liftM $ (← parse rwRules).mapM trRwRule),*]
    $(← trLoc (← parse location))?)

@[trTactic exact_mod_cast] def trExactModCast : TacM Syntax := do
  `(tactic| exactModCast $(← trExpr (← parse pExpr)))

@[trTactic apply_mod_cast] def trApplyModCast : TacM Syntax := do
  `(tactic| applyModCast $(← trExpr (← parse pExpr)))

@[trTactic assumption_mod_cast] def trAssumptionModCast : TacM Syntax := do
  `(tactic| assumptionModCast)

@[trConv norm_cast] def trNormCastConv : TacM Syntax := `(conv| normCast)

-- # tactic.replacer

@[trUserCmd «def_replacer»] def trDefReplacer : TacM Syntax := do
  let (n, ty) ← parse $ do (← ident, ← (tk ":" *> pExpr)?)
  `(command| def_replacer $(← mkIdentI n) $[$(← trOptType ty):typeSpec]?)

@[trUserAttr replaceable] def trReplaceableAttr := tagAttr `replaceable

-- # tactic.obviously

@[trUserAttr obviously] def trObviouslyAttr := tagAttr `obviously

@[trNITactic obviously] def trObviously (_ : AST3.Expr) : M Syntax := `(tactic| obviously)

-- # tactic.pretty_cases
@[trTactic pretty_cases] def trPrettyCases : TacM Syntax := do
  `(tactic| prettyCases)

-- # tactic.protected

@[trUserAttr «protected»] def trProtectedAttr := tagAttr `protected

@[trUserAttr protect_proj] def trProtectProjAttr : TacM Syntax := do
  let ids ← match ← parse withoutIdentList with
  | #[] => none
  | ids => some <$> liftM (ids.mapM mkIdentF)
  `(attr| protectProj $[without $ids*]?)

-- # tactic.push_neg

@[trTactic push_neg] def trPushNeg : TacM Syntax := do
  `(tactic| pushNeg $(← trLoc (← parse location))?)

@[trTactic contrapose] def trContrapose : TacM Syntax := do
  let (tac, s) := match ← parse (tk "!")? with
  | none => (``Parser.Tactic.contrapose, "contrapose")
  | some _ => (``Parser.Tactic.contrapose!, "contrapose!")
  let n ← parse (do (← ident, ← (tk "with" *> ident)?))?
  mkNode tac #[mkAtom s, mkOptionalNode' n fun (a, b) =>
    #[mkIdent a, mkOptionalNode' b fun b => #[mkAtom "with", mkIdent b]]]

-- # tactic.rename_var
@[trTactic rename_var] def trRenameVar : TacM Syntax := do
  `(tactic| renameVar $(mkIdent (← parse ident)) → $(mkIdent (← parse ident))
    $(← trLoc (← parse location))?)

-- # tactic.restate_axiom
@[trUserCmd «restate_axiom»] def trRestateAxiom : TacM Syntax := do
  let (a, b) ← parse $ do (← ident, ← (ident)?)
  `(command| restate_axiom $(← mkIdentI a) $(← liftM $ b.mapM mkIdentI)?)

-- # tactic.rewrite
@[trTactic assoc_rewrite assoc_rw] def trAssocRw : TacM Syntax := do
  `(tactic| assocRw
    [$(← liftM $ (← parse rwRules).mapM trRwRule),*]
    $(← trLoc (← parse location))?)

-- # tactic.show_term
@[trTactic show_term] def trShowTerm : TacM Syntax := do
  `(tactic| showTerm $(← trBlock (← itactic)):tacticSeq)

-- # tactic.simp_rw
@[trTactic simp_rw] def trSimpRw : TacM Syntax := do
  `(tactic| simpRw
    [$(← liftM $ (← parse rwRules).mapM trRwRule),*]
    $(← trLoc (← parse location))?)

-- # tactic.simp_command
@[trUserCmd «#simp»] def trSimpCmd : TacM Syntax := do
  let (o, args, attrs, e) ← parse $ do
    (← onlyFlag, ← simpArgList, (← (tk "with" *> ident*)?).getD #[], ← (tk ":")? *> pExpr)
  let hs := trSimpList (← trSimpArgs args)
  let o := if o then mkNullNode #[mkAtom "only"] else mkNullNode
  let colon := if attrs.isEmpty then mkNullNode else mkNullNode #[mkAtom ":"]
  mkNode ``Parser.Command.simp #[mkAtom "#simp", o, hs, trSimpAttrs attrs, colon, ← trExpr e]

-- # tactic.simp_result
@[trTactic dsimp_result] def trDSimpResult : TacM Syntax := do
  let o := if ← parse onlyFlag then mkNullNode #[mkAtom "only"] else mkNullNode
  let hs := trSimpList (← trSimpArgs (← parse simpArgList))
  mkNode ``Parser.Tactic.dsimpResult #[mkAtom "dsimpResult", o, hs,
    trSimpAttrs $ (← parse (tk "with" *> ident*)?).getD #[],
    mkAtom "=>", ← trBlock (← itactic)]

@[trTactic simp_result] def trSimpResult : TacM Syntax := do
  let o := if ← parse onlyFlag then mkNullNode #[mkAtom "only"] else mkNullNode
  let hs := trSimpList (← trSimpArgs (← parse simpArgList))
  mkNode ``Parser.Tactic.simpResult #[mkAtom "simpResult", o, hs,
    trSimpAttrs $ (← parse (tk "with" *> ident*)?).getD #[],
    mkAtom "=>", ← trBlock (← itactic)]

-- # tactic.simpa
@[trTactic simpa] def trSimpa : TacM Syntax := do
  let (tac, s) := match ← parse (tk "!")?, ← parse (tk "?")? with
  | none, none => (``Parser.Tactic.simpa, "simpa")
  | some _, none => (``Parser.Tactic.simpa!, "simpa!")
  | none, some _ => (``Parser.Tactic.simpa?, "simpa?")
  | some _, some _ => (``Parser.Tactic.simpa!?, "simpa!?")
  let o := if ← parse onlyFlag then mkNullNode #[mkAtom "only"] else mkNullNode
  let hs := trSimpList (← trSimpArgs (← parse simpArgList))
  let attrs := (← parse (tk "with" *> ident*)?).getD #[]
  let e ← liftM $ (← parse (tk "using" *> pExpr)?).mapM trExpr
  let cfg := mkConfigStx $ parseSimpConfig (← expr?) |>.bind quoteSimpConfig
  mkNode tac #[mkAtom s, cfg, o, hs, trSimpAttrs attrs,
    mkOptionalNode' e fun e => #[mkAtom "using", e]]

-- # tactic.simps
@[trUserAttr notation_class] def trNotationClassAttr : TacM Syntax := do
  let (star, n) ← parse $ do (← (tk "*")?, ← (ident)?)
  mkNode ``Parser.Attr.notationClass #[mkAtom "notationClass",
    mkOptionalNode' star fun _ => #[mkAtom "*"],
    ← mkOpt n mkIdentF]

def trSimpsRule : Sum (Name × Name) Name × Bool → M Syntax
  | (arg, pfx) => do
    let stx ← match arg with
    | Sum.inl (a, b) => do
      mkNode ``Command.simpsRule.rename #[← mkIdentF a, mkAtom "→", ← mkIdentF b]
    | Sum.inr a => do
      mkNode ``Command.simpsRule.erase #[mkAtom "-", ← mkIdentF a]
    mkNode ``Command.simpsRule #[stx,
      @mkNullNode $ if pfx then #[mkAtom "as_prefix"] else #[]]

@[trUserCmd «initialize_simps_projections»] def trInitializeSimpsProjections : TacM Syntax := do
  let (trc, args) ← parse $ do (← (tk "?")?, ← (do (← ident, ← simpsRules))*)
  let (tac, s) := match trc with
  | none => (``Command.initializeSimpsProjections, "initialize_simps_projections")
  | some _ => (``Command.initializeSimpsProjections?, "initialize_simps_projections?")
  mkNode tac #[mkAtom s, mkNullNode $ ← liftM (m := M) $ args.mapM fun (n, rules) => do
    mkNode ``Command.simpsProj #[← mkIdentF n,
      mkNullNode $ ← match rules with
      | #[] => #[]
      | _ => do #[mkAtom "(", (mkAtom ",").mkSep $ ← rules.mapM trSimpsRule, mkAtom ")"]]]

@[trUserAttr simps] def trSimpsAttr : TacM Syntax := do
  let (trc, ns, cfg) ← parse $ do (← (tk "?")?, ← ident*, ← (pExpr)?)
  let ns ← liftM $ ns.mapM mkIdentF
  let cfg ← liftM $ cfg.mapM trExpr
  match trc with
  | none => `(attr| simps $[(config := $cfg)]? $ns*)
  | some _ => `(attr| simps? $[(config := $cfg)]? $ns*)

-- # tactic.split_ifs
@[trTactic split_ifs] def trSplitIfs : TacM Syntax := do
  `(tactic| splitIfs $(← trLoc (← parse location))?
    $[with $(trWithIdentList (← parse withIdentList))*]?)

-- # tactic.squeeze

@[trTactic squeeze_scope] def trSqueezeScope : TacM Syntax := do
  `(tactic| squeezeScope $(← trBlock (← itactic)):tacticSeq)

@[trTactic squeeze_simp] def trSqueezeSimp : TacM Syntax := do
  let (tac, s) := match ← parse () *> parse (tk "?")?, ← parse (tk "!")? with
  | none, none => (``Parser.Tactic.squeezeSimp, "squeezeSimp")
  | none, some _ => (``Parser.Tactic.squeezeSimp?, "squeezeSimp?")
  | some _, none => (``Parser.Tactic.squeezeSimp!, "squeezeSimp!")
  | some _, some _ => (``Parser.Tactic.squeezeSimp?!, "squeezeSimp?!")
  let o := if ← parse onlyFlag then mkNullNode #[mkAtom "only"] else mkNullNode
  let hs := trSimpList (← trSimpArgs (← parse simpArgList))
  let attrs := (← parse (tk "with" *> ident*)?).getD #[]
  let loc := mkOptionalNode $ ← trLoc (← parse location)
  let cfg := mkConfigStx $ parseSimpConfig (← parse (structInst)?) |>.bind quoteSimpConfig
  mkNode tac #[mkAtom s, cfg, o, hs, trSimpAttrs attrs, loc]

@[trTactic squeeze_simpa] def trSqueezeSimpa : TacM Syntax := do
  let (tac, s) := match ← parse () *> parse (tk "?")?, ← parse (tk "!")? with
  | none, none => (``Parser.Tactic.squeezeSimpa, "squeezeSimpa")
  | none, some _ => (``Parser.Tactic.squeezeSimpa?, "squeezeSimpa?")
  | some _, none => (``Parser.Tactic.squeezeSimpa!, "squeezeSimpa!")
  | some _, some _ => (``Parser.Tactic.squeezeSimpa?!, "squeezeSimpa?!")
  let o := if ← parse onlyFlag then mkNullNode #[mkAtom "only"] else mkNullNode
  let hs := trSimpList (← trSimpArgs (← parse simpArgList))
  let attrs := (← parse (tk "with" *> ident*)?).getD #[]
  let e ← liftM $ (← parse (tk "using" *> pExpr)?).mapM trExpr
  let cfg := mkConfigStx $ parseSimpConfig (← parse (structInst)?) |>.bind quoteSimpConfig
  mkNode tac #[mkAtom s, cfg, o, hs, trSimpAttrs attrs,
    mkOptionalNode' e fun e => #[mkAtom "using", e]]

@[trTactic squeeze_dsimp] def trSqueezeDSimp : TacM Syntax := do
  let (tac, s) := match ← parse () *> parse (tk "?")?, ← parse (tk "!")? with
  | none, none => (``Parser.Tactic.squeezeDSimp, "squeezeDSimp")
  | none, some _ => (``Parser.Tactic.squeezeDSimp?, "squeezeDSimp?")
  | some _, none => (``Parser.Tactic.squeezeDSimp!, "squeezeDSimp!")
  | some _, some _ => (``Parser.Tactic.squeezeDSimp?!, "squeezeDSimp?!")
  let o := if ← parse onlyFlag then mkNullNode #[mkAtom "only"] else mkNullNode
  let hs := trSimpList (← trSimpArgs (← parse simpArgList))
  let attrs := (← parse (tk "with" *> ident*)?).getD #[]
  let loc := mkOptionalNode $ ← trLoc (← parse location)
  let cfg := mkConfigStx $ parseSimpConfig (← parse (structInst)?) |>.bind quoteSimpConfig
  mkNode tac #[mkAtom s, cfg, o, hs, trSimpAttrs attrs, loc]

-- # tactic.suggest
def trSuggestUsing (args : Array BinderName) : M Syntax := do
  let args ← args.mapM fun
  | BinderName.ident n => mkIdent n
  | BinderName._ => warn! "unsupported: using _ in suggest/library_search"
  mkNullNode $ ← match args with
  | #[] => #[]
  | _ => do #[mkAtom "using", mkNullNode args]

@[trTactic suggest] def trSuggest : TacM Syntax := do
  let n := (← parse (smallNat)?).map Quote.quote
  let hs := trSimpList (← trSimpArgs (← parse simpArgList))
  let attrs := (← parse (tk "with" *> ident*)?).getD #[]
  let use ← trSuggestUsing ((← parse (tk "using" *> ident_*)?).getD #[])
  let cfg := mkConfigStx $ ← liftM $ (← expr?).mapM trExpr
  mkNode ``Parser.Tactic.suggest #[mkAtom "suggest", cfg, hs, trSimpAttrs attrs, use]

@[trTactic library_search] def trLibrarySearch : TacM Syntax := do
  let (tac, s) := match ← parse (tk "!")? with
  | none => (``Tactic.LibrarySearch.librarySearch', "librarySearch")
  | some _ => (``Parser.Tactic.librarySearch!, "librarySearch!")
  let hs := trSimpList (← trSimpArgs (← parse simpArgList))
  let attrs := (← parse (tk "with" *> ident*)?).getD #[]
  let use ← trSuggestUsing ((← parse (tk "using" *> ident_*)?).getD #[])
  let cfg := mkConfigStx $ ← liftM $ (← expr?).mapM trExpr
  mkNode tac #[mkAtom s, cfg, hs, trSimpAttrs attrs, use]

-- # tactic.tauto
@[trTactic tauto tautology] def trTauto : TacM Syntax := do
  let c ← parse (tk "!")?
  let cfg ← liftM $ (← expr?).mapM trExpr
  match c with
  | none => `(tactic| tauto $[(config := $cfg)]?)
  | some _ => `(tactic| tauto! $[(config := $cfg)]?)

-- # tactic.trunc_cases
@[trTactic trunc_cases] def trTruncCases : TacM Syntax := do
  `(tactic| truncCases $(← trExpr (← parse pExpr))
    $[with $(trWithIdentList (← parse withIdentList))*]?)

-- # tactic.unify_equations
@[trTactic unify_equations] def trUnifyEquations : TacM Syntax := do
  warn! "unsupported tactic unify_equations" -- unattested

-- # tactic.where
@[trUserCmd «#where»] def trWhereCmd : TacM Syntax := parse skipAll *> `(command| #where)

-- # tactic.norm_num
@[trUserAttr norm_num] def trNormNumAttr := tagAttr `normNum

@[trTactic norm_num1] def trNormNum1 : TacM Syntax := do
  `(tactic| normNum1 $(← trLoc (← parse location))?)

@[trTactic norm_num] def trNormNum : TacM Syntax := do
  let hs := trSimpList (← trSimpArgs (← parse simpArgList))
  let loc := mkOptionalNode $ ← trLoc (← parse location)
  mkNode ``Tactic.normNum #[mkAtom "normNum", hs, loc]

@[trTactic apply_normed] def trApplyNormed : TacM Syntax := do
  `(tactic| applyNormed $(← trExpr (← parse pExpr)))

@[trConv norm_num1] def trNormNum1Conv : TacM Syntax := `(conv| normNum1)

@[trConv norm_num] def trNormNumConv : TacM Syntax := do
  let hs := trSimpList (← trSimpArgs (← parse simpArgList))
  mkNode ``Parser.Tactic.Conv.normNum #[mkAtom "normNum", hs]

-- # tactic.abel
@[trTactic abel1] def trAbel1 : TacM Syntax := `(tactic| abel1)

@[trTactic abel] def trAbel : TacM Syntax := do
  match ← parse (tk "!")?, ← parse (ident)?, ← trLoc (← parse location) with
  | none, none, loc => `(tactic| abel $(loc)?)
  | none, some `raw, loc => `(tactic| abel raw $(loc)?)
  | none, some `term, loc => `(tactic| abel term $(loc)?)
  | some _, none, loc => `(tactic| abel! $(loc)?)
  | some _, some `raw, loc => `(tactic| abel! raw $(loc)?)
  | some _, some `term, loc => `(tactic| abel! term $(loc)?)
  | _, _, _ => warn! "bad abel mode"

-- # tactic.ring
@[trTactic ring1] def trRing1 : TacM Syntax := do
  match ← parse (tk "!")? with
  | none => `(tactic| ring1)
  | some _ => `(tactic| ring1!)

def trRingMode (n : Name) : M Syntax :=
  if [`SOP, `raw, `horner].contains n then
    mkNode ``Parser.Tactic.ringMode #[mkIdent n]
  else warn! "bad ring mode"

@[trTactic ring_nf] def trRingNF : TacM Syntax := do
  let c ← parse (tk "!")?
  let mode ← liftM $ (← parse (ident)?).mapM trRingMode
  let loc ← trLoc (← parse location)
  match c with
  | none => `(tactic| ringNF $(mode)? $(loc)?)
  | some _ => `(tactic| ringNF! $(mode)? $(loc)?)

@[trTactic ring] def trRing : TacM Syntax := do
  match ← parse (tk "!")? with
  | none => `(tactic| ring)
  | some _ => `(tactic| ring!)

@[trConv ring_nf] def trRingNFConv : TacM Syntax := do
  let c ← parse (tk "!")?
  let mode ← liftM $ (← parse (ident)?).mapM trRingMode
  match c with
  | none => `(tactic| ringNF $(mode)?)
  | some _ => `(tactic| ringNF! $(mode)?)

@[trConv ring] def trRingConv : TacM Syntax := do
  match ← parse (tk "!")? with
  | none => `(tactic| ring)
  | some _ => `(tactic| ring!)

-- # tactic.ring_exp
@[trTactic ring_exp_eq] def trRingExpEq : TacM Syntax := do
  match ← parse (tk "!")? with
  | none => `(tactic| ringExpEq)
  | some _ => `(tactic| ringExpEq!)

@[trTactic ring_exp] def trRingExp : TacM Syntax := do
  let c ← parse (tk "!")?
  let loc ← trLoc (← parse location)
  match c with
  | none => `(tactic| ringExp $(loc)?)
  | some _ => `(tactic| ringExp! $(loc)?)

@[trConv ring_exp] def trRingExpConv : TacM Syntax := do
  match ← parse (tk "!")? with
  | none => `(tactic| ringExp)
  | some _ => `(tactic| ringExp!)

-- # tactic.noncomm_ring
@[trTactic noncomm_ring] def trNoncommRing : TacM Syntax := `(tactic| noncommRing)

-- # tactic.linarith
@[trTactic linarith] def trLinarith : TacM Syntax := do
  let (tac, s) := match ← parse (tk "!")? with
  | none => (``Parser.Tactic.linarith, "linarith")
  | some _ => (``Parser.Tactic.linarith!, "linarith!")
  let o := if ← parse onlyFlag then mkNullNode #[mkAtom "only"] else mkNullNode
  let args := mkNullNode $ ← match ← parse optPExprList with
  | #[] => #[]
  | args => do #[mkAtom "[", (mkAtom ",").mkSep $ ← liftM $ args.mapM trExpr, mkAtom "]"]
  let cfg := mkConfigStx $ ← liftM $ (← expr?).mapM trExpr
  mkNode tac #[mkAtom s, cfg, o, args]

@[trTactic nlinarith] def trNLinarith : TacM Syntax := do
  let (tac, s) := match ← parse (tk "!")? with
  | none => (``Parser.Tactic.nlinarith, "nlinarith")
  | some _ => (``Parser.Tactic.nlinarith!, "nlinarith!")
  let o := if ← parse onlyFlag then mkNullNode #[mkAtom "only"] else mkNullNode
  let args := mkNullNode $ ← match ← parse optPExprList with
  | #[] => #[]
  | args => do #[mkAtom "[", (mkAtom ",").mkSep $ ← liftM $ args.mapM trExpr, mkAtom "]"]
  let cfg := mkConfigStx $ ← liftM $ (← expr?).mapM trExpr
  mkNode tac #[mkAtom s, cfg, o, args]

-- # tactic.omega
@[trTactic omega] def trOmega : TacM Syntax := do
  let args ← parse ident*
  mkNode ``Parser.Tactic.omega #[mkAtom "omega",
    mkNullNode $ if args.contains `manual then #[mkAtom "manual"] else #[],
    mkNullNode $
      if args.contains `int then #[mkAtom "int"] else
      if args.contains `nat then #[mkAtom "nat"] else #[]]

-- # tactic.tfae
@[trTactic tfae_have] def trTfaeHave : TacM Syntax := do
  mkNode ``Parser.Tactic.tfaeHave #[mkAtom "tfaeHave",
    mkOptionalNode' (← parse ((ident)? <* tk ":")) fun h => #[mkIdent h, mkAtom ":"],
    Quote.quote (← parse smallNat),
    mkAtom (← parse ((tk "->" *> pure "→") <|> (tk "↔" *> pure "↔") <|> (tk "<-" *> pure "←"))),
    Quote.quote (← parse smallNat)]

@[trTactic tfae_finish] def trTfaeFinish : TacM Syntax := `(tactic| tfaeFinish)

-- # tactic.monotonicity

@[trUserAttr mono] def trMonoAttr : TacM Syntax := do
  match ← parse (ident)? with
  | some `left => `(attr| mono left)
  | some `right => `(attr| mono right)
  | some `both => `(attr| mono)
  | none => `(attr| mono)
  | _ => warn! "unsupported (impossible)"

@[trTactic mono] def trMono : TacM Syntax := do
  let star := mkOptionalNode' (← parse (tk "*")?) fun _ => #[mkAtom "*"]
  let side ← match ← parse (ident)? with
  | some `left => some (mkAtom "left")
  | some `right => some (mkAtom "right")
  | some `both => none
  | none => none
  | _ => warn! "unsupported (impossible)"
  let w ← match ← parse ((tk "with" *> pExprListOrTExpr) <|> pure #[]) with
  | #[] => none
  | w => liftM $ some <$> w.mapM trExpr
  let hs ← trSimpArgs (← parse ((tk "using" *> simpArgList) <|> pure #[]))
  mkNode ``Parser.Tactic.mono #[mkAtom "mono", star,
    mkOptionalNode' side fun side => #[mkNode ``Parser.Tactic.mono.side #[side]],
    mkOptionalNode' w fun w => #[mkAtom "with", (mkAtom ",").mkSep w],
    mkNullNode $ if hs.isEmpty then #[] else #[mkAtom "using", (mkAtom ",").mkSep hs]]

@[trTactic ac_mono] def trAcMono : TacM Syntax := do
  let arity ← parse $
    (tk "*" *> pure #[mkAtom "*"]) <|>
    (tk "^" *> do #[mkAtom "^", Quote.quote (← smallNat)]) <|> pure #[]
  let arg ← parse ((tk ":=" *> do (":=", ← pExpr)) <|> (tk ":" *> do (":", ← pExpr)))?
  let arg ← mkOptionalNodeM arg fun (s, e) => do #[mkAtom s, ← trExpr e]
  let cfg := mkConfigStx $ ← liftM $ (← expr?).mapM trExpr
  mkNode ``Parser.Tactic.acMono #[mkAtom "acMono", mkNullNode arity, cfg, arg]

-- # tactic.apply_fun
@[trTactic apply_fun] def trApplyFun : TacM Syntax := do
  `(tactic| applyFun
    $(← trExpr (← parse pExpr))
    $[$(← trLoc (← parse location))]?
    $[using $(← liftM $ (← parse (tk "using" *> pExpr)?).mapM trExpr)]?)

-- # tactic.fin_cases
@[trTactic fin_cases] def trFinCases : TacM Syntax := do
  let hyp ← parse $ (tk "*" *> none) <|> (some <$> ident)
  let w ← liftM $ (← parse (tk "with" *> pExpr)?).mapM trExpr
  match hyp with
  | none => `(tactic| finCases * $[with $w]?)
  | some h => `(tactic| finCases $(mkIdent h):ident $[with $w]?)

-- # tactic.interval_cases
@[trTactic interval_cases] def trIntervalCases : TacM Syntax := do
  mkNode ``Parser.Tactic.intervalCases #[mkAtom "intervalCases",
    ← mkOpt (← parse (pExpr)?) trExpr,
    ← mkOptionalNodeM (← parse (tk "using" *> do (← ident, ← ident))?) fun (x, y) => do
      #[mkAtom "using", mkIdent x, mkAtom ",", mkIdent y],
    mkOptionalNode' (← parse (tk "with" *> ident)?) fun h => #[mkAtom "with", mkIdent h]]

-- # tactic.reassoc_axiom

@[trUserAttr reassoc] def trReassocAttr : TacM Syntax := do
  `(attr| reassoc $(← liftM $ (← parse (ident)?).mapM mkIdentI)?)

@[trUserCmd «reassoc_axiom»] def trReassocAxiom : TacM Syntax := do
  `(command| reassoc_axiom $(← mkIdentI (← parse ident)))

@[trTactic reassoc] def trReassoc : TacM Syntax := do
  match ← parse (tk "!")?, (← parse ident*).map mkIdent with
  | none, ns => `(tactic| reassoc $ns*)
  | some _, ns => `(tactic| reassoc! $ns*)

@[trNITactic tactic.derive_reassoc_proof] def trDeriveReassocProof
  (_ : AST3.Expr) : M Syntax := `(deriveReassocProof)

-- # tactic.slice

@[trConv slice] def trSliceConv : TacM Syntax := do
  let AST3.Expr.nat a ← expr! | warn! "slice: weird nat"
  let AST3.Expr.nat b ← expr! | warn! "slice: weird nat"
  `(conv| slice $(Quote.quote a) $(Quote.quote b))

@[trTactic slice_lhs] def trSliceLHS : TacM Syntax := do
  `(tactic| sliceLHS $(Quote.quote (← parse smallNat)) $(Quote.quote (← parse smallNat))
    => $(← trConvBlock (← itactic)):convSeq)

@[trTactic slice_rhs] def trSliceRHS : TacM Syntax := do
  `(tactic| sliceRHS $(Quote.quote (← parse smallNat)) $(Quote.quote (← parse smallNat))
    => $(← trConvBlock (← itactic)):convSeq)

-- # tactic.subtype_instance
@[trTactic subtype_instance] def trSubtypeInstance : TacM Syntax := `(tactic| subtypeInstance)

-- # tactic.derive_fintype

-- # tactic.group
@[trTactic group] def trGroup : TacM Syntax := do
  `(tactic| group $(← trLoc (← parse location))?)

-- # tactic.cancel_denoms
@[trTactic cancel_denoms] def trCancelDenoms : TacM Syntax := do
  `(tactic| cancelDenoms $(← trLoc (← parse location))?)

-- # tactic.zify
@[trUserAttr zify] def trZifyAttr := tagAttr `zify

@[trTactic zify] def trZify : TacM Syntax := do
  let hs := trSimpList (← trSimpArgs (← parse simpArgList))
  let loc := mkOptionalNode $ ← trLoc (← parse location)
  mkNode ``Parser.Tactic.zify #[mkAtom "zify", hs, loc]

-- # tactic.transport
@[trTactic transport] def trTransport : TacM Syntax := do
  `(tactic| transport
    $[$(← liftM $ (← parse (pExpr)?).mapM trExpr)]?
    using $(← trExpr (← parse (tk "using" *> pExpr))))

-- # tactic.unfold_cases
@[trTactic unfold_cases] def trUnfoldCases : TacM Syntax := do
  `(tactic| unfoldCases $(← trBlock (← itactic)):tacticSeq)

-- # tactic.field_simp
@[trTactic field_simp] def trFieldSimp : TacM Syntax := do
  let o := if ← parse onlyFlag then mkNullNode #[mkAtom "only"] else mkNullNode
  let hs := trSimpList (← trSimpArgs (← parse simpArgList))
  let attrs := (← parse (tk "with" *> ident*)?).getD #[]
  let loc := mkOptionalNode $ ← trLoc (← parse location)
  let cfg := mkConfigStx $ parseSimpConfig (← expr?) |>.bind quoteSimpConfig
  mkNode ``Parser.Tactic.fieldSimp #[mkAtom "fieldSimp", cfg, o, hs, trSimpAttrs attrs, loc]

-- # tactic.equiv_rw

@[trTactic equiv_rw] def trEquivRw : TacM Syntax := do
  let e ← trExpr (← parse pExpr)
  let loc ← trLoc (← parse location)
  let cfg ← liftM $ (← expr?).mapM trExpr
  `(tactic| equivRw $[(config := $cfg)]? $e $[$loc]?)

@[trTactic equiv_rw_type] def trEquivRwType : TacM Syntax := do
  let e ← trExpr (← parse pExpr)
  let cfg ← liftM $ (← expr?).mapM trExpr
  `(tactic| equivRwType $[(config := $cfg)]? $e)

-- # tactic.nth_rewrite

@[trTactic nth_rewrite] def trNthRewrite : TacM Syntax := do
  `(tactic| nthRw $(Quote.quote (← parse smallNat))
    [$(← liftM $ (← parse rwRules).mapM trRwRule),*]
    $(← trLoc (← parse location))?)

@[trTactic nth_rewrite_lhs] def trNthRewriteLHS : TacM Syntax := do
  `(tactic| nthRwLHS $(Quote.quote (← parse smallNat))
    [$(← liftM $ (← parse rwRules).mapM trRwRule),*]
    $(← trLoc (← parse location))?)

@[trTactic nth_rewrite_rhs] def trNthRewriteRHS : TacM Syntax := do
  `(tactic| nthRwRHS $(Quote.quote (← parse smallNat))
    [$(← liftM $ (← parse rwRules).mapM trRwRule),*]
    $(← trLoc (← parse location))?)

-- # tactic.rewrite_search

@[trUserAttr rewrite] def trRewriteAttr := tagAttr `rewrite

@[trTactic rewrite_search] def trRewriteSearch : TacM Syntax := do
  let explain ← parse (tk "?")?
  let rw ← liftM $ (← parse rwRules).mapM trRwRule
  let cfg ← liftM $ (← expr?).mapM trExpr
  match explain with
  | none => `(tactic| rwSearch $[(config := $cfg)]? [$rw,*])
  | some _ => `(tactic| rwSearch? $[(config := $cfg)]? [$rw,*])

-- # tactic.pi_instances

@[trNITactic tactic.pi_instance_derive_field] def trPiInstanceDeriveField
  (_ : AST3.Expr) : M Syntax := `(piInstanceDeriveField)

@[trTactic pi_instance] def trPiInstance : TacM Syntax := `(piInstance)

-- # tactic.tidy

@[trUserAttr tidy] def trTidyAttr := tagAttr `tidy

@[trTactic tidy] def trTidy : TacM Syntax := do
  let explain ← parse (tk "?")?
  let cfg ← liftM $ (← expr?).mapM trExpr
  match explain with
  | none => `(tactic| tidy $[(config := $cfg)]?)
  | some _ => `(tactic| tidy? $[(config := $cfg)]?)

-- # tactic.wlog
@[trTactic wlog] def trWlog : TacM Syntax := do
  let h := (← parse (ident)?).map mkIdent
  let pat ← liftM $ (← parse (tk ":" *> pExpr)?).mapM trExpr
  let cases ← liftM $ (← parse (tk ":=" *> pExpr)?).mapM trExpr
  let perms ← parse (tk "using" *> (listOf ident* <|> do #[← ident*]))?
  let perms := match perms.getD #[] with
  | #[] => none
  | perms => some (perms.map (·.map mkIdent))
  let disch ← liftM $ (← expr?).mapM trExpr
  `(tactic| wlog $[(discharger := $disch)]? $(h)? $[: $pat]? $[:= $cases]? $[using $[$perms*],*]?)

-- # tactic.algebra
@[trUserAttr ancestor] def trAncestorAttr : TacM Syntax := do
  `(attr| ancestor $(← liftM $ (← parse ident*).mapM mkIdentI)*)

-- # tactic.elementwise

@[trUserAttr elementwise] def trElementwiseAttr : TacM Syntax := do
  `(attr| elementwise $(← liftM $ (← parse (ident)?).mapM mkIdentI)?)

@[trTactic elementwise] def trElementwise : TacM Syntax := do
  match ← parse (tk "!")?, (← parse ident*).map mkIdent with
  | none, ns => `(tactic| elementwise $ns*)
  | some _, ns => `(tactic| elementwise! $ns*)

@[trNITactic tactic.derive_elementwise_proof] def trDeriveElementwiseProof
  (_ : AST3.Expr) : M Syntax := `(deriveElementwiseProof)

-- # algebra.group.defs
attribute [trNITactic try_refl_tac] trControlLawsTac

-- # algebra.group.to_additive
@[trUserAttr to_additive_ignore_args] def trToAdditiveIgnoreArgsAttr : TacM Syntax := do
  `(attr| toAdditiveIgnoreArgs $((← parse smallNat*).map Quote.quote)*)

@[trUserAttr to_additive_reorder] def trToAdditiveReorderAttr : TacM Syntax := do
  `(attr| toAdditiveReorder $((← parse smallNat*).map Quote.quote)*)

@[trUserAttr to_additive] def trToAdditiveAttr : TacM Syntax := do
  let (bang, ques, tgt, doc) ← parse $ do (← (tk "!")?, ← (tk "?")?, ← (ident)?, ← (pExpr)?)
  let tgt ← liftM $ tgt.mapM mkIdentI
  let doc ← doc.mapM fun doc => match doc.unparen with
  | Expr.string s => Syntax.mkStrLit s
  | _ => warn! "to_additive: weird doc string"
  match bang, ques with
  | none, none => `(attr| toAdditive $(tgt)? $(doc)?)
  | some _, none => `(attr| toAdditive! $(tgt)? $(doc)?)
  | none, some _ => `(attr| toAdditive? $(tgt)? $(doc)?)
  | some _, some _ => `(attr| toAdditive!? $(tgt)? $(doc)?)

-- # meta.coinductive_predicates
@[trUserAttr monotonicity] def trMonotonicityAttr := tagAttr `monotonicity

@[trUserCmd «coinductive»] def trCoinductivePredicate (mods : Modifiers) : TacM Syntax := do
  parse () *> warn! "unsupported user cmd coinductive" -- unattested

-- # testing.slim_check.sampleable
@[trUserCmd «#sample»] def trSampleCmd : TacM Syntax := do
  `(command| #sample $(← trExpr (← parse pExpr)))

@[trNITactic sampleable.mk_trivial_interp] def trMkTrivialInterp
  (_ : AST3.Expr) : M Syntax := `(refine id)

-- # testing.slim_check.testable
@[trNITactic testable.mk_decorations] def trMkDecorations
  (_ : AST3.Expr) : M Syntax := `(mkDecorations)

-- # logic.nontrivial
@[trTactic nontriviality] def trNontriviality : TacM Syntax := do
  let t ← liftM $ (← parse (pExpr)?).mapM trExpr
  let lems ← trSimpArgs (← parse (tk "using" *> simpArgList <|> pure #[]))
  let lems := if lems.isEmpty then none else some lems
  `(tactic| nontriviality $[$t]? $[using $lems,*]?)

-- # order.filter.basic
@[trTactic filter_upwards] def trFilterUpwards : TacM Syntax := do
  `(tactic| filterUpwards
    [$(← liftM $ (← parse pExprList).mapM trExpr),*]
    $[$(← liftM $ (← parse (pExpr)?).mapM trExpr)]?)

-- # order.liminf_limsup
@[trNITactic isBounded_default] def trIsBounded_default (_ : AST3.Expr) : M Syntax := do
  `(tactic| isBounded_default)

-- # data.opposite
@[trTactic op_induction] def trOpInduction : TacM Syntax := do
  `(tactic| opInduction $[$((← parse (ident)?).map mkIdent):ident]?)

-- # data.qpf.multivariate.constructions.cofix
@[trTactic mv_bisim] def trMvBisim : TacM Syntax := do
  `(tactic| mvBisim
    $[$(← liftM $ (← parse (pExpr)?).mapM trExpr)]?
    $[with $(trWithIdentList (← parse withIdentList))*]?)

-- # topology.tactic

@[trUserAttr continuity] def trContinuityAttr := tagAttr `continuity

@[trTactic continuity] def trContinuity : TacM Syntax := do
  let bang ← parse (tk "!")?
  let ques ← parse (tk "?")?
  let cfg ← liftM $ (← expr?).mapM trExpr
  match bang, ques with
  | none, none => `(tactic| continuity $[(config := $cfg)]?)
  | some _, none => `(tactic| continuity! $[(config := $cfg)]?)
  | none, some _ => `(tactic| continuity? $[(config := $cfg)]?)
  | some _, some _ => `(tactic| continuity!? $[(config := $cfg)]?)

@[trTactic continuity'] def trContinuity' : TacM Syntax := `(tactic| continuity)
@[trNITactic tactic.interactive.continuity'] def trNIContinuity'
  (_ : AST3.Expr) : M Syntax := `(tactic| continuity)

-- # topology.unit_interval
@[trTactic unit_interval] def trUnitInterval : TacM Syntax := `(tactic| unitInterval)

-- # data.equiv.local_equiv
@[trTactic mfld_set_tac] def trMfldSetTac : TacM Syntax := `(tactic| mfldSetTac)

-- # measure_theory.measure.measure_space_def
@[trNITactic volume_tac] def trVolumeTac (_ : AST3.Expr) : M Syntax := do
  `(tactic| exact $(← mkIdentI `measure_theory.measure_space.volume))

-- # measure_theory.tactic

@[trUserAttr measurability] def trMeasurabilityAttr := tagAttr `measurability

@[trTactic measurability] def trMeasurability : TacM Syntax := do
  let bang ← parse (tk "!")?
  let ques ← parse (tk "?")?
  let cfg ← liftM $ (← expr?).mapM trExpr
  match bang, ques with
  | none, none => `(tactic| measurability $[(config := $cfg)]?)
  | some _, none => `(tactic| measurability! $[(config := $cfg)]?)
  | none, some _ => `(tactic| measurability? $[(config := $cfg)]?)
  | some _, some _ => `(tactic| measurability!? $[(config := $cfg)]?)

@[trTactic measurability'] def trMeasurability' : TacM Syntax := `(tactic| measurability)

-- # measure_theory.integral.interval_integral
@[trNITactic unique_diff_within_at_Ici_Iic_univ] def trUniqueDiffWithinAt_Ici_Iic_univ (_ : AST3.Expr) : M Syntax := do
  `(tactic| uniqueDiffWithinAt_Ici_Iic_univ)

-- # number_theory.padics.padic_numbers
@[trTactic padic_index_simp] def trPadicIndexSimp : TacM Syntax := do
  `(tactic| padicIndexSimp
    [$(← liftM $ (← parse pExprList).mapM trExpr),*]
    $(← trLoc (← parse location))?)

-- # ring_theory.witt_vector
@[trTactic ghost_fun_tac] def trGhostFunTac : TacM Syntax := do
  `(tactic| ghostFunTac $(← trExpr (← parse pExpr)), $(← trExpr (← parse pExpr)))

@[trTactic ghost_calc] def trGhostCalc : TacM Syntax := do
  `(tactic| ghostCalc $((← parse ident_*).map trBinderIdent)*)

@[trTactic init_ring] def trInitRing : TacM Syntax := do
  `(tactic| initRing $[using $(← liftM $ (← parse (tk "using" *> pExpr)?).mapM trExpr)]?)

@[trTactic ghost_simp] def trGhostSimp : TacM Syntax := do
  mkNode ``Parser.Tactic.ghostSimp #[mkAtom "ghostSimp",
    trSimpList (← trSimpArgs (← parse simpArgList))]

@[trTactic witt_truncate_fun_tac] def trWittTruncateFunTac : TacM Syntax :=
  `(tactic| wittTruncateFunTac)

@[trUserAttr is_poly] def trIsPolyAttr : TacM Syntax := tagAttr `isPoly
