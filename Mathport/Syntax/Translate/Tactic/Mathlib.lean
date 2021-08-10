/-
Copyright (c) 2021 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
import Mathport.Syntax.Translate.Tactic.Basic

open Lean
open Lean.Elab.Tactic (Location)

namespace Mathport.Translate.Tactic
open AST3 Parser

mutual

partial def trRCasesPat : RCasesPat → M Syntax
  | RCasesPat.one `_ => `(rcasesPat| _)
  | RCasesPat.one x => `(rcasesPat| $(mkIdent x):ident)
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
