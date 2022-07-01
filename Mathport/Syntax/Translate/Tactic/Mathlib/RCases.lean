/-
Copyright (c) 2021 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
import Mathport.Syntax.Translate.Tactic.Basic

open Lean
open Lean.Elab.Tactic (Location)

namespace Mathport.Translate.Tactic
open AST3 Mathport.Translate.Parser

-- # tactic.rcases

mutual

partial def trRCasesPat : RCasesPat → M (TSyntax `rcasesPat)
  | RCasesPat.one BinderName._ => `(rcasesPat| _)
  | RCasesPat.one (BinderName.ident x) => `(rcasesPat| $(mkIdent x):ident)
  | RCasesPat.clear => do `(rcasesPat| -)
  | RCasesPat.tuple pats => do `(rcasesPat| ⟨$(← pats.mapM trRCasesPatLo),*⟩)
  | RCasesPat.alts #[pat] => trRCasesPat pat
  | pat => do `(rcasesPat| ($(← trRCasesPatLo pat)))

partial def trRCasesPatMed (pat : RCasesPat) : M (TSyntax ``Parser.Tactic.rcasesPatMed) := do
  let pats := match pat with | RCasesPat.alts pats => pats | pat => #[pat]
  `(Parser.Tactic.rcasesPatMed| $[$(← pats.mapM trRCasesPat)]|*)

partial def trRCasesPatLo (pat : RCasesPat) : M (TSyntax ``Parser.Tactic.rcasesPatLo) := do
  let (pat, ty) ← match pat with
    | RCasesPat.typed pat ty => pure (pat, some (← trExpr ty))
    | _ => pure (pat, none)
  `(Parser.Tactic.rcasesPatLo| $(← trRCasesPatMed pat):rcasesPatMed $[: $ty:term]?)

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
  -- liftM $ show M _ from
  let vals ← vals.mapM fun vals => vals.mapM (liftM do trExpr ·)
  liftM do `(tactic|
    obtain $[$(← pat.mapM trRCasesPatMed):rcasesPatMed]?
      $[: $(← ty.mapM trExpr)]? $[:= $[$vals],*]?)

partial def trRIntroPat : RIntroPat → M (TSyntax `rintroPat)
  | RIntroPat.one pat => do `(rintroPat| $(← trRCasesPat pat):rcasesPat)
  | RIntroPat.binder pats ty => do
    `(rintroPat| ($[$(← pats.mapM trRIntroPat):rintroPat]* $[: $(← ty.mapM trExpr)]?))

@[trTactic rintro rintros] def trRIntro : TacM Syntax := do
  match ← parse rintroArg with
  | Sum.inr depth => `(tactic| rintro? $[: $(depth.map Quote.quote)]?)
  | Sum.inl (pats, ty) => show M _ from do
    `(tactic| rintro $[$(← pats.mapM trRIntroPat):rintroPat]* $[: $(← ty.mapM trExpr)]?)
