/-
Copyright (c) 2021 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Ebner
-/
import Mathport.Syntax.Translate.Basic

namespace Mathport
namespace Transform

open Lean Elab Elab.Command

abbrev M := CommandElabM

abbrev Transformer := Syntax → M Syntax

def throwUnsupported : M α := Elab.throwUnsupportedSyntax

open Elab in
def catchUnsupportedSyntax (k : M α) : M (Option α) :=
  catchInternalId unsupportedSyntaxExceptionId (some <$> k) (fun _ => pure none)

initialize transformerAttr : TagAttribute ←
  registerTagAttribute `mathport_transformer "Lean 4 → 4 syntax transformation for prettification"
    (validate := fun declName => do
      let info ← getConstInfo declName
      unless info.type.isConstOf ``Transformer do
        throwError "declaration must have type {mkConst ``Transformer}")

def matchAlts := Parser.Term.matchAlts
syntax "mathport_rules " matchAlts : command

open Elab.Command in
macro_rules
  | `(mathport_rules $[$alts:matchAlt]*) =>
    `(@[mathport_transformer] aux_def mathportRules : Transformer :=
      fun $[$alts:matchAlt]* | _ => throwUnsupported)

scoped elab "mathport_transformer_list%" : term => do
  let decls := transformerAttr.getDecls (← getEnv) |>.map mkCIdent
  Elab.Term.elabTerm (← `((#[$[$decls:term],*] : Array Transformer))) none

partial def applyTransformers (transformers : Array Transformer) (stx : Syntax) : M Syntax :=
  stx.rewriteBottomUpM fun stx => do
    for tr in transformers do
      if let some stx' ← catchUnsupportedSyntax do withRef stx do tr stx then
        return ← applyTransformers transformers stx'
    return stx

open PrettyPrinter TSyntax.Compat in
macro "#mathport_transform " stx:(term <|> command) : command =>
  `(run_cmd logInfo <|<-
    applyTransformers mathport_transformer_list% (Unhygienic.run `($stx)))
