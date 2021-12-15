/-
Copyright (c) 2021 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Ebner
-/
import Mathport.Syntax.Translate.Basic

namespace Mathport
namespace Transform

open Lean

abbrev M := Translate.M

abbrev Transformer := Syntax → M Syntax

def throwUnsupported : M α := Elab.throwUnsupportedSyntax

initialize transformerAttr : TagAttribute ←
  registerTagAttribute `mathportTransformer "Lean 4 → 4 syntax transformation for prettification"
    (validate := fun declName => do
      let info ← getConstInfo declName
      unless info.type.isConstOf ``Transformer do
        throwError "declaration must have type {mkConst ``Transformer}")

def matchAlts := Parser.Term.matchAlts
syntax "mathport_rules " matchAlts : command

open Elab in
def catchUnsupportedSyntax (k : M α) : M (Option α) :=
  catchInternalId unsupportedSyntaxExceptionId (some <$> k) (fun _ => none)

open Elab.Command in
macro_rules
  | `(mathport_rules $[$alts:matchAlt]*) =>
    `(@[mathportTransformer] aux_def mathportRules : Transformer :=
      fun $[$alts:matchAlt]* | _ => throwUnsupported)
