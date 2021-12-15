/-
Copyright (c) 2021 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Ebner
-/
import Mathport.Syntax.Transform.Basic
import Mathport.Syntax.Transform.Declaration
import Mathport.Syntax.Transform.Tactic
import Mathlib.Tactic.Lint.Frontend

namespace Mathport
namespace Transform

open Lean Elab Term

local elab "mathportTransformerList%" : term => do
  let decls := transformerAttr.getDecls (← getEnv) |>.map mkCIdent
  Elab.Term.elabTerm (← `((#[$[$decls:term],*] : Array Transformer))) none

partial def transform (stx : Syntax) : M Syntax :=
  let transformers := mathportTransformerList%
  stx.rewriteBottomUpM fun stx => do
    for tr in transformers do
      if let some stx' ← catchUnsupportedSyntax do tr stx then
        return ← transform stx'
    return stx
