/-
Copyright (c) 2021 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
import Mathport.Syntax.Translate.Tactic.Basic

open Lean

namespace Mathport.Translate.Tactic
open AST3 Parser

-- # tactic.alias

@[tr_user_cmd «alias»] def trAlias (doc : Option String) : Parse1 Syntax.Command :=
  parse1 (return (← ident <* withInput skipAll, ←
    (tk "<-" *> Sum.inl <$> ident*) <|>
    ((tk "↔" <|> tk "<->") *> Sum.inr <$>
      ((tk ".." *> pure none) <|> return some (← ident_, ← ident_)))))
  fun (old, args) => do
    let doc := doc.map trDocComment
    let old ← mkIdentI old
    match args with
    | Sum.inl ns => `(command| $[$doc]? alias $old ← $(← liftM $ ns.mapM mkIdentI)*)
    | Sum.inr none => `(command| $[$doc]? alias $old ↔ ..)
    | Sum.inr (some (l, r)) => do
      `(command| $[$doc]? alias $old ↔ $(← trBinderIdentI l) $(← trBinderIdentI r))

