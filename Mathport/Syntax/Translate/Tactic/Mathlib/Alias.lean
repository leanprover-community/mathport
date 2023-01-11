/-
Copyright (c) 2021 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
import Mathport.Syntax.Translate.Tactic.Basic
import Mathport.Syntax.Translate.Command

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
    | Sum.inl ns =>
      ns.forM (do _ ← trDeclId · none)
      `(command| $[$doc]? alias $old ← $(← liftM $ ns.mapM mkIdentI)*)
    | Sum.inr none =>
      warn! "warning: don't know how to generate #align statements for .."
      `(command| $[$doc]? alias $old ↔ ..)
    | Sum.inr (some (l, r)) => do
      if let .ident li := l then _ ← trDeclId li none
      if let .ident ri := r then _ ← trDeclId ri none
      `(command| $[$doc]? alias $old ↔ $(← trBinderIdentI l) $(← trBinderIdentI r))
