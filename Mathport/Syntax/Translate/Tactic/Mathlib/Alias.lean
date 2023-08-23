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

@[tr_user_cmd «alias»] def trAlias (doc : Option String) : Parse1 Unit :=
  parse1 (return (← ident <* withInput skipAll, ←
    (tk "<-" *> Sum.inl <$> ident*) <|>
    ((tk "↔" <|> tk "<->") *> Sum.inr <$>
      ((tk ".." *> pure none) <|> return some (← ident_, ← ident_)))))
  fun (name, args) => do
    let doc := doc.map trDocComment
    let old ← mkIdentI name
    match args with
    | Sum.inl ns =>
      for n in ns do
        _ ← trDeclId n none .regular false
        push (← `(command| $[$doc]? alias $(← mkIdentI n) := $old))
    | Sum.inr args =>
      let (l, r) ← args.getDM do
        let .str parent base := name
          | warn! "alias only works for string names" | pure (.«_», .«_»)
        let components := base.splitOn "_iff_"
        let forward := String.intercalate "_of_" components.reverse
        let backward := String.intercalate "_of_" components
        let forwardName := Name.mkStr parent forward
        let backwardName := Name.mkStr parent backward
        pure (.ident forwardName, .ident backwardName)
      if let .ident li := l then _ ← trDeclId li none .regular false
      if let .ident ri := r then _ ← trDeclId ri none .regular false
      push <|← `(command| $[$doc]? alias ⟨$(← trBinderIdentI l), $(← trBinderIdentI r)⟩ := $old)
