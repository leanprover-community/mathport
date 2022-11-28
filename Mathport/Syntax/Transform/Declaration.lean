/-
Copyright (c) 2021 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Ebner
-/
import Mathport.Syntax.Transform.Basic

mathport_rules
  | `($mods:declModifiers $attr:attrKind instance $[$prio:namedPrio]? $[$id:declId]? $sig:declSig :=
      { $[$fieldName:ident := $fieldVal:term],* }) =>
    `($mods:declModifiers $attr:attrKind instance $[$prio:namedPrio]? $[$id:declId]? $sig:declSig where
        $[$fieldName:ident := $fieldVal:term]*)
  | `($mods:declModifiers def $id:declId $sig:optDeclSig :=
        { $[$fieldName:ident := $fieldVal:term],* }) =>
    `($mods:declModifiers def $id:declId $sig:optDeclSig where
        $[$fieldName:ident := $fieldVal:term]*)

open Lean Parser.Term Mathport.Transform in
mathport_rules
  | `(letDecl| $id:ident $xs* := fun $ys* => $val:term) => do
    -- well this is surprisingly annoying
    let ofTerm
    | `($v:ident) => pure (v : TSyntax [`ident, ``hole])
    | `(_) => `(hole| _)
    | _ => throwUnsupported
    let ys ← ys.mapM fun
    | `(funBinder| ⦃$vs* : $ty⦄) => `(letIdBinder| ⦃$vs* : $ty⦄)
    | `(funBinder| {$vs*}) => `(letIdBinder| {$vs*})
    | `(funBinder| {$vs* : $ty}) => `(letIdBinder| {$vs* : $ty})
    | `(funBinder| [$[$v :]? $ty]) => `(letIdBinder| [$[$v :]? $ty])
    | `(funBinder| $x:ident) => `(letIdBinder| $x:ident)
    | `(funBinder| ($v1 $vs* : $(ty)?)) => do
      let v1' ← ofTerm v1
      `(letIdBinder| ($v1' $(← vs.mapM ofTerm)* $[: $ty]?))
    | `(funBinder| ($v1 $vs*)) => do
      let v1' ← ofTerm v1
      `(letIdBinder| ($v1' $(← vs.mapM ofTerm)*))
    | `(funBinder| _) => `(letIdBinder| _)
    | _ => throwUnsupported
    `(letDecl| $id:ident $(xs ++ ys)* := $val:term)
