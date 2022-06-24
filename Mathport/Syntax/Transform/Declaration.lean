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
        $[$fieldName:ident := $fieldVal:term];*)
  | `($mods:declModifiers def $id:declId $sig:optDeclSig :=
        { $[$fieldName:ident := $fieldVal:term],* }) =>
    `($mods:declModifiers def $id:declId $sig:optDeclSig where
        $[$fieldName:ident := $fieldVal:term];*)

-- TODO: this seems to break with mathport-generated lambdas
-- open Lean.Parser.Command in
-- mathport_rules
--   | `(whereStructField| $id:ident := fun $xs:ident* => $val:term) =>
--     `(whereStructField| $id:ident $xs:ident* := $val:term)
