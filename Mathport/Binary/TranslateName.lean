/-
Copyright (c) 2021 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Selsam

Lean3 uses snake_case for everything.

As of now, Lean4 uses:
- camelCase for defs
- PascalCase for types
- snake_case for proofs
-/
import Lean
import Mathport.Util.String

inductive ExprKind
  | eType
  | eProp
  | eDef
  | eProof

open Lean

def Lean.Name.toLean4 (n3 : Name) (eKind : ExprKind) : Name :=
  let prefix4 := translatePrefix n3.getPrefix
  match n3 with
  | Name.num _ k ..  => Name.mkNum prefix4 k
  | Name.str _ s ..  => Name.mkStr prefix4 (translateSuffix s)
  | _                => Name.anonymous
where
  translatePrefix : Name → Name
    | Name.num pfix k .. => Name.mkNum (translatePrefix pfix) k
    | Name.str pfix s .. => Name.mkStr (translatePrefix pfix) s.snake2pascal
    | Name.anonymous ..  => Name.anonymous

  translateSuffix (s : String) : String :=
    match eKind with
    | ExprKind.eType  => s.snake2pascal
    | ExprKind.eProp  => s.snake2pascal
    | ExprKind.eDef   => s.snake2camel
    | ExprKind.eProof => s
