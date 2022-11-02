/-
Copyright (c) 2021 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Selsam

These functions mimic the ones in lean3/src/library/num.cpp
-/
import Lean
import Mathport.Binary.Basic
import Mathlib.Init.ZeroOne

namespace Mathport.Binary

open Lean

partial def isConcreteNat? (e : Expr) : Option Nat := do
  if e.isConstOf ``Nat.zero then
    some 0
  else if e.isAppOfArity ``Nat.succ 1 then
    let n ← isConcreteNat? e.appArg!
    some (n+1)
  else
    none

structure NumInfo where
  number   : Nat
  level    : Level
  type     : Expr
  hasZero? : Option Expr := none
  hasOne?  : Option Expr := none
  hasAdd?  : Option Expr := none
  deriving Inhabited

partial def isNumber? (e : Expr) : Option NumInfo := do
  if e.isAppOfArity ``Zero.zero 2 then pure {
    number   := 0,
    level    := e.getAppFn.constLevels!.head!,
    type     := e.getArg! 0
    hasZero? := e.getArg! 1
  }
  else if e.isAppOfArity ``One.one 2 then pure {
    number  := 1,
    level   := e.getAppFn.constLevels!.head!,
    type    := e.getArg! 0,
    hasOne? := e.getArg! 1
  }
  else if e.isAppOfArity ``bit0 3 then
    -- TODO: may need to check if these instances are def-eq
    -- (I am hoping that mathlib does not produce terms in which they are not)
    let info ← isNumber? $ e.getArg! 2
    pure { info with
             number  := info.number * 2,
             hasAdd? := info.hasAdd? <|> e.getArg! 1 }
  else if e.isAppOfArity ``bit1 4 then
    let info ← isNumber? $ e.getArg! 3
    pure { info with
             number  := info.number * 2 + 1,
             hasAdd? := info.hasAdd? <|> e.getArg! 2 }
  else none

def translateNumbers (e : Expr) : MetaM Expr := Meta.transform e (pre := core) where
  core e : MetaM TransformStep := pure <|
    match isConcreteNat? e with
    | some n => TransformStep.done $ mkNatLit n
    | none   =>
      match isNumber? e with
      | none => .continue
      | some { number := n, level, type, .. } =>
        -- TODO: we will want to avoid wrapping "normal" Nat numbers
        -- (current workaround is for the OfNat instances to `no_index` the numbers)
        let inst := mkAppN (mkConst ``OfNat.mk [level]) #[type, mkRawNatLit n, e]
        TransformStep.done $ mkAppN (mkConst ``OfNat.ofNat [level]) #[type, mkRawNatLit n, inst]

end Mathport.Binary
