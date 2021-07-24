/-
Copyright (c) 2021 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Selsam

These functions mimic the ones in lean3/src/library/num.cpp
-/
import Lean
import Mathport.Binary.Basic

namespace Mathport.Binary

open Lean

partial def isConcreteNat? (e : Expr) : Option Nat := OptionM.run $
  if e.isConstOf `Nat.zero then
    some 0
  else if e.isAppOfArity `Nat.succ 1 then do
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

partial def isNumber? (e : Expr) : Option NumInfo := do
  if e.isAppOfArity `HasZero.zero 2 then some {
    number   := 0,
    level    := e.getAppFn.constLevels!.head!,
    type     := e.getArg! 0
    hasZero? := e.getArg! 1
  }
  else if e.isAppOfArity `HasOne.one 2 then some {
    number  := 1,
    level   := e.getAppFn.constLevels!.head!,
    type    := e.getArg! 0,
    hasOne? := e.getArg! 1
  }
  -- TODO: may need to check if these instances are def-eq
  -- (I am hoping that mathlib does not produce terms in which they are not)
  else if e.isAppOfArity `bit0 3 then OptionM.run $ do
    let info ← isNumber? $ e.getArg! 2
    some { info with
             number  := info.number * 2,
             hasAdd? := info.hasAdd? <|> e.getArg! 1 }
  else if e.isAppOfArity `bit1 4 then OptionM.run $ do
    let info ← isNumber? $ e.getArg! 2
    some { info with
             number  := info.number * 2 + 1,
             hasAdd? := info.hasAdd? <|> e.getArg! 2 }
  else none

end Mathport.Binary
