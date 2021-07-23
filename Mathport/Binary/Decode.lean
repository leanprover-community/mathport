/-
Copyright (c) 2021 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Selsam
-/
import Lean

namespace Mathport.Binary

open Lean

-- Awkward: this section refers to names that are created during the port

def decodeChar (e : Expr) : MetaM Char := do
  if e.isAppOfArity `Char.mk 2 then
    match (e.getArg! 0).natLit? with
    | some n => Char.ofNat n
    | _ => throwError "[decodeChar] failed on {e}"
  else
    throwError "[decodeChar] failed on {e}"

partial def decodeStringCore (e : Expr) : MetaM String := do
  if e.isAppOfArity `List.nil 1 then
    ""
  else if e.isAppOfArity `List.cons 3 then
    let s ← decodeStringCore (e.getArg! 2)
    let c ← decodeChar (e.getArg! 1)
    pure ⟨c :: s.data⟩
  else
    throwError "[decodeStringCore] failed on {e}"

def decodeUnsigned (e : Expr) : MetaM Nat :=
  if e.isAppOfArity `Fin.mk 2 then
    match (e.getArg! 0).natLit? with
    | some n => n
    | _ => throwError "[decodeUInt32] failed on {e}"
  else
    throwError "[decodeUInt32] failed on {e}"

def decodeString (e : Expr) : MetaM String := do
  if e.isAppOfArity `StringImp.mk 1 then
    decodeStringCore (e.getArg! 0)
  else throwError "[decodeString] failed on {e}"

partial def decodeName (e : Expr) : MetaM Name := do
  if e.isAppOfArity `Name'.anonymous 0 then
    Name.anonymous
  else if e.isAppOfArity `Name'.mk_string 2 then
    Name.mkStr (← decodeName (e.getArg! 1)) (← decodeString (e.getArg! 0))
  else if e.isAppOfArity `Name'.mk_numeral 2 then
    Name.mkNum (← decodeName (e.getArg! 1)) (← decodeUnsigned (e.getArg! 0))
  else
    throwError "[decodeName] failed on {e}"

end Mathport.Binary
