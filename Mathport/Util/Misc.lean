/-
Copyright (c) 2021 Microsoft Corporation. All rights reserved.
nReleased under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Daniel Selsam
-/
import Lean
import Std.Data.HashMap
import Std.Data.RBMap

namespace Lean

deriving instance Hashable for Position

def dummyFileMap : FileMap := ⟨"", #[0], #[1]⟩

end Lean

export Std (HashSet HashMap RBMap RBNode)
export System (FilePath)

instance : MonadLift (Except String) IO where
  monadLift
  | _, Except.error err => throw $ IO.userError err
  | _, Except.ok x => pure x

@[macroInline] def assert {m : Type → Type v} [Pure m] [MonadExcept ε m]
  (p : Prop) [Decidable p] (e : ε) : m Unit :=
  if p then pure () else throw e

def Subarray.getOp {α : Type u} [Inhabited α] (self : Subarray α) (idx : Nat) : α :=
  let i := idx + self.start
  if i < self.stop then self.as[i] else arbitrary

@[inline] def Std.Format.parenPrec (p prec : Nat) (f : Format) :=
  if prec >= p then paren f else f

instance : Coe (Array α) (Subarray α) := ⟨(·[0:])⟩

def Option.mapM {α : Type u} {β : Type v} {m : Type v → Type w} [Monad m] (f : α → m β) :
    Option α → m (Option β)
  | none => pure none
  | some a => some <$> f a

def Lean.Syntax.mkCharLit (val : Char) (info := SourceInfo.none) : Syntax :=
  mkLit charLitKind (Char.quote val) info

syntax (name := cmdQuot) "`(command|" incQuotDepth(command) ")" : term

open Lean Elab in
elab:max "throw!" interpStr:interpolatedStr(term) : term <= ty => do
  let pos ← Elab.getRefPosition
  let head := Syntax.mkStrLit $ mkErrorStringWithPos (← read).fileName pos ""
  let str ← Elab.liftMacroM <| interpStr.expandInterpolatedStr (← `(String)) (← `(toString))
  Elab.Term.elabTerm (← `(throw ($head ++ $str))) ty

open Lean Elab Term Quotation in
@[termElab cmdQuot] def elabCmdQuot : TermElab := adaptExpander stxQuot.expand

def String.cmp (x y : String) : Ordering :=
  if x < y then Ordering.lt
  else if x > y then Ordering.gt
  else Ordering.eq

def List.splitAt {α} (xs : List α) (i : Nat) : List α × List α :=
  (xs.take i, xs.drop i)

def Array.splitAt {α} (xs : Array α) (i : Nat) : Array α × Array α :=
  ((xs.toList.take i).toArray, (xs.toList.drop i).toArray)

-- TODO: faster version
def Std.HashMap.insertWith [Hashable α] [BEq α] (m : HashMap α β) (merge : β → β → β) (a : α) (b : β) : HashMap α β :=
  match m.find? a with
  | none => m.insert a b
  | some c => m.insert a (merge c b)
