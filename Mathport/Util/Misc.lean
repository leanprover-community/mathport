/-
Copyright (c) 2021 Microsoft Corporation. All rights reserved.
nReleased under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Daniel Selsam
-/
import Lean
import Std.Data.HashMap
import Std.Data.RBMap

def uncurry (f : α → β → γ) : α × β → γ
  | (x, y) => f x y

namespace Lean

open Std (HashMap)

deriving instance Hashable for Position

def dummyFileMap : FileMap := ⟨"", #[0], #[1]⟩

def Expr.replaceConstNames (e : Expr) (f : Name → Option Name) : Expr :=
  e.replace fun
    | const n us ..   => f n |>.map fun n' => mkConst n' us
    | proj n idx t .. => f n |>.map fun n' => mkProj n' idx t
    | _ => none

def InductiveType.updateNames (indType : InductiveType) (newIndName : Name) : InductiveType := do
  let map : HashMap Name Name := ({} : HashMap Name Name).insert indType.name newIndName
  { indType with
    name  := newIndName,
    ctors := indType.ctors.map fun ctor => { ctor with
      name := ctor.name.replacePrefix indType.name newIndName
      type := ctor.type.replaceConstNames fun n => map.find? n }
  }

def Declaration.collectNames : Declaration → List Name
  | Declaration.defnDecl defn          => [defn.name]
  | Declaration.thmDecl thm            => [thm.name]
  | Declaration.axiomDecl ax           => [ax.name]
  | Declaration.inductDecl _ _ [ind] _ => ind.name :: (ind.name ++ `rec) :: ind.ctors.map Constructor.name
  | _ => panic! "unexpected declaration type"

def Declaration.toName : Declaration → Name
  | Declaration.defnDecl defn          => defn.name
  | Declaration.thmDecl thm            => thm.name
  | Declaration.axiomDecl ax           => ax.name
  | Declaration.inductDecl _ _ [ind] _ => ind.name
  | _ => panic! "unexpected declaration type"

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
  Elab.Term.elabTerm (← `(throwError ($head ++ $str : String))) ty

open Lean Elab Term Quotation in
@[termElab cmdQuot] def elabCmdQuot : TermElab := adaptExpander stxQuot.expand

def List.splitAt {α} (xs : List α) (i : Nat) : List α × List α :=
  (xs.take i, xs.drop i)

def Array.splitAt {α} (xs : Array α) (i : Nat) : Array α × Array α :=
  ((xs.toList.take i).toArray, (xs.toList.drop i).toArray)

-- TODO: faster version
def Std.HashMap.insertWith [Hashable α] [BEq α] (m : HashMap α β) (merge : β → β → β) (a : α) (b : β) : HashMap α β :=
  match m.find? a with
  | none => m.insert a b
  | some c => m.insert a (merge c b)

namespace Lean.Elab.Command

def CommandElabM.toIO (x : CommandElabM α) (ctx : Context) (s : State) : IO α := do
  match ← x ctx |>.run' s |>.toIO' with
  | Except.error (Exception.error _ msg)   => do throw $ IO.userError (← msg.toString)
  | Except.error (Exception.internal id _) => throw $ IO.userError $ "internal exception #" ++ toString id.idx
  | Except.ok a => pure a

def CommandElabM.toIO' (x : CommandElabM α) (ctx : Context) (env : Environment) : IO α := do
  toIO x ctx (mkState env)

end Lean.Elab.Command
