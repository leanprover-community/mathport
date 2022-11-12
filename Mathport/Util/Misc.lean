/-
Copyright (c) 2021 Microsoft Corporation. All rights reserved.
nReleased under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Daniel Selsam
-/
import Lean

def uncurry (f : α → β → γ) : α × β → γ
  | (x, y) => f x y

namespace Lean

elab "lean_dir%" : term =>
  return toExpr (← getLibDir (← findSysroot)).toString

def Expr.isAppOfArityGE (e : Expr) (n : Name) (k : Nat) : Bool :=
  e.withApp fun f args => f.isConstOf n && args.size ≥ k

open Lean (HashMap)

deriving instance Repr for ConstantVal
deriving instance Repr for AxiomVal
deriving instance Repr for ReducibilityHints
deriving instance Repr for DefinitionVal
deriving instance Repr for TheoremVal
deriving instance Repr for OpaqueVal
deriving instance Repr for Constructor
deriving instance Repr for InductiveType
deriving instance Repr for Declaration

deriving instance Hashable for Position

def dummyFileMap : FileMap := ⟨"", #[0], #[1]⟩

def Expr.replaceConstNames (e : Expr) (f : Name → Option Name) : Expr :=
  e.replace fun
    | const n us ..   => f n |>.map fun n' => mkConst n' us
    | proj n idx t .. => f n |>.map fun n' => mkProj n' idx t
    | _ => none

def InductiveType.selfPlaceholder : Name := `_indSelf

def InductiveType.replaceSelfWithPlaceholder (indType : InductiveType) : InductiveType := { indType with
  ctors := indType.ctors.map fun ctor => { ctor with
    name := ctor.name.replacePrefix indType.name selfPlaceholder
    type := renameSelf ctor.type }
  }
where
  renameSelf (ctorType : Expr) := ctorType.replaceConstNames fun n => if n == indType.name then selfPlaceholder else none

def InductiveType.replacePlaceholder (indType : InductiveType) (newName : Name) : InductiveType := { indType with
  name := newName,
  ctors := indType.ctors.map fun ctor => { ctor with
    name := ctor.name.replacePrefix selfPlaceholder newName,
    type := renameSelf ctor.type }
  }
where
  renameSelf (ctorType : Expr) := ctorType.replaceConstNames fun n => if n == selfPlaceholder then newName else none

def InductiveType.updateNames (indType : InductiveType) (oldIndName newIndName : Name) : InductiveType := Id.run do
  let map : HashMap Name Name := ({} : HashMap Name Name).insert oldIndName newIndName
  { indType with
    name  := newIndName,
    ctors := indType.ctors.map fun ctor => { ctor with
      name := ctor.name.replacePrefix oldIndName newIndName
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

export System (FilePath)

instance : MonadLift (Except String) IO where
  monadLift
    | .error err => throw $ IO.userError err
    | .ok x => pure x

@[inline] def Std.Format.parenPrec (p prec : Nat) (f : Format) :=
  if prec >= p then paren f else f

instance : Coe (Array α) (Subarray α) := ⟨(·[0:])⟩

-- TODO: This broke when bumping Lean 4 to nightly-2021-12-15.
-- However it is not actually used in `mathport`, so I've just commented it out for now.
-- /-- Run action with `stdin` emptied and `stdout+stderr` captured into a `String`. -/
-- def IO.FS.withIsolatedStreams' [Monad m] [MonadFinally m] [MonadLiftT IO m] (x : m α) : m (String × α) := do
--   let bIn ← mkRef { : Stream.Buffer }
--   let bOut ← mkRef { : Stream.Buffer }
--   let r ← withStdin (Stream.ofBuffer bIn) <|
--     withStdout (Stream.ofBuffer bOut) <|
--       withStderr (Stream.ofBuffer bOut) <|
--         x
--   let bOut ← liftM (m := IO) bOut.get
--   let out := String.fromUTF8Unchecked bOut.data
--   pure (out, r)

def Lean.Syntax.mkCharLit (val : Char) (info := SourceInfo.none) : Syntax :=
  mkLit charLitKind (Char.quote val) info

open Lean in
instance : MonadQuotation Id where
  getRef              := pure Syntax.missing
  withRef             := fun _ => id
  getCurrMacroScope   := pure 0
  getMainModule       := pure `_fakeMod
  withFreshMacroScope := id

open Lean Elab in
elab:max "throw!" interpStr:interpolatedStr(term) : term <= ty => do
  let pos ← getRefPosition
  let head := Syntax.mkStrLit $ mkErrorStringWithPos (← getFileName) pos ""
  let str ← Elab.liftMacroM <| interpStr.expandInterpolatedStr (← `(String)) (← `(toString))
  Elab.Term.elabTerm (← `(throwError ($head ++ $str : String))) ty

def Array.splitAt {α} (xs : Array α) (i : Nat) : Array α × Array α :=
  let right := xs.extract i xs.size
  (xs.shrink i, right)

def Array.asNonempty : Array α → Option (Array α)
  | #[] => none
  | hs => some hs

-- TODO: faster version
def Lean.HashMap.insertWith [Hashable α] [BEq α] (m : HashMap α β) (merge : β → β → β) (a : α) (b : β) : HashMap α β :=
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

section -- for debugging

open Lean Lean.Elab Lean.Elab.Term Lean.Elab.Tactic
open Lean Lean.Elab Lean.Elab.Command Lean.Parser
open Lean.Parser Lean.PrettyPrinter

syntax (name := termStx) "#term "   term    : command
syntax (name := tacStx)  "#tactic " tactic  : command
syntax (name := cmdStx)  "#cmd "    command : command
syntax (name := attrStx)  "#attr "   attr : command

deriving instance Repr for Syntax

@[command_elab termStx] def elabTermStx : CommandElab
  | `(#term $stx:term) => println! "{ stx}"
  | _ => throwUnsupportedSyntax

@[command_elab cmdStx] def elabCmdStx : CommandElab
  | `(#cmd $stx:command) => do
    -- let stx ← liftTermElabM `none do formatCommand stx
    println! "{stx}\n"
    let stx ← liftCoreM <| parenthesizeCommand stx
    println! "{stx}\n"
  | _ => throwUnsupportedSyntax

@[command_elab attrStx] def elabAttrStx : CommandElab
  | `(#attr $stx:attr) => println! "{ stx}"
  | _ => throwUnsupportedSyntax

end
