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
import Mathport.Util.Misc
import Mathport.Util.String
import Mathport.Binary.Basic
import Mathport.Binary.Number
import Mathport.Binary.Decode
import Mathport.Binary.TranslateName
import Mathport.Binary.Heterogenize

namespace Mathport.Binary

open Lean Lean.Meta Mathlib.Prelude.Rename

/--
  Return true iff `declName` is one of the auxiliary definitions/projections
  used to implement coercions (also in Lean 3)
-/
def isCoeDecl (declName : Name) : Bool :=
  declName == ``Coe.coe || declName == ``CoeTC.coe || declName == ``CoeHead.coe ||
  declName == ``CoeTail.coe || declName == ``CoeHTCT.coe || declName == ``CoeDep.coe ||
  declName == ``CoeT.coe || declName == ``CoeFun.coe || declName == ``CoeSort.coe ||
  declName == ``Lean.Internal.liftCoeM || declName == ``Lean.Internal.coeM ||
  declName == `CoeT.coeₓ || declName == `coeT || declName == `coeToLift || declName == `coeBaseₓ ||
  declName == `coe || declName == `liftT || declName == `lift || declName == `HasLiftT.lift ||
  declName == `coeB

/-- Expand coercions occurring in `e` (+ Lean 3 defs) -/
partial def expandCoe (e : Expr) : MetaM Expr :=
  withReducibleAndInstances do
    transform e (pre := step)
where
  step (e : Expr) : MetaM TransformStep := do
    let f := e.getAppFn
    if !f.isConst then
      return .continue
    else
      let declName := f.constName!
      if isCoeDecl declName then
        match (← unfoldDefinition? e) with
        | none   => return .continue
        | some e' =>
          let mut e' := e'.headBeta
          while e'.getAppFn.isProj do
            if let some f ← reduceProj? e'.getAppFn then
              e' := (mkAppN f e'.getAppArgs).headBeta
            else
              return .continue
          return .visit e'
      else
        return .continue

instance : ToExpr Syntax.Preresolved where
  toTypeExpr := mkConst ``Syntax.Preresolved
  toExpr
    | .namespace ns => mkApp (mkConst ``Syntax.Preresolved.namespace) (toExpr ns)
    | .decl n fields => mkApp2 (mkConst ``Syntax.Preresolved.decl) (toExpr n) (toExpr fields)

def trExprCore (ctx : Context) (cmdCtx : Elab.Command.Context) (cmdState : Elab.Command.State) (e : Expr) (ind? : Option (Name × Expr × List Name)) : MetaM Expr := do
  match ind? with
  | none => core e
  | some ⟨indName, indType, lps⟩ =>
    withLocalDeclD indName indType fun x => do
      let e := e.replace fun e => if e.isConstOf indName then some x else none
      let e ← core e
      let e := e.replace fun e =>
        if e == x then some (mkConst indName $ lps.map mkLevelParam)
        else if !e.hasFVar then (some e)
        else none
      pure e
where
  core e := do
    let mut e := e
    e ← replaceConstNames e
    e ← Meta.transform e (post := replaceSorryPlaceholders)
    e ← expandCoe e
    e ← translateNumbers e
    if let some (_, ap4) := (getRenameMap cmdState.env).find? `auto_param then
      e ← Meta.transform e (pre := translateAutoParams ap4)
    e ← heterogenize e
    reflToRfl e

  replaceConstNames (e : Expr) : MetaM Expr := pure <|
    e.replaceConstNames fun n => (getRenameMap cmdState.env).find? n |>.map (·.2)

  reflToRfl (e : Expr) : MetaM Expr := pure <|
    e.replace fun e =>
      if e.isAppOfArity `Eq.refl 2 then
        some $ e.withApp fun f args => mkAppN (mkConst `rfl f.constLevels!) args
      else none

  replaceSorryPlaceholders (e : Expr) : MetaM TransformStep := do
    if e.isAppOfArity sorryPlaceholderName 1 then
      let type := e.appArg!
      let e ← mkSorry type (synthetic := false)
      return TransformStep.done e
    else
      return TransformStep.done e

  translateAutoParams (ap4 : Name) (e : Expr) : MetaM TransformStep :=
    -- def auto_param : Sort u → name → Sort u :=
    -- λ (α : Sort u) (tac_name : name), α
    if e.isAppOfArity ap4 2 then do
      let level    := e.getAppFn.constLevels!.head!
      let type     := e.getArg! 0
      let tacName3 := e.getArg! 1
      try
        let tacName3 ← decodeName tacName3
        let tacName ← mkCandidateLean4NameForKindIO tacName3 ExprKind.eDef
        let substr : Expr := mkAppN (mkConst ``String.toSubstring) #[toExpr $ tacName.toString]
        let tacSyntax := mkAppN (mkConst ``Lean.Syntax.ident) #[mkConst ``Lean.SourceInfo.none, substr, toExpr tacName, toExpr ([] : List Syntax.Preresolved)]
        let e' := mkAppN (mkConst ``autoParam [level]) #[type, tacSyntax]
        unless ← Meta.isDefEq e e' do throwError "[translateAutoParams] introduced non-defeq, {e} != {e'}"
        pure $ TransformStep.done e'
      catch ex => do
        -- they prove theorems about auto_param!
        println! "[decode] {(← ex.toMessageData.toString)}"
        -- strip the auto_param?
        pure .continue
    else
      pure .continue

  mkCandidateLean4NameForKindIO (n3 : Name) (eKind : ExprKind) : IO Name := do
    (mkCandidateLean4NameForKind n3 eKind).toIO ctx {} cmdCtx cmdState

def trExpr (e : Expr) (ind? : Option (Name × Expr × List Name) := none) : BinportM Expr := do
  let ctx ← read
  let cmdCtx ← readThe Elab.Command.Context
  let cmdState ← getThe Elab.Command.State
  liftMetaM $ trExprCore ctx cmdCtx cmdState e ind?

end Mathport.Binary
