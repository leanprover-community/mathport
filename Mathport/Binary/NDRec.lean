/-
Copyright (c) 2020 Gabriel Ebner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Ebner
-/
import Lean
import Mathport.Util.Misc

namespace Mathport.Binary

open Lean Lean.Meta

def mkNDRec (indTy ndRecName : Name) : MetaM (Option Declaration) := do
  let some (ConstantInfo.inductInfo indI) ← getConst? indTy | throwError (toString indTy)
  let indTy' ← inferType (mkConst indI.name (indI.levelParams.map mkLevelParam))
  let useDepElim ← forallTelescopeReducing indTy' $ fun _ indSort => do
    let .sort level := indSort | throwError (toString indSort)
    pure $ level.normalize != levelZero
  if useDepElim then return none

  let some (ConstantInfo.recInfo recI) ← getConst? (indTy ++ `rec) | throwError (toString $ indTy ++ `rec)
  let crec := mkConst recI.name (recI.levelParams.map mkLevelParam);
  let recTy ← inferType crec;
  forallTelescopeReducing recTy $ fun args _ => do
    let (params, args) := args.splitAt recI.numParams;
    let (motive, args) := args.splitAt 1;
    let motive := motive.get! 0;
    let motiveTy ← inferType motive;
    forallTelescopeReducing motiveTy $ fun _ elimSort => do
      let .sort elimLevel := elimSort | throwError (toString elimSort)
      let (_minorPremises, args) := args.splitAt recI.numMinors
      let (indices, major) := args.splitAt recI.numIndices
      let majorPremise := major.get! 0
      let oldMotiveTy ← Meta.mkForallFVars indices (mkSort elimLevel)
      withLocalDecl `C BinderInfo.implicit oldMotiveTy $ fun oldMotive => do
        let newMotive ← Meta.mkLambdaFVars (indices.push majorPremise) (mkAppN oldMotive indices)
        let val ← Meta.mkLambdaFVars ((params).push oldMotive) $ mkAppN crec ((params).push newMotive)
        let ty ← inferType val
        pure $ Declaration.defnDecl {
            name        := ndRecName,
            levelParams := recI.levelParams,
            type        := ty,
            value       := val,
            safety      := DefinitionSafety.safe,
            hints       := ReducibilityHints.abbrev,
        }

end Mathport.Binary
