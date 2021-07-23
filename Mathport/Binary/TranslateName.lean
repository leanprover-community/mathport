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

namespace Mathport.Binary

open Lean Lean.Meta

inductive ExprKind
  | eType
  | eProp
  | eDef
  | eProof

partial def translatePrefix (nameInfoMap : HashMap Name NameInfo) (pfix3 : Name) : Name := do
  match nameInfoMap.find? pfix3 with
  | some ⟨pfix4, _⟩ => pfix4
  | none =>
    match pfix3 with
    | Name.num pfix k .. => Name.mkNum (translatePrefix nameInfoMap pfix3) k
    | Name.str pfix s .. => Name.mkStr (translatePrefix nameInfoMap pfix3) s.snake2pascal
    | Name.anonymous ..  => Name.anonymous

def translateSuffix (s : String) (eKind : ExprKind) : String := do
  match eKind with
  | ExprKind.eType  => s.snake2pascal
  | ExprKind.eProp  => s.snake2pascal
  | ExprKind.eDef   => s.snake2camel
  | ExprKind.eProof => s

def getExprKind (type : Expr) : MetaM ExprKind := do
    let x ← mkFreshExprMVar (some type)
    if ← isProp x then ExprKind.eProp
    else if ← isType x then ExprKind.eType
    else if ← isProof x then ExprKind.eProof
    else ExprKind.eDef

def mkCandidateLean4NameForKind (nameInfoMap : HashMap Name NameInfo) (n3 : Name) (eKind : ExprKind) : Name :=
  let pfix4 := translatePrefix nameInfoMap n3.getPrefix
  match n3 with
  | Name.num _ k ..  => Name.mkNum pfix4 k
  | Name.str _ s ..  => Name.mkStr pfix4 (translateSuffix s eKind)
  | _                => Name.anonymous

partial def mkCandidateLean4Name (n3 : Name) (type : Expr) : BinportM Name := do
  if (← get).nameInfoMap.contains n3 then throwError "mkCandidateLean4Name should not be called after adding decl, '{n3}'"
  pure $ mkCandidateLean4NameForKind (← get).nameInfoMap n3 (← liftMetaM <| getExprKind type)

open ClashKind

-- Given a declaration whose expressions have already been translated to Lean4
-- (i.e. the names *occurring* in the expressions have been translated
partial def determineLean4Name (decl : Declaration) : BinportM (Declaration × ClashKind) := do
  match decl with
  | Declaration.axiomDecl ax                =>
    refineAx { ax with name := ← mkCandidateLean4Name ax.name ax.type }
  | Declaration.thmDecl thm                 =>
    refineThm { thm with name := ← mkCandidateLean4Name thm.name thm.type}
  | Declaration.defnDecl defn               =>
    refineDef { defn with name := ← mkCandidateLean4Name defn.name defn.type }
  | Declaration.inductDecl lps nps [indType] iu =>
    refineInd lps nps (indType.updateName <| (← mkCandidateLean4Name indType.name indType.type)) iu
  | _                                       => throwError "unexpected declaration type"

where
  refineAx (ax3 : AxiomVal) : BinportM (Declaration × ClashKind) := do
    match (← getEnv).find? ax3.name with
    | some (ConstantInfo.axiomInfo ax4) =>
      if ← isDefEqUpto ax3.levelParams ax3.type ax4.levelParams ax4.type then
        pure (Declaration.axiomDecl ax3, foundDefEq)
      else
        refineAx { ax3 with name := extendName ax3.name }
    | none => pure (Declaration.axiomDecl ax3, freshDecl)
    | _ => throwError "refineAx: unexpected theorem"

  refineThm (thm3 : TheoremVal) : BinportM (Declaration × ClashKind) := do
    match (← getEnv).find? thm3.name with
    | some (ConstantInfo.thmInfo thm4) =>
      if ← isDefEqUpto thm3.levelParams thm3.type thm4.levelParams thm4.type then
        pure (Declaration.thmDecl thm3, foundDefEq)
      else
        refineThm { thm3 with name := extendName thm3.name }
    | none => pure (Declaration.thmDecl thm3, freshDecl)
    | _ => throwError "refineNameThm: unexpected theorem"

  refineDef (defn3 : DefinitionVal) : BinportM (Declaration × ClashKind) := do
    match (← getEnv).find? defn3.name with
    | some (ConstantInfo.defnInfo defn4) =>
      if ← isDefEqUpto defn3.levelParams defn3.value defn4.levelParams defn4.value then
        pure (Declaration.defnDecl defn3, foundDefEq)
      else
        refineDef { defn3 with name := extendName defn3.name }
    | none => pure (Declaration.defnDecl defn3, freshDecl)
    | _ => throwError "refineDef: unexpected theorem"

  refineInd (lps : List Name) (numParams : Nat) (indType3 : InductiveType) (isUnsafe : Bool) : BinportM (Declaration × ClashKind) := do
    match (← getEnv).find? indType3.name with
    | some (ConstantInfo.inductInfo indVal) =>
      let recurse := refineInd lps numParams (indType3.updateName (extendName indType3.name)) isUnsafe
      if indVal.numParams ≠ numParams then recurse
      else if not (← isDefEqUpto lps indType3.type indVal.levelParams indVal.type) then recurse
      else
        let ctors := indType3.ctors.zip indVal.ctors
        let ctorsDefEq (ctor3 : Constructor) (name4 : Name) : BinportM Bool := do
          let some (ConstantInfo.ctorInfo ctor4) ← (← getEnv).find? name4 | throwError "constructor '{name4}' not found"
          isDefEqUpto lps ctor3.type ctor4.levelParams ctor4.type
        if ← ctors.allM (fun (x, y) => ctorsDefEq x y) then
          pure (Declaration.inductDecl lps numParams [indType3] isUnsafe, foundDefEq)
        else recurse
    | none => pure (Declaration.inductDecl lps numParams [indType3] isUnsafe, freshDecl)
    | _ => throwError "refineInd: unexpected theorem"

  isDefEqUpto (lvls₁ : List Name) (t₁ : Expr) (lvls₂ : List Name) (t₂ : Expr) : BinportM Bool := liftMetaM do
    isDefEq t₁ (t₂.instantiateLevelParams lvls₂ $ lvls₁.map mkLevelParam)

  extendName : Name → Name
    | Name.str p s _ => Name.mkStr p (s ++ "'")
    | n              => Name.mkStr n "'"

def determineLean4NameAndUpdateMap (decl : Declaration) : BinportM Declaration := do
  let (decl', clashKind) ← determineLean4Name decl
  for (n3, n4) in List.zip decl.collectNames decl'.collectNames do
    modify fun s => { s with nameInfoMap := s.nameInfoMap.insert n3 ⟨n4, clashKind⟩ }
  pure decl'

def lookupLean4Name (n3 : Name) : BinportM Name := do
  match (← get).nameInfoMap.find? n3 with
  | some ⟨n4, _⟩ => pure n4
  | none         => throwError "name not found: '{n3}'"

def lookupLean4NameInCore (nameInfoMap : HashMap Name NameInfo) (n3 : Name) : CoreM Name := do
  match nameInfoMap.find? n3 with
  | some ⟨n4, _⟩ => pure n4
  | none         => throwError "name not found: '{n3}'"

end Mathport.Binary
