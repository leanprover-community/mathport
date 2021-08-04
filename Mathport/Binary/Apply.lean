/-
Copyright (c) 2021 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Selsam
-/
import Lean
import Mathport.Util.Misc
import Mathport.Util.While
import Mathport.Binary.Config
import Mathport.Binary.Basic
import Mathport.Binary.NDRec
import Mathport.Binary.EnvModification
import Mathport.Binary.TranslateName
import Mathport.Binary.TranslateExpr

namespace Mathport.Binary

open Std (HashMap HashSet)
open Lean Lean.Meta Lean.Elab Lean.Elab.Command

def printIndType (lps : List Name) (indType : InductiveType) : BinportM Unit := do
  println! "[inductive] {indType.name}.\{{lps}}. : {indType.type}"
  for ctor in indType.ctors do
    println! "  {ctor.name} : {ctor.type}"

def refineAddDecl (decl : Declaration) : BinportM (Declaration × ClashKind) := do
  let path := (← read).path
  println! "[addDecl] START REFINE {path.mod3} {decl.toName}"
  let ⟨decl, clashKind⟩ ← refineLean4NamesAndUpdateMap decl
  match clashKind with
  | ClashKind.foundDefEq =>
    println! "[addDecl] FOUND DEF-EQ {path.mod3} {decl.toName}"
  | ClashKind.freshDecl =>
    println! "[addDecl] START CHECK  {path.mod3} {decl.toName}"

/-
    match decl with
    | Declaration.defnDecl defn => println! "[defn] {defn.name} : {defn.type} := {defn.value}"
    | Declaration.inductDecl lps _ [indType] _ => printIndType lps indType
    | _ => pure ()
-/
    Lean.addDecl decl
    println! "[addDecl] END CHECK    {path.mod3} {decl.toName}"
    if shouldGenCodeFor decl then
      println! "[compile] {decl.toName} START"
      match (← getEnv).compileDecl {} decl with
      | Except.ok env    => println! "[compile] {decl.toName} SUCCESS!"
                            setEnv env
      | Except.error err => let msg ← err.toMessageData (← getOptions)
                            let msg ← msg.toString
                            println! "[compile] {decl.toName} {msg}"
  pure (decl, clashKind)

where
  shouldGenCodeFor (decl : Declaration) : Bool :=
    -- TODO: sadly, noncomputable comes after the definition
    -- (so if this isn't good enough, we will need to refactor)
    match decl with
    | Declaration.defnDecl _ => true
    | _                      => false

def setAttr (attr : Attribute) (declName : Name) : BinportM Unit := do
  let env ← getEnv
  match getAttributeImpl env attr.name with
  | Except.error errMsg => throwError errMsg
  | Except.ok attrImpl  => liftMetaM $ attrImpl.add declName attr.stx attr.kind

def maybeRegisterEquation (n : Name) : BinportM Unit := do
  -- example: list.nth.equations._eqn_1
  let n₁ : Name := n.getPrefix
  if n₁.isStr && n₁.getString! == "equations" then
    modify λ s => { s with name2equations := s.name2equations.insertWith (· ++ ·) n₁.getPrefix [n] }

def applyExport (d : ExportDecl) : BinportM Unit := do
  -- we use the variable names of elabExport
  if not d.exceptNames.isEmpty then
    warnStr s!"export of {d.ns} with exceptions is ignored"
  else if d.nsAs != Name.anonymous then
    warnStr s!"export of {d.ns} with 'nsAs' is ignored"
  else if ¬ d.hadExplicit then
    warnStr s!"export of {d.ns} with no explicits is ignored"
  else
    let mut env ← getEnv
    for (n1, n2) in d.renames do
      -- TODO: naive name translation doesn't work for the alias
      -- We should probably inspect the suffixes and modify/remove the prefixes
      -- env := addAlias env (← lookupLean4Name n1) (← lookupLean4Name n2)
      println! "[export] SKIP {n1} := {n1}"
      continue
    setEnv env

def applyMixfix (kind : MixfixKind) (n : Name) (prec : Nat) (tok : String) : BinportM Unit := do
try
  let n ← lookupNameExt! n

  -- For now, we avoid the `=` `=` clash by making all Mathlib notations
  -- lower priority than the Lean4 ones.
  let prio : Nat := (← liftMacroM <| evalOptPrio none).pred

  let stxPrec  : Syntax := Syntax.mkNumLit (toString prec)
  let stxName  : Option Syntax := none
  let stxPrio  : Option Syntax := quote prio
  let stxOp    : Syntax := Syntax.mkStrLit tok
  let stxFun   : Syntax := Syntax.ident SourceInfo.none n.toString.toSubstring n []

  let stx ←
    match kind with
    | MixfixKind.infixl =>
      `(infixl:$stxPrec $[(name := $stxName)]? $[(priority := $stxPrio)]? $stxOp => $stxFun)
    | MixfixKind.infixr =>
      `(infixr:$stxPrec $[(name := $stxName)]? $[(priority := $stxPrio)]? $stxOp => $stxFun)
    | MixfixKind.prefix =>
      `(prefix:$stxPrec $[(name := $stxName)]? $[(priority := $stxPrio)]? $stxOp => $stxFun)
    | MixfixKind.postfix =>
      `(postfix:$stxPrec $[(name := $stxName)]? $[(priority := $stxPrio)]? $stxOp => $stxFun)
    | MixfixKind.singleton =>
      let correctPrec : Option Syntax := Syntax.mkNumLit (toString Parser.maxPrec)
      `(notation $[: $correctPrec]? $[(name := $stxName)]? $[(priority := $stxPrio)]? $stxOp => $stxFun)

  let nextIdx : Nat ← (← get).nNotations
  modify λ s => { s with nNotations := nextIdx + 1 }
  let ns : Syntax := mkIdent $ s!"{"__".intercalate ((← read).path.mod4.components.map Name.getString!)}_{nextIdx}"
  let stx ← `(namespace $ns:ident $stx end $ns:ident)
  elabCommand stx
catch ex => warn ex

def applySimpLemma (n : Name) (prio : Nat) : BinportM Unit := do
  tryAddSimpLemma (← lookupNameExt! n) prio
  for eqn in (← get).name2equations.findD n [] do
    tryAddSimpLemma (← lookupNameExt! eqn) prio
where
  tryAddSimpLemma (n : Name) (prio : Nat) : BinportM Unit :=
    try
      liftMetaM $ addSimpLemma n False AttributeKind.global prio
      println! "[simp] {n} {prio}"
    catch ex => warn ex

def applyReducibility (n : Name) (status : ReducibilityStatus) : BinportM Unit := do
  -- (note: this will fail/no-op if it declares reducible in a new module)
  try setAttr { name := reducibilityToName status } (← lookupNameExt! n)
  catch ex => warn ex
where
  reducibilityToName (status : ReducibilityStatus) : Name :=
    match status with
    | ReducibilityStatus.reducible     => `reducible
    | ReducibilityStatus.semireducible => `semireducible
    | ReducibilityStatus.irreducible   => `irreducible

def applyProjection (proj : ProjectionInfo) : BinportM Unit := do
  try
    -- we lookup names inside `try`, because meta things may have been skipped
    let projName ← lookupNameExt! proj.projName
    let ctorName ← lookupNameExt! proj.ctorName
    let indName := ctorName.getPrefix
    setEnv $ addProjectionFnInfo (← getEnv) projName ctorName proj.nParams proj.index proj.fromClass
    let descr := (← get).structures.findD indName ⟨indName, #[]⟩
    match (← getEnv).find? ctorName with
    | some (ConstantInfo.ctorInfo ctor) =>
      let fieldInfo ← mkFieldInfo ctor.numParams ctor.type projName
      modify fun s => { s with structures := s.structures.insert indName ⟨descr.structName, descr.fields.push fieldInfo⟩ }
    | _ => warnStr "projection for something other than constructor {projName}, {ctorName}"
  catch ex => warn ex
where
  mkFieldInfo (numParams : Nat) (ctorType : Expr) (projName : Name) : BinportM StructureFieldInfo := do
    match projName with
    | Name.str _ fieldName .. =>
      pure {
        fieldName := fieldName,
        projFn := projName,
        subobject? := (collectSubobjects numParams ctorType).find? fieldName
      }
    | _ => throwError "unexpected projName with num field: {projName}"

  collectSubobjects (numParams : Nat) (type : Expr) : HashMap Name Name := do
    let mut subobjects : HashMap Name Name := {}
    let mut type := type
    let mut i    := 0
    while type.isForall do
      if i > numParams then
        let name := type.bindingName!
        if name.isStr && name.getString!.startsWith "_to_" then
          let parentName := type.bindingDomain!.getAppFn.constName!
          subobjects := subobjects.insert name parentName
      type := type.bindingDomain!
    subobjects

def applyClass (n : Name) : BinportM Unit := do
  -- (for meta classes, Lean4 won't know about the decl)
  try
    match addClass (← getEnv) (← lookupNameExt! n) with
    | Except.error msg => warnStr msg
    | Except.ok env    => setEnv env
  catch ex => warn ex

def applyInstance (nc ni : Name) (prio : Nat) : BinportM Unit := do
  -- (for meta instances, Lean4 won't know about the decl)
  -- TODO: `prio.pred`?
  if not $ (← read).config.disabledInstances.contains ni then
    try
      liftMetaM $ addInstance (← lookupNameExt! ni) AttributeKind.global prio
      setAttr { name := `inferTCGoalsRL } (← lookupNameExt! ni)
    catch ex => warn ex

def applyAxiomVal (ax : AxiomVal) : BinportM Unit := do
  let (decl, clashKind) ← refineAddDecl $ Declaration.axiomDecl { ax with
    type := (← trExpr ax.type)
  }
  if clashKind == ClashKind.freshDecl then maybeRegisterEquation decl.toName

def applyTheoremVal (thm : TheoremVal) : BinportM Unit := do
  let (decl, clashKind) ← refineAddDecl $ Declaration.thmDecl { thm with
    type := (← trExpr thm.type),
    value := (← trExpr thm.value)
  }
  if clashKind == ClashKind.freshDecl then maybeRegisterEquation decl.toName

def applyDefinitionVal (defn : DefinitionVal) : BinportM Unit := do
  if ← isBadSUnfold3 defn.name then return ()

  -- TODO: MetaM does not have a def-eq cache, and so whereas Lean3 was robust to some
  -- manually written `to_*` definitions not disable self_opt, a single bad definition
  -- can (currently) cause exponential blowup in Lean4.
  -- As a workaround, we mark anything of the form `to_*` as abbrevs.
  let hints :=
    if defn.name.isStr && defn.name.getString!.startsWith "to_" then
      ReducibilityHints.abbrev
    else defn.hints

  discard <| refineAddDecl $ Declaration.defnDecl { defn with
    type  := (← trExpr defn.type)
    value := (← trExpr defn.value)
    hints := hints
  }
where
  isBadSUnfold3 (n3 : Name) : BinportM Bool := do
    if !n3.isStr then return false
    if n3.getString! != "_sunfold" then return false
    let pfix4 ← lookupNameExt! n3.getPrefix
    match (← getEnv).find? (pfix4 ++ `_main) with
    | some cinfo =>
      match cinfo.value? with
      -- bad means the original function isn't actually recursive
      | some v => Option.isNone $ v.find? fun e => e.isConst && e.constName!.isStr && e.constName!.getString! == "brec_on"
      | _ => throwError "should have value"
    | _ => return false /- this can happen when e.g. `nat.add._main -> Nat.add` (which may be needed due to eqn lemmas) -/

def applyInductiveDecl (lps : List Name) (nParams : Nat) (indType : InductiveType) (isUnsafe : Bool) : BinportM Unit := do
  let (decl, clashKind) ← refineAddDecl $ Declaration.inductDecl lps nParams [{ indType with
    type  := (← trExpr indType.type),
    ctors := (← indType.ctors.mapM fun ctor => do pure { ctor with type := (← trExpr ctor.type) })
  }] isUnsafe
  if clashKind == ClashKind.freshDecl then mkAuxDecls decl.toName

  match ← liftMetaM $ mkNDRec decl.toName (indType.name ++ `ndrec /- old name -/) with
  | some ndRec => do
    -- TODO: this will create a spurious alignment, and will *miss* the alignment `eq.rec` -> `Eq.ndrec`
    -- For now, we just add the missing alignment manually
    let (ndRecDecl, clashKind) ← refineAddDecl ndRec
    addNameAlignment (indType.name ++ `rec) ndRecDecl.toName
    if clashKind == ClashKind.freshDecl then setAttr { name := `reducible } ndRecDecl.toName
  | none => pure ()

where
  mkAuxDecls (name : Name) : BinportM Unit := do
    try
      -- these may fail for the invalid inductive types currently being accepted
      -- by the temporary patch https://github.com/dselsam/lean4/commit/1bef1cb3498cf81f93095bda16ed8bc65af42535
      mkRecOn name
      mkCasesOn name
      mkNoConfusion name
      mkBelow name
      mkIBelow name
      mkBRecOn name
      mkBInductionOn name
    catch _ => pure ()


def applyModification (mod : EnvModification) : BinportM Unit := withReader (fun ctx => { ctx with currDecl := mod.toName }) do
  println! "[apply] {mod}"
  match mod with
  | EnvModification.export d               => applyExport d
  | EnvModification.mixfix kind n prec tok => applyMixfix kind n prec tok
  | EnvModification.simp n prio            => applySimpLemma n prio
  | EnvModification.reducibility n kind    => applyReducibility n kind
  | EnvModification.projection proj        => applyProjection proj
  | EnvModification.class n                => applyClass n
  | EnvModification.instance nc ni prio    => applyInstance nc ni prio
  | EnvModification.private _ _            => pure ()
  | EnvModification.protected n            => pure ()
  | EnvModification.decl d                 =>
    match d with
    | Declaration.axiomDecl ax                => applyAxiomVal ax
    | Declaration.thmDecl thm                 => applyTheoremVal thm
    | Declaration.defnDecl defn               => applyDefinitionVal defn
    | Declaration.inductDecl lps nps [ind] iu => applyInductiveDecl lps nps ind iu
    | _                                       => throwError "unexpected declaration type"

def postprocessModule : BinportM Unit := do
  registerStructures
where
  registerStructures := do
    for (structName, structDescr) in (← get).structures.toList do
      modifyEnv fun env => registerStructure env structDescr
      println! "[registerStructure] {structName}"
      for ⟨fieldName, projName, subobject?⟩ in structDescr.fields do
        println! "[registerStructure.field] {structName} {fieldName} {projName} {subobject?}"

end Mathport.Binary
