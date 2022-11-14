/-
Copyright (c) 2021 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Selsam
-/
import Lean
import Mathport.Util.Misc
import Mathport.Bridge.Config
import Mathport.Binary.Basic
import Mathport.Binary.NDRec
import Mathport.Binary.EnvModification
import Mathport.Binary.TranslateName
import Mathport.Binary.TranslateExpr

namespace Mathport.Binary

open Lean Lean.Meta Lean.Elab Lean.Elab.Command

def inCurrentModule [Monad M] [MonadEnv M] (n : Name) : M Bool :=
  return (← getEnv).getModuleIdxFor? n |>.isNone

def printIndType (lps : List Name) (indType : InductiveType) : BinportM Unit := do
  println! "[inductive] {indType.name}.\{{lps}}. : {indType.type}"
  for ctor in indType.ctors do
    println! "  {ctor.name} : {ctor.type}"

def printDeclDebug (decl : Declaration) : BinportM Unit := do
  match decl with
  | Declaration.thmDecl thm =>
    println! "--- {thm.name} ---"
    println! "[type]  {thm.type}"
    println! "[value] {thm.value}"
  | _ => pure ()

def stubValue : Declaration → MetaM Declaration
  | .thmDecl val => return .thmDecl { val with value := ← mkSorry val.type true }
  | .defnDecl val => return .opaqueDecl { val with value := ← mkSorry val.type true, isUnsafe := false }
  | .mutualDefnDecl defns => .mutualDefnDecl <$> defns.mapM fun defn =>
    return { defn with value := ← mkSorry defn.type true }
  | d => pure d

def stubType : Declaration → MetaM Declaration
  | .axiomDecl val =>
    return .axiomDecl { val with type := mkPUnit (← inferTypeD val.type) }
  | .thmDecl val => do
    stubValue (.thmDecl { val with type := mkPUnit (← inferTypeD val.type) })
  | .defnDecl val => do
    stubValue (.defnDecl { val with type := mkPUnit (← inferTypeD val.type) })
  | .opaqueDecl val =>
    return .opaqueDecl { val with type := mkPUnit (← inferTypeD val.type) }
  | .mutualDefnDecl defns => do
    stubValue <| .mutualDefnDecl <|← defns.mapM fun defn =>
      return { defn with type := mkPUnit (← inferTypeD defn.type) }
  | .inductDecl lp _ tys uns => (.inductDecl lp 0 · uns) <$> tys.mapM fun ty =>
    return { ty with
      type := ← try forallTelescopeReducing ty.type fun _ => pure
                catch _ => pure (.sort (.succ .zero))
      ctors := ← ty.ctors.mapM fun ctor =>
        return { ctor with type := .const ty.name (lp.map .param) } }
  | d => pure d
where
  inferTypeD ty := try inferType ty catch _ => pure (.sort .zero)
  mkPUnit tyty :=
    let u := match tyty with
    | .sort lvl => lvl
    | _ => .zero
    mkConst ``PUnit [u]

def refineAddDecl (decl : Declaration) : BinportM (Declaration × ClashKind) := do
  let path := (← read).path
  println! "[addDecl] START REFINE {path.mod3} {decl.toName}"
  let ⟨decl, clashKind⟩ ← refineLean4NamesAndUpdateMap decl
  match clashKind with
  | ClashKind.found "" =>
    println! "[addDecl] FOUND DEF-EQ {path.mod3} {decl.toName}"
  | ClashKind.found _ =>
    println! "[addDecl] FOUND DUBIOUS {path.mod3} {decl.toName}"
  | ClashKind.freshDecl =>
    println! "[addDecl] START CHECK  {path.mod3} {decl.toName}"
    try
      liftCoreM <| Lean.addDecl decl
    catch ex =>
      println! "[kernel] {← ex.toMessageData.toString}"
      if (← read).config.error2warning then
        -- printDeclDebug decl
        try
          println! "[addDecl] stubbing value of {decl.toName}"
          let decl ← liftMetaM <| stubValue decl
          liftCoreM <| Lean.addDecl decl
        catch _ =>
          println! "[addDecl] stubbing type of {decl.toName}"
          let decl ← liftMetaM <| stubType decl
          try
            liftCoreM <| Lean.addDecl decl
          catch _ =>
            println! "[addDecl] failed to port {decl.toName}"
            throw ex
      else throw ex

    modifyEnv fun env => binportTag.ext.addEntry env decl.toName
    println! "[addDecl] END CHECK    {path.mod3} {decl.toName}"
    if shouldGenCodeFor decl then
      println! "[compile] {decl.toName} START"
      match (← getEnv).compileDecl {} decl with
      | Except.ok env    => println! "[compile] {decl.toName} SUCCESS!"
                            setEnv env
      | Except.error err => let msg := err.toMessageData (← getOptions)
                            let msg ← msg.toString
                            println! "[compile] {decl.toName} {msg}"
  pure (decl, clashKind)

where
  shouldGenCodeFor (decl : Declaration) : Bool :=
    -- TODO: sadly, noncomputable comes after the definition
    -- (so if this isn't good enough, we will need to refactor)
    match decl with
    | Declaration.defnDecl _ => false -- https://github.com/leanprover-community/mathport/issues/172
    | _                      => false

def setAttr (attr : Attribute) (declName : Name) : BinportM Unit := do
  let env ← getEnv
  match getAttributeImpl env attr.name with
  | Except.error errMsg => throwError errMsg
  | Except.ok attrImpl  => liftMetaM $ attrImpl.add declName attr.stx attr.kind

def equationFor? (n : Name) : Option Name :=
  let n₁ : Name := n.getPrefix
  if n₁.isStr && n₁.getString! == "equations" then some n₁.getPrefix
  else none

def maybeRegisterEquation (eqn : Name) : BinportM Unit := do
  -- example: list.nth.equations._eqn_1
  match equationFor? eqn with
  | some defn => modify λ s => { s with name2equations := s.name2equations.insertWith (· ++ ·) defn [eqn] }
  | none => pure ()

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
      println! "[export] SKIP {n1} := {n2}"
      continue
    setEnv env

def applyMixfix (kind : MixfixKind) (n : Name) (prec : Nat) (tok : String) : BinportM Unit := do
try
  let n ← lookupNameExt! n

  -- For now, we avoid the `=` `=` clash by making all Mathlib notations
  -- lower priority than the Lean4 ones.
  let prio : Nat := (← liftMacroM <| evalOptPrio none).pred

  let stxPrec  : Syntax.Prec := Quote.quote prec
  let stxName  : Option Syntax.Ident := none
  let stxPrio  : Option Syntax.Prio := some (quote prio)
  let stxOp    : TSyntax strLitKind := Syntax.mkStrLit tok
  let stxFun   : Syntax.Term := mkIdent n

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
      let correctPrec : Option Syntax.Prec := some (quote Parser.maxPrec)
      `(notation $[: $correctPrec]? $[(name := $stxName)]? $[(priority := $stxPrio)]? $stxOp:str => $stxFun)

  let nextIdx : Nat := (← get).nNotations
  modify λ s => { s with nNotations := nextIdx + 1 }
  let ns : Syntax.Ident := mkIdent s!"{"__".intercalate ((← read).path.mod4.components.map Name.getString!)}_{nextIdx}"
  let stx ← `(namespace $ns $stx end $ns)
  elabCommand stx
catch ex => warn ex

def applySimpLemma (n : Name) (prio : Nat) : BinportM Unit := do
  -- TODO: remove these once https://github.com/leanprover-community/mathlib/pull/8738 (+ friends) are merged
  let badSimps := #[`set.eq_on_empty, `punit.eq_punit, `list.cons_injective, `list.length_injective, `list.reverse_injective]
  if badSimps.contains n then return ()

  tryAddSimpLemma (← lookupNameExt! n) prio
  for eqn in (← get).name2equations.findD n [] do
    tryAddSimpLemma (← lookupNameExt! eqn) prio
where
  tryAddSimpLemma (n : Name) (prio : Nat) : BinportM Unit :=
    try
      liftMetaM $ addSimpTheorem (ext := simpExtension) (declName := n) (post := True) (inv := False) (attrKind := AttributeKind.global) (prio := prio)
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
    let structName := ctorName.getPrefix
    unless ← inCurrentModule structName do return
    setEnv $ addProjectionFnInfo (← getEnv) projName ctorName proj.nParams proj.index proj.fromClass
    let descr := (← get).structures.findD structName ⟨structName, #[]⟩
    match (← getEnv).find? ctorName with
    | some (ConstantInfo.ctorInfo ctor) =>
      let fieldInfo ← mkFieldInfo ctor.numParams ctor.type projName proj.projName
      modify fun s => { s with structures := s.structures.insert structName ⟨descr.structName, descr.fields.push fieldInfo⟩ }
    | _ => warnStr "projection for something other than constructor {projName}, {ctorName}"
  catch ex => warn ex
where
  mkFieldInfo (numParams : Nat) (ctorType : Expr) (projName projName3 : Name) : BinportM StructureFieldInfo := do
    match projName, projName3 with
    | Name.str _ fieldName .., Name.str _ fieldName3 .. =>
      pure {
        fieldName
        projFn := projName
        subobject? := getSubobject? numParams ctorType fieldName3
        -- TODO: what to put here?
        binderInfo := BinderInfo.default
      }
    | _, _ => throwError "unexpected projName with num field: {projName}"

  getSubobject? (numParams : Nat) (type : Expr) (fieldName3 : String) : Option Name := Id.run do
    -- Note: we do not translate binder names, so we need the *lean3* fieldName here
    let candidateName := "_" ++ fieldName3
    let mut type := type
    let mut i    := 0

    while type.isForall do
      if i ≥ numParams then
        match type.bindingName! with
        | Name.str Name.anonymous s .. =>
          if s == candidateName then
            return some type.bindingDomain!.getAppFn.constName!
        | _ => pure ()
      type := type.bindingBody!
      i := i + 1
    return none

def applyClass (n : Name) : BinportM Unit := do
  -- (for meta classes, Lean4 won't know about the decl)
  try
    match addClass (← getEnv) (← lookupNameExt! n) with
    | Except.error msg => warnStr msg
    | Except.ok env    => setEnv env
  catch ex => warn ex

def applyInstance (_nc ni : Name) (prio : Nat) : BinportM Unit := do
  -- (for meta instances, Lean4 won't know about the decl)
  -- TODO: `prio.pred`?
  if (← read).config.disabledInstances.contains ni then return ()
  try
    liftMetaM $ addInstance (← lookupNameExt! ni) AttributeKind.global prio
    setAttr { name := `infer_tc_goals_rl } (← lookupNameExt! ni)
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

  let mut hints := defn.hints
  let mut forceAbbrev := false

  if (← read).config.forceAbbrevs.contains defn.name then
    hints := ReducibilityHints.abbrev
    forceAbbrev := true

  -- Only for definitions (really, instances) do we try to translate the coes
  let type  ← trExpr defn.type
  let value ← trExpr defn.value

  discard <| refineAddDecl $ Declaration.defnDecl { defn with
    type  := type
    value := value
    hints := hints
  }

  if forceAbbrev then applyReducibility defn.name ReducibilityStatus.reducible
where
  isBadSUnfold3 (n3 : Name) : BinportM Bool := do
    if !n3.isStr then return false
    if n3.getString! != "_sunfold" then return false
    let pfix4 ← lookupNameExt! n3.getPrefix
    match (← getEnv).find? (pfix4 ++ `_main) with
    | some cinfo =>
      match cinfo.value? with
      -- bad means the original function isn't actually recursive
      | some v => pure $ Option.isNone $ v.find? fun e =>
        e.isConst && e.constName!.isStr && e.constName!.getString! == "brec_on"
      | _ => throwError "should have value"
    | _ => return false /- this can happen when e.g. `nat.add._main -> Nat.add` (which may be needed due to eqn lemmas) -/

def applyInductiveDecl (lps : List Name) (nParams : Nat) (indType : InductiveType) (isUnsafe : Bool) : BinportM Unit := do
  -- The `Module` inductive type includes `module` in its constructor types, which gets mapped to `Module`, causing confusion.
  -- In the past, we worked around this by changing `module` -> `ModuleS`, but this is highly undesirable.
  -- Now, we simple first change all the `Module` names to `_indSelf`, then change `_indSelf` later.
  let indType := indType.replaceSelfWithPlaceholder
  let ind? := some (indType.name, indType.type, lps)
  let decl := Declaration.inductDecl lps nParams [{ indType with
    type  := (← trExpr indType.type),
    ctors := (← indType.ctors.mapM fun ctor => do pure { ctor with type := (← trExpr ctor.type (ind? := ind?)) })
  }] isUnsafe

  let (decl, clashKind) ← refineAddDecl decl
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
      liftMetaM $ Lean.mkNoConfusion name
      mkBelow name
      mkIBelow name
      mkBRecOn name
      mkBInductionOn name
    catch _ => pure ()

def applyPosition (n : Name) (line col : Nat) : BinportM Unit := do
  let range := DeclarationRanges.mk
        { pos := { line := line, column := col },
          charUtf16 := col,
          endPos := { line := line, column := col },
          endCharUtf16 := col }
        { pos := { line := line, column := col },
          charUtf16 := col,
          endPos := { line := line, column := col },
          endCharUtf16 := col}
  if let some n ← lookupNameExt n then
    if ← inCurrentModule n then
      Lean.addDeclarationRanges n range

def applyModification (mod : EnvModification) : BinportM Unit := withReader (fun ctx => { ctx with currDecl := mod.toName }) do
  println! "[apply] {mod}"
  match mod with
  | EnvModification.mixfix .. -- synport handles notation
  | EnvModification.private ..
  | EnvModification.protected ..
  | EnvModification.position ..         => pure ()
  | EnvModification.export d            => applyExport d
  | EnvModification.simp n prio         => applySimpLemma n prio
  | EnvModification.reducibility n kind => applyReducibility n kind
  | EnvModification.projection proj     => applyProjection proj
  | EnvModification.class n             => applyClass n
  | EnvModification.instance nc ni prio => applyInstance nc ni prio
  | EnvModification.decl d              =>
    match d with
    | Declaration.axiomDecl ax                => applyAxiomVal ax
    | Declaration.thmDecl thm                 => applyTheoremVal thm
    | Declaration.defnDecl defn               => applyDefinitionVal defn
    | Declaration.inductDecl lps nps [ind] iu => applyInductiveDecl lps nps ind iu
    | _                                       => throwError "unexpected declaration type"

def applyModificationPost (mod : EnvModification) : BinportM Unit := do
  match mod with
  | EnvModification.position n line col => applyPosition n line col
  | _ => pure ()

def postprocessModule : BinportM Unit := do
  registerStructures
where
  registerStructures := do
    for (structName, structDescr) in (← get).structures.toList do
      modifyEnv fun env => registerStructure env structDescr
      println! "[registerStructure] {structName}"
      for { fieldName, projFn, subobject?, .. } in structDescr.fields do
        println! "[registerStructure.field] {structName} {fieldName} {projFn} {subobject?}"

end Mathport.Binary
