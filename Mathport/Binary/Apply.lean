/-
Copyright (c) 2021 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Selsam
-/
import Lean
import Mathport.Util.Misc
import Mathport.Binary.Config
import Mathport.Binary.Path
import Mathport.Binary.Basic
import Mathport.Binary.NDRec
import Mathport.Binary.EnvModification

namespace Mathport.Binary

open Std (HashMap HashSet)
open Lean Lean.Meta Lean.Elab Lean.Elab.Command

def addDecl (n : Name) (d : Declaration) : BinportM Unit := do
  let path34 := (← read).path34
  println! "[addDecl] START {path34.mrpath} {n}"
  Lean.addDecl d
  println! "[addDecl] END   {path34.mrpath} {n}"
  if shouldGenCodeFor d then
    match (← getEnv).compileDecl {} d with
    | Except.ok env    => println! "[compile] {n} SUCCESS!"
                          setEnv env
    | Except.error err => let msg ← err.toMessageData (← getOptions)
                          let msg ← msg.toString
                          println! "[compile] {n} {msg}"
where
  shouldGenCodeFor (d : Declaration) : Bool :=
    -- TODO: sadly, noncomputable comes after the definition
    -- (so if this isn't good enough, we will need to refactor)
    match d with
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
      env := addAlias env (← trName n1) (← trName n2)
    setEnv env

def applyMixfix (kind : MixfixKind) (n : Name) (prec : Nat) (tok : String) : BinportM Unit := do
  let n ← trName n

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
  let ns : Syntax := mkIdent $ s!"{"__".intercalate (← read).path34.mrpath.components}_{nextIdx}"
  let stx ← `(namespace $ns:ident $stx end $ns:ident)
  elabCommand stx

def applySimpLemma (n : Name) (prio : Nat) : BinportM Unit := do
  tryAddSimpLemma (← trName n) prio
  for eqn in (← get).name2equations.findD n [] do
    tryAddSimpLemma (← trName eqn) prio
where
  tryAddSimpLemma (n : Name) (prio : Nat) : BinportM Unit :=
    try
      liftMetaM $ addSimpLemma n False AttributeKind.global prio
      println! "[simp] {n} {prio}"
    catch ex => warn ex

def applyReducibility (n : Name) (status : ReducibilityStatus) : BinportM Unit := do
  -- (note: this will fail/no-op if it declares reducible in a new module)
  try setAttr { name := reducibilityToName status } (← trName n)
  catch ex => warn ex
where
  reducibilityToName (status : ReducibilityStatus) : Name :=
    match status with
    | ReducibilityStatus.reducible => `reducible
    | ReducibilityStatus.semireducible => `semireducible
    | ReducibilityStatus.irreducible => `irreducible

def applyProjection (proj : ProjectionInfo) : BinportM Unit := do
  setEnv $ addProjectionFnInfo (← getEnv) (← trName proj.projName) (← trName proj.ctorName) proj.nParams proj.index proj.fromClass

def applyClass (n : Name) : BinportM Unit := do
  let env ← getEnv
  if ← isAligned n then return ()
  -- (for meta classes, Lean4 won't know about the decl)
  match addClass env (← trName n) with
  | Except.error msg => warnStr msg
  | Except.ok env    => setEnv env

def applyInstance (nc ni : Name) (prio : Nat) : BinportM Unit := do
  -- (for meta instances, Lean4 won't know about the decl)
  -- TODO: `prio.pred`?
  if not $ (← read).config.disabledInstances.contains ni then
    try
      liftMetaM $ addInstance (← trName ni) AttributeKind.global prio
      setAttr { name := `inferTCGoalsRL } (← trName ni)
    catch ex => warn ex

def applyAxiomVal (ax : AxiomVal) : BinportM Unit := do
  let name ← trName ax.name
  let type ← trExpr ax.type

  if ← isAligned ax.name then return ()
  maybeRegisterEquation ax.name

  addDecl ax.name $ Declaration.axiomDecl {
    ax with
      name := name,
      type := type
  }

def applyTheoremVal (thm : TheoremVal) : BinportM Unit := do
  let name ← trName thm.name
  let type ← trExpr thm.type

  if ← isAligned thm.name then return ()
  maybeRegisterEquation thm.name

  if ← shouldAxiomatize thm.name then
    println! "sorry skipping: {thm.name}"
    addDecl thm.name $ Declaration.axiomDecl {
      thm with
        name     := name,
        type     := type,
        isUnsafe := false -- TODO: what to put here?
    }
  else
    let value ← trExpr thm.value
    addDecl thm.name $ Declaration.thmDecl {
      thm with
        name  := name,
        type  := type,
        value := value
    }
where
  shouldAxiomatize (thmName : Name) : BinportM Bool := do
    if (← read).config.sorries.contains thm.name then return true
    if (← read).config.skipProofs ∧ ¬ (← read).config.neverSorries.contains thm.name then return true
    return false

def applyDefinitionVal (defn : DefinitionVal) : BinportM Unit := do
  let name ← trName defn.name
  let type ← trExpr defn.type

  if ← isAligned defn.name then return ()
  if ← isBadSUnfold name then return ()

  let value ← trExpr defn.value

  addDecl defn.name $ Declaration.defnDecl {
    defn with
      name  := name,
      type  := type,
      value := value,
      hints := defn.hints
  }
where
  isBadSUnfold (n : Name) : BinportM Bool := do
    if !n.isStr then return false
    if n.getString! != "_sunfold" then return false
    match (← getEnv).find? (n.getPrefix ++ `_main) with
    | some cinfo =>
      match cinfo.value? with
      -- bad means the original function isn't actually recursive
      | some v => Option.isNone $ v.find? fun e => e.isConst && e.constName!.isStr && e.constName!.getString! == "brec_on"
      | _ => throwError "should have value"
    | _ => return false /- this can happen when e.g. `nat.add._main -> Nat.add` (which may be needed due to eqn lemmas) -/

def applyInductiveDecl (lps : List Name) (nParams : Nat) (ind : InductiveType) (isUnsafe : Bool) : BinportM Unit := do
  let name ← trName ind.name
  let type ← trExpr ind.type (reduce := false)

  if not (← isAligned ind.name) then
    let ctors ← ind.ctors.mapM fun (ctor : Constructor) => do
      let cname ← trName ctor.name
      let ctype ← trExpr ctor.type (reduce := false)
      pure { ctor with name := cname, type := ctype }
    addDecl ind.name $ Declaration.inductDecl lps nParams
      [{ ind with name := name, type := type, ctors := ctors }] isUnsafe
    mkAuxDecls name

  match ← liftMetaM $ mkNDRec name with
  | some ndRec => do
    let ndRecName := mkNDRecName name
    addDecl ndRecName ndRec
    setAttr { name := `reducible } ndRecName
  | none => pure ()

where
  mkAuxDecls (name : Name) : BinportM Unit :=
    try
      -- these may fail for the invalid inductive types currently being accepted
      -- by the temporary patch https://github.com/dselsam/lean4/commit/1bef1cb3498cf81f93095bda16ed8bc65af42535
      mkRecOn name
      mkCasesOn name
      mkNoConfusion name
      mkBelow name -- already there
      mkIBelow name
      mkBRecOn name
      mkBInductionOn name
    catch _ => pure ()


def applyModification (mod : EnvModification) : BinportM Unit := withReader (fun ctx => { ctx with currDecl := mod.toName }) do
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

end Mathport.Binary
