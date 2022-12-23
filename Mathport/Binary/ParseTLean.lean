/-
Copyright (c) 2020 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Selsam, Gabriel Ebner
-/
import Lean
import Std.Data.List.Basic
import Mathport.Util.Parse
import Mathport.Binary.Basic
import Mathport.Binary.EnvModification

namespace Mathport.Binary

open Lean

structure ParserState where
  names            : Array Name            := #[Name.anonymous]
  levels           : Array Level           := #[levelZero]
  exprs            : Array Expr            := #[]
  envModifications : Array EnvModification := #[]
  ind2params       : HashMap Name Nat      := {}

abbrev ParseM := StateRefT ParserState IO

private def nat2expr (i : Nat) : ParseM Expr := do
  let s ← get
  if h : i < s.exprs.size then return s.exprs[i]
  throw $ IO.userError s!"[nat2expr] {i} > {s.exprs.size}"

private def nat2level (i : Nat) : ParseM Level := do
  let s ← get
  if h : i < s.levels.size then return s.levels[i]
  throw $ IO.userError s!"[nat2level] {i} > {s.levels.size}"

private def nat2name (i : Nat) : ParseM Name := do
  let s ← get
  if h : i < s.names.size then return s.names[i]
  throw $ IO.userError s!"[nat2name] {i} > {s.names.size}"

private def parseHints (s : String) : ParseM ReducibilityHints := do
  match s with
  | "A" => pure ReducibilityHints.abbrev
  | "O" => pure ReducibilityHints.opaque
  | _   =>
    match s.splitOn "." with
    | [height, selfOpt] =>
      let height ← parseNat height
      let selfOpt ← parseBool selfOpt
      -- Lean4 does not have reducibility hints, and so we mark these
      -- as abbrev to avoid tryHeuristic
      if !selfOpt then return ReducibilityHints.abbrev
      if h : height < UInt32.size then return ReducibilityHints.regular ⟨⟨height, h⟩⟩
      throw $ IO.userError s!"Reducibility hint too large {height}"
    | _ => throw $ IO.userError s!"failed to parse reducibility hint: {s}"

private def parseMixfixKind (kind : String) : ParseM MixfixKind :=
  match kind with
  | "prefix"    => pure MixfixKind.prefix
  | "postfix"   => pure MixfixKind.postfix
  | "infixl"    => pure MixfixKind.infixl
  | "infixr"    => pure MixfixKind.infixr
  | "singleton" => pure MixfixKind.singleton
  | _           => throw $ IO.userError s!"invalid mixfix kind {kind}"

private def str2expr (s : String)  : ParseM Expr := parseNat s >>= nat2expr
private def str2level (s : String) : ParseM Level := parseNat s >>= nat2level
private def str2name  (s : String) : ParseM Name  := parseNat s >>= nat2name


private def writeName (i : String) (n : Name) : ParseM Unit := do
  let i ← parseNat i
  if i ≠ (← get).names.size then throw $ IO.userError s!"names in wrong order"
  modify $ λ s => { s with names := s.names.push n }

private def writeLevel (i : String) (l : Level) : ParseM Unit := do
  let i ← parseNat i
  if i ≠ (← get).levels.size then throw $ IO.userError s!"levels in wrong order"
  modify $ λ s => { s with levels := s.levels.push l }

private def writeExpr (i : String) (e : Expr) : ParseM Unit := do
  let i ← parseNat i
  if i ≠ (← get).exprs.size then throw $ IO.userError s!"exprs in wrong order"
  modify $ λ s => { s with exprs := s.exprs.push e }

private def parseReducibilityStatus : String → ParseM ReducibilityStatus
| "Reducible"     => pure ReducibilityStatus.reducible
| "Semireducible" => pure ReducibilityStatus.semireducible
| "Irreducible"   => pure ReducibilityStatus.irreducible
| s               => throw $ IO.userError s!"unknown reducibility status {s}"

def emit (envModification : EnvModification) : ParseM Unit := do
  modify fun s => { s with envModifications := s.envModifications.push envModification }

def parseLine (line : String) : ParseM Unit := do
  let tokens := line.splitOn " "
  match tokens with
  | [] => throw $ IO.userError "[parseLine] line has no tokens"
  | (t::_) => if t.isNat then parseTerm tokens else parseMisc tokens

  where
    parseTerm (tokens : List String) : ParseM Unit := do
      match tokens with
      | (i :: "#NS" :: j :: rest)  => writeName  i $ (← str2name j).mkStr (" ".intercalate rest)
      | [i, "#NI", j, k]           => writeName  i $ (← str2name j).mkNum (← parseNat k)
      | [i, "#US", j]              => writeLevel i $ mkLevelSucc (← str2level j)
      | [i, "#UM", j₁, j₂]         => writeLevel i $ mkLevelMax (← str2level j₁) (← str2level j₂)
      | [i, "#UIM", j₁, j₂]        => writeLevel i $ mkLevelIMax (← str2level j₁) (← str2level j₂)
      | [i, "#UP", j]              => writeLevel i $ mkLevelParam (← str2name j)
      | [i, "#EV", j]              => writeExpr  i $ mkBVar (← parseNat j)
      | [i, "#EMVAR"]              => writeExpr  i $ mkMVar ⟨.anonymous⟩
      | [i, "#ELC"]                => writeExpr  i $ mkFVar ⟨.anonymous⟩
      | [i, "#ES", j]              => writeExpr  i $ mkSort (← str2level j)
      | (i :: "#EC" :: j :: us)    => writeExpr  i $ mkConst (← str2name j) (← us.mapM str2level)
      | [i, "#EA", j₁, j₂]         => writeExpr  i $ mkApp (← str2expr j₁) (← str2expr j₂)
      | [i, "#EL", bi, j₁, j₂, j₃] => writeExpr  i $ mkLambda (← str2name j₁) (← parseBinderInfo bi) (← str2expr j₂) (← str2expr j₃)
      | [i, "#EP", bi, j₁, j₂, j₃] => writeExpr  i $ mkForall (← str2name j₁) (← parseBinderInfo bi) (← str2expr j₂) (← str2expr j₃)
      | [i, "#EZ", j₁, j₂, j₃, j₄] => writeExpr  i $ mkLet (← str2name j₁) (← str2expr j₂) (← str2expr j₃) (← str2expr j₄)
      | [i, "#SORRY_MACRO", j]     => writeExpr  i $ mkSorryPlaceholder (← str2expr j)
      | [i, "#QUOTE_MACRO", _r,_j] => writeExpr  i $ .app (.app (.const `expr.sort []) (.const `bool.tt [])) (.const `level.zero []) -- TODO
      | [i, "#PROJ_MACRO", iName, _cName, _pName, idx, arg] =>
        let (iName, idx, arg) := (← str2name iName, ← parseNat idx, ← str2expr arg)
        let some numParams := (← get).ind2params.find? iName
          | throw $ IO.userError "projection type {iName} not found"
        writeExpr i $ mkProj iName (idx - numParams) arg
      | _                          => throw $ IO.userError s!"[parseTerm] unexpected '{tokens}'"

    parseMisc (tokens : List String) : ParseM Unit := do
      match tokens with
      | ("#AX" :: n :: t :: ups) =>
        let (n, t, ups) := (← str2name n, ← str2expr t, ← ups.mapM str2name)
        emit $ EnvModification.decl $ Declaration.axiomDecl {
          name        := n,
          levelParams := ups,
          type        := t,
          isUnsafe    := false,
        }

      | ("#DEF" :: n :: thm :: h :: t :: v :: ups) =>
        let (n, h, t, v, ups) := (← str2name n, ← parseHints h, ← str2expr t, ← str2expr v, ← ups.mapM str2name)
        let thm ← parseNat thm
        -- TODO: why can't I synthesize `thm > 0` any more?
        if Nat.ble 1 thm then
          emit $ EnvModification.decl $ Declaration.thmDecl {
            name        := n,
            levelParams := ups,
            type        := t,
            value       := v
          }
        else
          emit $ EnvModification.decl $ Declaration.defnDecl {
            name        := n,
            levelParams := ups,
            type        := t,
            value       := v,
            safety      := DefinitionSafety.safe, -- TODO: confirm only safe things are being exported
            hints       := h,
          }

      | ("#IND" :: nps :: n :: t :: nis :: rest) =>
        let (nps, n, t, nis) := (← parseNat nps, ← str2name n, ← str2expr t, ← parseNat nis)
        let (is, ups) := rest.splitAt (2 * nis)
        let lparams ← ups.mapM str2name
        let ctors ← parseIntros is
        modify fun s => { s with ind2params := s.ind2params.insert n nps }
        emit $ EnvModification.decl $ Declaration.inductDecl lparams nps [{
          name := n,
          type := t,
          ctors := ctors
          }] false

      | ["#QUOT"]                                => pure ()

      | ("#MIXFIX" :: kind :: n :: prec :: tok)  => emit $ EnvModification.mixfix (← parseMixfixKind kind) (← str2name n) (← parseNat prec) (" ".intercalate tok)
      | ["#PRIVATE", pretty, real]               => emit $ EnvModification.private (← str2name pretty) (← str2name real)
      | ["#PROTECTED", n]                        => emit $ EnvModification.protected (← str2name n)
      | ["#POS_INFO", n, line, col]              => emit $ EnvModification.position (← str2name n) (← parseNat line) (← parseNat col)

      -- TODO: look at the 'deleted' bit
      | ("#ATTR" :: a :: p :: n :: _ :: rest)    => do
        let attrName ← str2name a
        if attrName == "simp" then
          emit $ EnvModification.simp (← str2name n) (← parseNat p)
        else if attrName == "reducibility" then
          match rest with
          | [status] => emit $ EnvModification.reducibility (← str2name n) (← parseReducibilityStatus status)
          | _        => throw $ IO.userError s!"[reducibility] expected name"
        else
          pure ()

      | ["#CLASS", c]                => emit $ EnvModification.class (← str2name c)
      | ["#CLASS_INSTANCE", c, i, p] => emit $ EnvModification.instance (← str2name c) (← str2name i) (← parseNat p)

      | ["#PROJECTION", proj, mk, nParams, i, ii] => do
        emit $ EnvModification.projection {
          projName     := ← str2name proj,
          ctorName     := ← str2name mk,
          nParams      := ← parseNat nParams,
          index        := ← parseNat i,
          fromClass    := ← parseBool ii
        }

      | ("#EXPORT_DECL" :: currNs :: ns :: nsAs :: hadExplicit :: nRenames :: rest) => do
        let rest := rest.toArray
        let nRenames ← parseNat nRenames
        let mut renames := #[]
        for i in [:nRenames] do
          let n1 ← str2name rest[2*i]!
          let n2 ← str2name rest[2*i+1]!
          renames := renames.push (n1, n2)

        let nExcepts ← parseNat rest[2*nRenames]!
        let offset := (2 * nRenames + 1)
        let mut exceptNames := #[]
        for i in [:nExcepts] do
          exceptNames := exceptNames.push $ ← str2name rest[offset + i]!

        let exportDecl : ExportDecl := {
          currNs := (← str2name currNs),
          ns     := (← str2name ns),
          nsAs        := (← str2name nsAs),
          hadExplicit := (← parseNat hadExplicit) > 0,
          renames     := renames,
          exceptNames := exceptNames
        }
        emit $ EnvModification.export exportDecl

      | ("#CLASS_TRACK_ATTR" :: _)               => pure ()
      | ("#AUXREC" :: _)                         => pure ()
      | ("#NEW_NAMESPACE" :: _)                  => pure ()
      | ("#NONCOMPUTABLE" :: _)                  => pure ()
      | ("#NOCONF" :: _)                         => pure ()
      | ("#TOKEN" :: _)                          => pure ()
      | ("#USER_ATTR" :: _)                      => pure ()
      | ("#RELATION" :: _)                       => pure ()
      | ("#UNIFICATION_HINT" :: _)               => pure ()
      | ("#INVERSE" :: _)                        => pure ()
      | _ => throw $ IO.userError s!"[parseLine] unexpected case: '{line}'\n{tokens}"

    parseIntros : List String → ParseM (List Constructor)
      | (n :: t :: is) => do
        let rest ← parseIntros is
        pure $ { name := (← str2name n), type := ← str2expr t } :: rest

      | _              => pure []

    parseBinderInfo : String → ParseM BinderInfo
      | "#BD" => pure BinderInfo.default
      | "#BI" => pure BinderInfo.implicit
      | "#BS" => pure BinderInfo.strictImplicit
      | "#BC" => pure BinderInfo.instImplicit
      | s     => throw $ IO.userError s!"[parseBinderInfo] unexpected: {s}"

def parseTLean (tlean : FilePath) : IO (Array EnvModification) :=
  StateRefT'.run' (s := {}) do
    let lines := (← IO.FS.readFile tlean).splitOn "\n"
    let lines := lines.tail! -- discard imports
    for line in lines do
      unless line.isEmpty do
        parseLine line
    return (← get).envModifications

end Mathport.Binary
