/-
Copyright (c) 2021 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Daniel Selsam
-/
import Mathport.Bridge.Config
import Mathport.Syntax.Data4
import Mathport.Syntax.Translate.Notation
import Mathport.Syntax.Translate.Attributes
import Mathport.Syntax.Translate.Parser

abbrev Lean.Syntax.Conv := TSyntax `conv
abbrev Lean.Syntax.Attr := TSyntax `attr
abbrev Lean.Syntax.BracketedBinder := TSyntax ``Parser.Term.bracketedBinder
abbrev Lean.Syntax.SimpleOrBracketedBinder :=
  TSyntax [`ident, ``Parser.Term.hole, ``Parser.Term.bracketedBinder]
abbrev Lean.Syntax.FunBinder := TSyntax ``Parser.Term.funBinder
abbrev Lean.Syntax.EraseOrAttrInstance :=
  TSyntax [``Parser.Command.eraseAttr, ``Parser.Term.attrInstance]

-- Core has two (incompatible) definitions for `binderIdent`:
-- `Lean.binderIdent` (which is a syntax)
abbrev Lean.Syntax.BinderIdent := TSyntax ``binderIdent
-- `Lean.Parser.Term.binderIdent` (which is a def)
abbrev Lean.Syntax.Ident_ := TSyntax [identKind, ``Parser.Term.hole]
-- Sometimes also written this way, which is of course different:
-- `ident <|> "_"`
abbrev Lean.Syntax.Ident_' := TSyntax [identKind]
  -- TODO: correct type after https://github.com/leanprover/lean4/issues/1275

def Lean.Syntax.getInfo : Syntax → SourceInfo
  | node info .. => info
  | ident info .. => info
  | atom info .. => info
  | missing => SourceInfo.none

def Lean.SourceInfo.getEndPos? (info : SourceInfo) (originalOnly := false) : Option String.Pos :=
  match info, originalOnly with
  | original (endPos := pos) .., _ => some pos
  | synthetic (endPos := pos) .., false => some pos
  | _, _ => none

namespace Mathport

open Lean hiding Expr Expr.app Expr.const Expr.sort Level Level.imax Level.max Level.param Command
open Lean.Elab (Visibility)
open Lean.Elab.Command (CommandElabM liftCoreM)

open Lean.Parser.Term (bracketedBinderF)
instance : Coe Syntax.Ident_ Syntax.SimpleOrBracketedBinder where coe s := ⟨s⟩
instance : Coe (TSyntax ``bracketedBinderF) Syntax.BracketedBinder where coe s := ⟨s⟩

instance : Coe (TSyntax ``Parser.Attr.simple) Syntax.Attr where
  coe s := Unhygienic.run `(attr| $s:simple)

instance : Coe (TSyntax ``Parser.Command.declModifiersF)
    (TSyntax ``Parser.Command.declModifiers) where
  coe s := ⟨s⟩

instance : Coe Term Syntax.FunBinder where
  coe s := Id.run `(Parser.Term.funBinder| $s)

def implicitBinderF := Parser.Term.implicitBinder
def strictImplicitBinderF := Parser.Term.strictImplicitBinder

instance : Coe (TSyntax ``implicitBinderF) Syntax.FunBinder where coe s := ⟨s⟩
instance : Coe (TSyntax ``strictImplicitBinderF) Syntax.FunBinder where coe s := ⟨s⟩
instance : Coe (TSyntax ``Parser.Term.instBinder) Syntax.FunBinder where coe s := ⟨s⟩

instance : Coe (TSyntax ``Parser.Term.structInst) Term where
  coe s := Unhygienic.run `($s:structInst)

instance : Coe (TSyntax scientificLitKind) Term where
  coe s := Unhygienic.run `($s:scientific)

instance : Coe (TSyntax numLitKind) Syntax.Level where coe s := ⟨s⟩

instance : Coe Syntax.Ident_ Syntax.Term where coe s := ⟨s⟩

namespace Translate

open Lean (HashMap)
open AST3

structure NotationData where
  n3 : Name
  n4 : Name
  desc : NotationDesc

def NotationData.unpack : NotationData → NotationEntry
  | ⟨n3, _n4, NotationDesc.builtin⟩ => (predefinedNotations.find? n3).get!
  | ⟨_n3, n4, desc⟩ => ⟨n4, desc, desc.toKind n4, false⟩

abbrev NotationEntries := NameMap NotationData

structure Scope where
  curNamespace : Name := Name.anonymous
  oldStructureCmd : Bool := false
  localNotations : NotationEntries := {}
  deriving Inhabited

structure State where
  output : Format := ""
  current : Scope := {}
  scopes : Array Scope := #[]
  simpSets : NameSet := predefinedSimpSets
  niTactics : NameMap (AST3.Expr → CommandElabM Syntax.Tactic) := {}
  tactics : NameMap (Array (Spanned AST3.Param) → CommandElabM Syntax.Tactic) := {}
  convs : NameMap (Array (Spanned AST3.Param) → CommandElabM Syntax.Conv) := {}
  userNotas : NameMap (Array (Spanned AST3.Param) → CommandElabM Term) := {}
  userAttrs : NameMap (Array (Spanned AST3.Param) → CommandElabM Syntax.Attr) := {}
  userCmds : NameMap (AST3.Modifiers → Array (Spanned AST3.Param) → CommandElabM Unit) := {}
  remainingComments : List Comment := {}
  afterNextCommand : Array Syntax.Command := #[]
  deriving Inhabited

def NotationEntries.insert (m : NotationEntries) : NotationData → NotationEntries
  | d => NameMap.insert m d.n3 d

initialize synportNotationExtension : SimplePersistentEnvExtension NotationData NotationEntries ←
  registerSimplePersistentEnvExtension {
    addEntryFn    := NotationEntries.insert
    addImportedFn := fun es => mkStateFromImportedEntries NotationEntries.insert {} es
  }

def getGlobalNotationEntry? (n : Name) : CommandElabM (Option NotationEntry) :=
  return match synportNotationExtension.getState (← getEnv) |>.find? n with
  | none => predefinedNotations.find? n
  | some d => d.unpack

def registerGlobalNotationEntry (d : NotationData) : CommandElabM Unit :=
  modifyEnv fun env => synportNotationExtension.addEntry env d

-- Note: the PrecedenceExtension may be unnecessary once
-- https://github.com/leanprover-community/lean/pull/599/commits/4354958
-- is propagated through mathlib.

inductive PrecedenceKind
  | «prefix»
  | rest
  deriving Inhabited, BEq, Hashable, Repr

inductive Precedence
  | nat (n : Nat)
  | max
  | maxPlus
  deriving Inhabited, BEq, Hashable, Repr

def PrecedenceKind.ofMixfixKind : MixfixKind → PrecedenceKind
  | MixfixKind.prefix => PrecedenceKind.prefix
  | _ => PrecedenceKind.rest

abbrev PrecedenceEntries := HashMap (String × PrecedenceKind) Precedence

def PrecedenceEntries.insert (m : PrecedenceEntries) :
    String × PrecedenceKind × Precedence → PrecedenceEntries
  | ⟨tk, kind, prec⟩ => HashMap.insert m (tk, kind) prec

initialize synportPrecedenceExtension :
  SimplePersistentEnvExtension (String × PrecedenceKind × Precedence) PrecedenceEntries ←
  registerSimplePersistentEnvExtension {
    addEntryFn    := PrecedenceEntries.insert
    addImportedFn := fun es => mkStateFromImportedEntries PrecedenceEntries.insert {} es
  }

def registerPrecedenceEntry (tk : String) (kind : MixfixKind) (prec : Precedence) :
  CommandElabM Unit := do
  let tk := tk.trim
  let kind := PrecedenceKind.ofMixfixKind kind
  modifyEnv fun env => synportPrecedenceExtension.addEntry env ⟨tk, kind, prec⟩

def getPrecedence? (tk : String) (kind : MixfixKind) : CommandElabM (Option Precedence) :=
  let tk := tk.trim
  let kind := PrecedenceKind.ofMixfixKind kind
  return synportPrecedenceExtension.getState (← getEnv) |>.find? (tk, kind)

def Precedence.toSyntax : Precedence → Syntax.Prec
  | Precedence.nat n => Quote.quote n
  | Precedence.max => Id.run `(prec| arg)
  | Precedence.maxPlus => Id.run `(prec| max)

structure Context where
  config : Config
  notations : Array Notation
  commands : Array Command
  trExpr : Expr → CommandElabM Term
  trTactic : Tactic → CommandElabM Syntax.Tactic
  trCommand : Command → CommandElabM Unit
  transform : Syntax → CommandElabM Syntax
  deriving Inhabited

abbrev M := ReaderT Context $ StateRefT State CommandElabM

def printOutput (out : Format) : M Unit :=
  modify fun s => { s with output := s.output ++ out }

def logComment (comment : Format) : M Unit :=
  printOutput f!"/- {comment} -/\n"

private def checkColGt := Lean.Parser.checkColGt

class Warnable (α) where
  warn : String → α

instance : Warnable Unit where
  warn _ := ()

instance : Warnable String where
  warn s := s

instance : Warnable (TSyntax strLitKind) where
  warn s := quote s

instance : Warnable Nat where
  warn _ := 0

instance : Warnable Syntax.Ident where
  warn s := mkIdent s

instance : Warnable Name where
  warn s := s

instance : Warnable Syntax where
  warn s := mkIdent s

instance : Warnable Syntax.Term where
  warn s := quote s

instance : Warnable Syntax.Command where
  warn s := Id.run `(#print $(quote s):str)

instance : Warnable Syntax.Tactic where
  warn s := Id.run `(tactic| trace $(quote s))

instance : Warnable Syntax.Attr where
  warn s := Id.run `(attr| $(mkIdent s):ident)

instance : Warnable Syntax.Conv where
  warn _ := Id.run `(conv| skip)

instance : Warnable (TSyntax numLitKind) where
  warn _ := ⟨Id.run `(Parser.numLit| 00)⟩

instance : Warnable Syntax.Prio where
  warn _ := Id.run `(prio| 00)

instance : Warnable Syntax.Prec where
  warn _ := Id.run `(prec| 00)

instance : Warnable (TSyntax ``Parser.Tactic.tacticSeq) where
  warn s := Id.run `(Parser.Tactic.tacticSeq| trace $(quote s))

instance : Warnable (TSyntax ``Parser.Tactic.Conv.convSeq) where
  warn _ := Id.run `(Parser.Tactic.Conv.convSeq| skip)

instance : Warnable (TSyntax ``Parser.Term.letDecl) where
  warn s := Id.run `(Parser.Term.letDecl| error := $(Warnable.warn s))

instance : Warnable (TSyntax ``Parser.Command.notationItem) where
  warn s := Id.run `(Parser.Command.notationItem| $(quote s):str)

instance : Warnable Syntax.SimpleOrBracketedBinder where
  warn s := mkIdent s

instance : Warnable Syntax.BracketedBinder where
  warn s := Id.run `(Parser.Term.bracketedBinderF| ($(mkIdent s)))

instance : Warnable (Option α) where
  warn _ := none

instance : Warnable (Array α) where
  warn _ := #[]

open Lean Elab in
elab:max "warn!" interpStr:interpolatedStr(term) or:((checkColGt "|" term)?) : term <= ty => do
  let head := Syntax.mkStrLit $ mkErrorStringWithPos (← getFileName) (← getRefPosition) ""
  let str ← Elab.liftMacroM <| interpStr.expandInterpolatedStr (← `(String)) (← `(toString))
  let or ←
    if or.1.isNone then
      `(pure (Warnable.warn str))
    else
      pure ⟨or.1.getArg 1⟩
  (Term.elabTerm · ty) <|<- `(do
    let str : String := $head ++ $str
    logComment str
    $or:term)

def positionToStringPos (pos : Position) : String.Pos :=
  ⟨10000 * pos.line + pos.column⟩ -- moderately hacky

def stringPosToLine (pos : String.Pos) : Nat :=
  pos.byteIdx / 10000 -- slightly more hacky

def withSpan (m : Option Meta) (k : M α) : M α :=
  match m with
  | none => k
  | some { start, end_, .. } =>
    let sourceInfo := SourceInfo.synthetic (positionToStringPos start) (positionToStringPos end_)
    withRef (Syntax.atom sourceInfo "") k

def setInfo (meta : Option Meta) (stx : Syntax) : Syntax :=
  match stx.getInfo, meta with
  | SourceInfo.none, some { start, end_, .. } =>
    stx.setInfo (SourceInfo.synthetic (positionToStringPos start) (positionToStringPos end_))
  | _, _ => stx

def setInfoT (meta : Option Meta) (stx : TSyntax ks) : TSyntax ks :=
  ⟨setInfo meta stx⟩

def withSpanS (m : Option Meta) (k : M (TSyntax ks)) : M (TSyntax ks) :=
  return setInfoT m (← withSpan m do k)

def spanning (k : β → M α) (x : Spanned β) : M α := withSpan x.meta do k x.kind
def spanningS (k : β → M (TSyntax ks)) (x : Spanned β) : M (TSyntax ks) :=
  withSpanS x.meta do k x.kind

def trExprUnspanned (e : Expr) : M Term := do (← read).trExpr e
def trExpr := spanningS trExprUnspanned

def trTacticUnspanned (e : Tactic) : M Syntax.Tactic := do (← read).trTactic e
def trTacticRaw := spanningS trTacticUnspanned

def trCommandUnspanned (e : Command) : M Unit := do (← read).trCommand e
def trCommand := spanning trCommandUnspanned

def renameIdentCore (n : Name) (choices : Array Name := #[]) : M ((String × Name) × Name) :=
  return Rename.resolveIdentCore! (← getEnv) n true choices
def renameIdent (n : Name) (choices : Array Name := #[]) : M Name :=
  return Rename.resolveIdent! (← getEnv) n true choices
def renameNamespace (n : Name) : M Name := return Rename.renameNamespace (← getEnv) n
def renameAttr (n : Name) : M Name := return Rename.renameAttr n
def renameModule (n : Name) : M Name := do Rename.renameModule (← read).config.pathConfig n
def renameField (n : Name) : M Name := return Rename.renameField? (← getEnv) n |>.getD n
def renameOption (n : Name) : M Name := warn! "warning: unsupported option {n}" | pure n

def mkIdentR (n : Name) : M Ident :=
  return ⟨(mkIdent n).1.setInfo (← MonadRef.mkInfoFromRefPos)⟩

def mkIdentI (n : Name) (choices : Array Name := #[]) : M Ident := do
  mkIdentR (← renameIdent n choices)
def mkIdentA (n : Name) : M Ident := do mkIdentR (← renameAttr n)
def mkIdentN (n : Name) : M Ident := do mkIdentR (← renameNamespace n)
def mkIdentF (n : Name) : M Ident := do mkIdentR (← renameField n)
def mkIdentO (n : Name) : M Ident := do mkIdentR (← renameOption n)

def Parser.ParserM.run' (p : ParserM α) (args : Array (Spanned VMCall)) : M α := do
  match p.run ⟨(← read).commands, args⟩ with
  | Except.ok a => pure a
  | Except.error e => throw! "unsupported: {e}"

def mkCommentString (comment : Comment) : String :=
  if comment.text.contains '\n' then s!"/-{comment.text}-/\n" else s!"--{comment.text}\n"

def addLeadingComment' (comment : Comment) (info : SourceInfo) : SourceInfo :=
  let commentText := mkCommentString comment
  match info with
    | SourceInfo.none =>
      SourceInfo.original commentText.toSubstring
        (positionToStringPos comment.start)
        "".toSubstring
        (positionToStringPos comment.end)
    | SourceInfo.synthetic a b _ =>
      SourceInfo.original commentText.toSubstring a "".toSubstring b
    | SourceInfo.original leading a trailing b =>
      SourceInfo.original (commentText ++ leading.toString).toSubstring a trailing b

partial def addLeadingComment (comment : Comment) (stx : Syntax) : Option Syntax :=
  if let Syntax.node i k args := stx then Id.run do
    for h : j in [0:args.size] do
      let j := ⟨j, by exact h.2⟩
      if let some a' := addLeadingComment comment args[j] then
        return Syntax.node i k (args.set j a')
    pure none
  else
    stx.setInfo (addLeadingComment' comment stx.getInfo)

def addTrailingComment' (comment : Comment) (info : SourceInfo) : SourceInfo :=
  let commentText := mkCommentString comment
  match info with
    | SourceInfo.none =>
      SourceInfo.original "".toSubstring
        (positionToStringPos comment.start)
        commentText.toSubstring
        (positionToStringPos comment.end)
    | SourceInfo.synthetic a b _ =>
      SourceInfo.original "".toSubstring a commentText.toSubstring b
    | SourceInfo.original leading a trailing b =>
      SourceInfo.original leading a (trailing.toString ++ commentText).toSubstring b

partial def addTrailingComment (comment : Comment) (stx : Syntax) : Option Syntax :=
  if let Syntax.node i k args := stx then Id.run do
    for h : j in [0:args.size] do
      let j := ⟨args.size - j - 1, Nat.sub_lt (m := j+1) (by exact lt_of_le_of_lt h.1 h.2) j.succ_pos⟩
      if let some a' := addTrailingComment comment args[j] then
        return Syntax.node i k (args.set j a')
    pure none
  else
    stx.setInfo (addTrailingComment' comment stx.getInfo)

def nextCommentIf (p : Comment → Bool) : M (Option Comment) := do
  let firstComment :: remainingComments := (← get).remainingComments | return none
  unless p firstComment do return none
  modify ({ · with remainingComments })
  return firstComment

def pushFrontComment (comment : Comment) : M Unit :=
  modify fun s => { s with remainingComments := comment :: s.remainingComments }

partial def insertComments (stx : Syntax) : M Syntax := do
  if let some headPos := stx.getInfo.getPos? then
    if let some comment ← nextCommentIf (positionToStringPos ·.«end» ≤ headPos) then
      let stx ← insertComments stx
      if let some stx := addLeadingComment comment stx then
        return stx
      else
        pushFrontComment comment
        return stx
  match stx with
    | Syntax.node .. => pure <| stx.setArgs (← stx.getArgs.mapM insertComments)
    | _ => pure stx

partial def printFirstLineComments (extraComments : Option String) : M Unit := do
  if let some comment ← nextCommentIf (·.start.line ≤ 1) then
    let comment := match extraComments with
    | some extra => { comment with text := comment.text ++ "\n" ++ extra }
    | none => comment
    printOutput (mkCommentString comment)
    printFirstLineComments none

def printRemainingComments : M Unit := do
  for comment in (← get).remainingComments do
    printOutput (mkCommentString comment)
  modify ({ · with remainingComments := [] })

partial def reprintCore : Syntax → Option Format
  | Syntax.missing => none
  | Syntax.atom _ val => val.trim
  | Syntax.ident _ rawVal _ _ => rawVal.toString
  | Syntax.node _ _ args =>
    match args.toList.filterMap reprintCore with
    | [] => none
    | [arg] => arg
    | args => Format.group <| Format.nest 2 <| Format.line.joinSep args

def reprint (stx : Syntax) : Format :=
  reprintCore stx |>.getD ""

def captureTraces [Monad m] [MonadTrace m] [MonadFinally m] (k : m α) :
    m (α × Lean.PersistentArray TraceElem) := do
  let old ← getTraces
  try
    modifyTraces fun _ => {}
    pure (← k, ← getTraces)
  finally
    modifyTraces fun _ => old

private def tryParenthesizeCommand (stx : Syntax) : CoreM <| Syntax × Format := do
  try
    pure (← Lean.PrettyPrinter.parenthesizeCommand stx, f!"")
  catch e =>
    let (_, traces) ← captureTraces do
      withOptions (·.setBool `trace.PrettyPrinter.parenthesize true) do
        try Lean.PrettyPrinter.parenthesizeCommand stx catch _ => pure stx
    let traces ← traces.toList.mapM (·.msg.format)
    pure (stx,
      f!"/- failed to parenthesize: {← e.toMessageData.toString}\n{Format.joinSep traces "\n"}-/")

def commandToFmt (stx : Syntax.Command) : M Format := do
  let stx ← try (← read).transform stx catch ex =>
    warn! "failed to transform: {← ex.toMessageData.toString}" | pure stx
  let stx ← insertComments stx
  liftCoreM $ do
    let (stx, parenthesizerErr) ← tryParenthesizeCommand stx
    pure $ parenthesizerErr ++ (←
      try Lean.PrettyPrinter.formatCommand stx
      catch e =>
        pure f!"-- failed to format: {← e.toMessageData.toString}\n{reprint stx}")

def push (stx : Syntax.Command) : M Unit := do
  if (← get).afterNextCommand.isEmpty then
    printOutput f!"{← commandToFmt stx}\n\n"
  else
    printOutput f!"{← commandToFmt stx}\n"
    for stx in ← modifyGet fun s => (s.afterNextCommand, { s with afterNextCommand := #[] }) do
      printOutput f!"{← commandToFmt stx}\n"
    printOutput f!"\n"

def stripLastNewline : Format → Format
  | .append f₁ f₂ => .append f₁ (stripLastNewline f₂)
  | .text s => .text <|
      let p := s.prev s.endPos; if s.get p == '\n' then s.extract 0 p else s
  | f => f

def pushM (stx : M Syntax.Command) : M Unit := stx >>= push

def pushAlign (n3 n4 : Name) : M Unit := do
  let stx ← `(command| #align $(mkIdent n3) $(mkIdent n4))
  modify fun s => { s with afterNextCommand := s.afterNextCommand.push stx }

def withReplacement (name : Option Name) (x : M Unit) : M Unit :=
  match name with
  | none => x
  | some n => do
    match (← read).config.replacementStyle with
    | .skip => modify fun s => { s with afterNextCommand := #[] }
    | .comment =>
      printOutput f!"#print {n} /-\n"
      x
      modify fun s => { s with output := stripLastNewline s.output ++ "-/\n\n" }
    | .keep => x

def getNotationEntry? (n : Name) : M (Option NotationEntry) := do
  match (← get).current.localNotations.find? n with
  | none => getGlobalNotationEntry? n
  | some d => pure d.unpack

def mkOptionalNode' (x : Option α) (f : α → Array Syntax) : Syntax :=
  mkNullNode $ match x with
  | none => #[]
  | some a => f a

def mkOptionalNodeM [Monad m] (x : Option α) (f : α → m (Array Syntax)) : m Syntax := do
  @mkNullNode <$> match x with
  | none => pure #[]
  | some a => f a

def trDocComment (doc : String) :=
  mkNode ``Parser.Command.docComment #[mkAtom "/--", mkAtom (doc.trimLeft ++ "-/")]

structure BinderContext where
  requireType := false

inductive Binder'
  | basic : Syntax.BracketedBinder → Binder'
  | collection : BinderInfo →
    Array (Spanned BinderName) → (nota : Name) → (rhs : Spanned Expr) → Binder'

partial def trPrio : Expr → M Prio
  | Expr.nat n => pure $ Quote.quote n
  | Expr.paren e => trPrio e.kind -- do `(prio| ($(← trPrio e.kind)))
  | _ => warn! "unsupported: advanced prio syntax" | pure $ quote (999 : Nat)

def trIdent_ : BinderName → Syntax.Ident_
  | .ident n => mkIdent n
  | .«_» => Id.run `(Parser.Term.hole| _)

def trIdent_' : BinderName → Syntax.Ident_'
  | .ident n => mkIdent n
  | .«_» => ⟨mkAtom "_"⟩ -- TODO revisit after https://github.com/leanprover/lean4/issues/1275

def trBinderIdent : BinderName → Syntax.BinderIdent
  | .ident n => Id.run `(binderIdent| $(mkIdent n):ident)
  | .«_» => Id.run `(binderIdent| _)

def trBinderIdentI : BinderName → M (Syntax.BinderIdent)
  | .ident n => do `(binderIdent| $(← mkIdentI n):ident)
  | .«_» => `(binderIdent| _)

def optTy (ty : Option Term) : M (Option (TSyntax ``Parser.Term.typeSpec)) :=
  ty.mapM fun stx => do `(Parser.Term.typeSpec| : $stx)

def trCalcArg : Spanned Expr × Spanned Expr → M (TSyntax ``calcStep)
  | (lhs, rhs) => do `(calcStep| $(← trExpr lhs) := $(← trExpr rhs))

def blockTransform : SyntaxNodeKind := decl_name%

def mkBlockTransform (f : Array Syntax.Tactic → Id Syntax.Tactic)
    (args : Array Syntax.Tactic := #[]) : Syntax.Tactic :=
  ⟨mkNode blockTransform (#[Id.run (f #[])] ++ args)⟩

def fillBlockTransform (block : Syntax.Tactic) (args : Array Syntax.Tactic) : Syntax.Tactic :=
  let args := block.raw.getArgs[1:].toArray ++ args
  let args : Array Syntax :=
    if args.isEmpty then #[Id.run `(tactic| skip)] else mkSepArray args mkNullNode
  -- assumes that the block tactic has the form `syntax "foo" tacticSeq : tactic`
  ⟨block.raw[0].modifyArg 1 (·.modifyArg 0 (·.modifyArg 0 (·.setArgs args)))⟩

partial def processBlockTransforms (tacs : Array Syntax.Tactic) : Array Syntax.Tactic :=
  if let some i := tacs.findIdx? fun stx => stx.raw.getKind == blockTransform then
    let (left, right) := tacs.splitAt (i + 1)
    let right := processBlockTransforms right
    let block := fillBlockTransform left.back right
    left.pop.push block
  else tacs

def processBlockTransform (tac : Syntax.Tactic) : Syntax.Tactic :=
  if tac.raw.getKind == blockTransform then fillBlockTransform tac #[] else tac

def mkSemiSepArray (tacs : Array Syntax.Tactic) : Syntax := Id.run do
  let mut i := 0
  let mut lastLine := none
  let mut r : Array Syntax := #[]
  for a in tacs do
    let thisLine := a.raw.getPos?.map stringPosToLine
    if i > 0 then
      let sameLine := match lastLine with
        | some x => thisLine == some x
        | _ => false
      r := r.push (if sameLine then mkAtom ";" else mkNullNode) |>.push a
    else
      r := r.push a
    i := i + 1
    lastLine := thisLine
  return mkNullNode r

def trTactic (tac : Spanned Tactic) : M (TSyntax `tactic) :=
  processBlockTransform <$> trTacticRaw tac

partial def trBlock : Block → M (TSyntax ``Parser.Tactic.tacticSeq)
  | ⟨_, none, none, #[]⟩ => do `(Parser.Tactic.tacticSeq| {})
  | ⟨_, none, none, tacs⟩ =>
    return mkNode ``Parser.Tactic.tacticSeq #[mkNode ``Parser.Tactic.tacticSeq1Indented #[
      mkSemiSepArray $ processBlockTransforms $ ← tacs.mapM trTacticRaw]]
  | ⟨_, _cl, _cfg, _tacs⟩ => warn! "unsupported (TODO): block with cfg"

partial def trIdTactic : Block → M Syntax.Tactic
  | ⟨_, none, none, #[]⟩ => do `(tactic| skip)
  | ⟨_, none, none, #[tac]⟩ => trTactic tac
  | bl => do `(tactic| ($(← trBlock bl):tacticSeq))

def trBinderDefault : Default →
    M (TSyntax [``Parser.Term.binderTactic, ``Parser.Term.binderDefault])
  | Default.«:=» e => do `(Parser.Term.binderDefault| := $(← trExpr e))
  | Default.«.» ⟨m, e⟩ => do
    `(Parser.Term.binderTactic| := by
      $(← trTactic ⟨m, Tactic.expr ⟨m, Expr.ident e⟩⟩):tactic)

def expandBinderCollection
  (trBinder : Array (Spanned BinderName) → Option (Spanned Expr) → M (Array (TSyntax ks)))
  (bi : BinderInfo) (vars : Array (Spanned BinderName))
  (n : Name) (e : Spanned Expr) : M (Array (TSyntax ks)) := do
  warn! "warning: expanding binder collection {
    bi.bracket true $ spaced repr vars ++ " " ++ n.toString ++ " " ++ repr e}"
  let H := #[Spanned.dummy BinderName._]
  vars.concatMapM fun v => do
    let v := v.map fun | BinderName.ident v => v | _ => `_x
    let ty := Expr.notation (Choice.one n) #[v.map $ Arg.expr ∘ Expr.ident, e.map Arg.expr]
    return (← trBinder #[v.map BinderName.ident] none) ++ (← trBinder H (some (Spanned.dummy ty)))

def trBasicBinder : BinderContext → BinderInfo → Option (Array (Spanned BinderName)) →
    Binders → Option (Spanned Expr) → Option Default → M Syntax.BracketedBinder
  | _, BinderInfo.instImplicit, vars, _, some ty, none => do
    let var ← match vars with
      | none => pure none
      | some #[⟨_, .ident n⟩] => pure $ some $ mkIdent n
      | some #[⟨_, .«_» ..⟩] => pure none
      | some _ => warn! "unsupported (impossible)"
    `(bracketedBinderF| [$[$var :]? $(← trExpr ty)])
  | {requireType, ..}, bi, some vars, bis, ty, dflt => do
    let ty := match requireType || !bis.isEmpty, ty with
      | true, none => some (Spanned.dummy Expr.«_»)
      | _, _ => ty
    let ty ← ty.mapM fun ty => trExprUnspanned (Expr.Pi bis ty)
    let vars := vars.map fun v => trIdent_ v.kind
    match bi with
    | BinderInfo.implicit =>
      `(bracketedBinderF| { $[$vars]* $[: $ty]? })
    | BinderInfo.strictImplicit =>
      `(bracketedBinderF| ⦃ $[$vars]* $[: $ty]? ⦄)
    | _ => do
      let dflt ← dflt.mapM trBinderDefault
      `(bracketedBinderF| ( $[$vars]* $[: $ty]? $[$dflt]? ))
  | _, _, _, _, _, _ => warn! "unsupported (impossible)"

def trBinder' : BinderContext → Spanned Binder → M (Array Binder')
  | bc, ⟨m, Binder.binder bi vars bis ty dflt⟩ =>
    return #[Binder'.basic <|<- withSpanS m do trBasicBinder bc bi vars bis ty dflt]
  | _, ⟨_, Binder.collection bi vars n e⟩ => do
    return #[Binder'.collection bi vars n e]
  | _, ⟨_, Binder.notation _⟩ => warn! "unsupported: (notation) binder"

def trBinders' (bc : BinderContext) (bis : Array (Spanned Binder)) : M (Array Binder') := do
  bis.concatMapM (fun bi => trBinder' bc bi)

def expandBinder : BinderContext → Binder' → M (Array Syntax.BracketedBinder)
  | _, Binder'.basic bi => pure #[bi]
  | bc, Binder'.collection bi vars n rhs =>
    expandBinderCollection
      (fun vars ty => return #[← trBasicBinder bc bi (some vars) #[] ty none])
      bi vars n rhs

def expandBinders (bc : BinderContext) (bis : Array Binder') :
    M (Array Syntax.BracketedBinder) := do
  bis.concatMapM (fun bi => expandBinder bc bi)

def trBinders (bc : BinderContext) (bis : Array (Spanned Binder)) :
    M (Array Syntax.BracketedBinder) := do
  expandBinders bc (← trBinders' bc bis)

def trBracketedBinders (bc : BinderContext) (bis : Array (Spanned Binder)) :
    M (Array Syntax.BracketedBinder) :=
  return (← expandBinders {} (← trBinders' bc bis)).map fun ⟨s⟩ => ⟨s⟩

def trDArrow (bis : Array (Spanned Binder)) (ty : Spanned Expr) : M Term := do
  let bis ← trBracketedBinders { requireType := true } bis
  bis.foldrM (init := ← trExpr ty) fun bi ty =>
    `($bi:bracketedBinder → $ty)

def trOptType (ty : Option (Spanned Expr)) : M (Option (TSyntax ``Parser.Term.typeSpec)) :=
  ty.mapM trExpr >>= optTy

def trArm : Arm → M (TSyntax ``Parser.Term.matchAltExpr)
  | ⟨lhs, rhs⟩ => do
    `(Parser.Term.matchAltExpr|
      | $(← lhs.mapM trExpr),* => $(← trExpr rhs))

def mkSimpleAttr (n : Name) (args : Array Syntax := #[]) : Syntax.Attr :=
  ⟨mkNode ``Parser.Attr.simple #[mkIdent n, mkNullNode args]⟩

def mkOpt (a : Option α) (f : α → M Syntax) : M Syntax :=
  match a with
  | none => pure mkNullNode
  | some a => return mkNullNode #[← f a]

def trAppArgs : (e : Spanned Expr) → (m : Spanned Expr → M α) → M (α × Array Term)
  | { kind := Expr.app f x, .. }, m => do
    let (f, args) ← trAppArgs f m
    pure (f, args.push (← trExpr x))
  | e, m => return (← m e, #[])
