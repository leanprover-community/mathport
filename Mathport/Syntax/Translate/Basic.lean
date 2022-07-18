/-
Copyright (c) 2021 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Daniel Selsam
-/
import Mathport.Bridge.Path
import Mathport.Syntax.Data4
import Mathport.Syntax.Translate.Notation
import Mathport.Syntax.Translate.Attributes
import Mathport.Syntax.Translate.Parser
import Mathlib

abbrev Lean.Syntax.Tactic := TSyntax `tactic
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

namespace Translate

open Std (HashMap)
open AST3

structure NotationData where
  n3 : String
  n4 : Name
  desc : NotationDesc

def NotationData.unpack : NotationData → NotationEntry
  | ⟨n3, _n4, NotationDesc.builtin⟩ => (predefinedNotations.find? n3).get!
  | ⟨_n3, n4, desc⟩ => ⟨n4, desc, desc.toKind n4, false⟩

abbrev NotationEntries := HashMap String NotationData

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
  deriving Inhabited

def NotationEntries.insert (m : NotationEntries) : NotationData → NotationEntries
  | d => HashMap.insert m d.n3 d

initialize synportNotationExtension : SimplePersistentEnvExtension NotationData NotationEntries ←
  registerSimplePersistentEnvExtension {
    name          := `Mathport.Translate.synportNotationExtension
    addEntryFn    := NotationEntries.insert
    addImportedFn := fun es => mkStateFromImportedEntries NotationEntries.insert {} es
  }

def getGlobalNotationEntry? (s : String) : CommandElabM (Option NotationEntry) :=
  return match synportNotationExtension.getState (← getEnv) |>.find? s with
  | none => predefinedNotations.find? s
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
    name          := `Mathport.Translate.synportPrecedenceExtension
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
  pcfg : Path.Config
  notations : Array Notation
  commands : Array Command
  trExpr : Expr → CommandElabM Term
  trCommand : Command → CommandElabM Unit
  transform : Syntax → CommandElabM Syntax
  deriving Inhabited

abbrev M := ReaderT Context $ StateRefT State CommandElabM

def printOutput (out : Format) : M Unit :=
  modify fun s => { s with output := s.output ++ out }

def logComment (comment : Format) : M Unit :=
  printOutput f!"-- {comment}\n"

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

def trCommandUnspanned (e : Command) : M Unit := do (← read).trCommand e
def trCommand := spanning trCommandUnspanned

def renameIdent (n : Name) (choices : Array Name := #[]) : M Name :=
  return Rename.resolveIdent! (← getEnv) n choices
def renameNamespace (n : Name) : M Name := return Rename.renameNamespace (← getEnv) n
def renameAttr (n : Name) : M Name := return Rename.renameAttr n
def renameModule (n : Name) : M Name := do Rename.renameModule (← read).pcfg n
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
    | SourceInfo.synthetic a b =>
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
    | SourceInfo.synthetic a b =>
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

partial def printFirstLineComments : M Unit := do
  if let some comment ← nextCommentIf (·.start.line ≤ 1) then
    printOutput (mkCommentString comment)
    printFirstLineComments

def printRemainingComments : M Unit := do
  for comment in (← get).remainingComments do
    printOutput (mkCommentString comment)
  modify ({ · with remainingComments := [] })

def AST3toData4 : AST3 → M Data4
  | ⟨prel, imp, commands, _, _, _⟩ => do
    let prel := prel.map fun _ => mkNode ``Parser.Module.prelude #[mkAtom "prelude"]
    let imp ← imp.foldlM (init := #[]) fun imp ns =>
      ns.foldlM (init := imp) fun imp n =>
        return imp.push $ mkNode ``Parser.Module.import #[mkAtom "import",
          mkNullNode, mkIdent (← renameModule n.kind)]
    let fmt ← liftCoreM $ PrettyPrinter.format Parser.Module.header.formatter $
      mkNode ``Parser.Module.header #[mkOptionalNode prel, mkNullNode imp]
    printFirstLineComments
    printOutput fmt
    commands.forM fun c => do
      try trCommand c
      catch e =>
        let e := s!"error in {(← getEnv).mainModule}: {← e.toMessageData.toString}"
        println! e
        -- println! (repr c.kind)
        printOutput f!"/- {e}\nLean 3 AST:\n{(repr c.kind).group}-/\n\n"
    printRemainingComments
    pure ⟨(← get).output, HashMap.empty⟩

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
    m (α × Std.PersistentArray TraceElem) := do
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

def push (stx : Syntax) : M Unit := do
  let stx ← try (← read).transform stx catch ex =>
    warn! "failed to transform: {← ex.toMessageData.toString}" | pure stx
  let stx ← insertComments stx
  let fmt ← liftCoreM $ do
    let (stx, parenthesizerErr) ← tryParenthesizeCommand stx
    pure $ parenthesizerErr ++ (←
      try Lean.PrettyPrinter.formatCommand stx
      catch e =>
        pure f!"-- failed to format: {← e.toMessageData.toString}\n{reprint stx}")
  printOutput f!"{fmt}\n\n"

def pushM (stx : M Syntax) : M Unit := stx >>= push

def elabCommand (stx : Syntax) : CommandElabM Unit := do
  -- try dbg_trace "warning: elaborating:\n{← liftCoreM $
  --   Lean.PrettyPrinter.parenthesizeCommand stx >>= Lean.PrettyPrinter.formatCommand}"
  -- catch e => dbg_trace "warning: failed to format: {← e.toMessageData.toString}\nin: {stx}"
  Elab.Command.elabCommand stx

def pushElab (stx : Syntax) : M Unit := elabCommand stx *> push stx

def modifyScope (f : Scope → Scope) : M Unit :=
  modify fun s => { s with current := f s.current }

def pushScope : M Unit :=
  modify fun s => { s with scopes := s.scopes.push s.current }

def popScope : M Unit :=
  modify fun s => match s.scopes.back? with
  | none => s
  | some c => { s with current := c, scopes := s.scopes.pop }

def getNotationEntry? (s : String) : M (Option NotationEntry) := do
  match (← get).current.localNotations.find? s with
  | none => getGlobalNotationEntry? s
  | some d => pure d.unpack

def registerNotationEntry (loc : Bool) (d : NotationData) : M Unit :=
  if loc then modifyScope fun sc => { sc with localNotations := sc.localNotations.insert d }
  else registerGlobalNotationEntry d

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

partial def scientificLitOfDecimal (num den : Nat) : Option (TSyntax scientificLitKind) :=
  findExp num den 0 |>.map fun (m, e) =>
    let str := toString m
    if e == str.length then
      Syntax.mkScientificLit ("0." ++ str)
    else if e < str.length then
      let mStr := str.extract 0 ⟨str.length - e⟩
      let eStr := str.extract ⟨str.length - e⟩ ⟨str.length⟩
      Syntax.mkScientificLit (mStr ++ "." ++ eStr)
    else
      Syntax.mkScientificLit (str ++ "e-" ++ toString e)
where
  findExp n d exp :=
    if d % 10 == 0 then findExp n (d / 10) (exp + 1)
    else if d == 1 then some (n, exp)
    else if d % 2 == 0 then findExp (n * 5) (d / 2) (exp + 1)
    else if d % 5 == 0 then findExp (n * 2) (d / 5) (exp + 1)
    else none

def mkCDot : Term := Unhygienic.run `(·)

structure BinderContext where
  requireType := false

inductive Binder'
  | basic : Syntax.BracketedBinder → Binder'
  | collection : BinderInfo →
    Array (Spanned BinderName) → (nota : Name) → (rhs : Spanned Expr) → Binder'

instance : Coe (TSyntax numLitKind) Syntax.Level where coe s := ⟨s⟩

partial def trLevel : Level → M Syntax.Level
  | Level.«_» => `(level| _)
  | Level.nat n => pure $ Quote.quote n
  | Level.add l n => do `(level| $(← trLevel l.kind) + $(Quote.quote n.kind))
  | Level.imax ls => do `(level| imax $(← ls.mapM fun l => trLevel l.kind)*)
  | Level.max ls => do `(level| max $(← ls.mapM fun l => trLevel l.kind)*)
  | Level.param u => pure $ mkIdent u
  | Level.paren l => trLevel l.kind -- do `(level| ($(← trLevel l.kind)))

partial def trPrio : Expr → M Prio
  | Expr.nat n => pure $ Quote.quote n
  | Expr.paren e => trPrio e.kind -- do `(prio| ($(← trPrio e.kind)))
  | _ => warn! "unsupported: advanced prio syntax" | pure $ quote (999 : Nat)

partial def trPrecExpr : Expr → M Precedence
  | Expr.nat n => pure $ Precedence.nat n
  | Expr.paren e => trPrecExpr e.kind -- do `(prec| ($(← trPrecExpr e.kind)))
  | Expr.const ⟨_, `max⟩ _ _ => pure Precedence.max
  | Expr.const ⟨_, `std.prec.max_plus⟩ _ _ => pure Precedence.maxPlus
  | Expr.notation (Choice.one `«expr + ») #[
      ⟨_, Arg.expr (Expr.ident `max)⟩,
      ⟨_, Arg.expr (Expr.nat 1)⟩
    ] => pure Precedence.maxPlus
  | e => warn! "unsupported: advanced prec syntax {repr e}" | pure $ Precedence.nat 999

def trPrec : AST3.Precedence → M Precedence
  | AST3.Precedence.nat n => pure $ Precedence.nat n
  | AST3.Precedence.expr e => trPrecExpr e.kind

def trIdent_ : BinderName → Syntax.Ident_
  | .ident n => mkIdent n
  | .«_» => Id.run `(Parser.Term.hole| _)

def trIdent_' : BinderName → Syntax.Ident_'
  | .ident n => mkIdent n
  | .«_» => ⟨mkAtom "_"⟩ -- TODO revisit after https://github.com/leanprover/lean4/issues/1275

instance : Coe Syntax.Ident_ Syntax.Term where coe s := ⟨s⟩

def trBinderIdent : BinderName → Syntax.BinderIdent
  | .ident n => Id.run `(binderIdent| $(mkIdent n):ident)
  | .«_» => Id.run `(binderIdent| _)

def trBinderIdentI : BinderName → M (Syntax.BinderIdent)
  | .ident n => do `(binderIdent| $(← mkIdentI n):ident)
  | .«_» => `(binderIdent| _)

def optTy (ty : Option Term) : M (Option (TSyntax ``Parser.Term.typeSpec)) :=
  ty.mapM fun stx => do `(Parser.Term.typeSpec| : $stx)

def trCalcArgs (args : Array (Spanned Expr × Spanned Expr)) : M (Array (TSyntax ``calcStep)) :=
  args.mapM fun (lhs, rhs) =>
    return mkNode ``calcStep #[← trExpr lhs, mkAtom ":=", ← trExpr rhs]

mutual

  partial def trBlock : Block → M (TSyntax ``Parser.Tactic.tacticSeq)
    | ⟨_, none, none, #[]⟩ => do `(Parser.Tactic.tacticSeq| {})
    | ⟨_, none, none, tacs⟩ =>
      return mkNode ``Parser.Tactic.tacticSeq #[mkNode ``Parser.Tactic.tacticSeq1Indented #[
        mkNullNode $ ← tacs.mapM fun tac => return mkGroupNode #[← trTactic tac, mkNullNode]]]
    | ⟨_, _cl, _cfg, _tacs⟩ => warn! "unsupported (TODO): block with cfg"

  partial def trTactic : Spanned Tactic → M Syntax.Tactic := spanningS fun
    | Tactic.block bl => do `(tactic| · ($(← trBlock bl):tacticSeq))
    | Tactic.by tac => do `(tactic| · $(← trTactic tac):tactic)
    | Tactic.«;» tacs => do
      let rec build (i : Nat) (lhs : Syntax.Tactic) : M Syntax.Tactic :=
        if h : i < tacs.size then do
          match ← trTacticOrList tacs[i] with
          | Sum.inl tac => `(tactic| $lhs <;> $(← build (i+1) tac))
          | Sum.inr tacs => build (i+1) (← `(tactic| $lhs <;> [$tacs,*]))
        else pure lhs
      if h : tacs.size > 0 then
        build 1 (← trTactic tacs[0])
      else
        `(tactic| skip)
    | Tactic.«<|>» tacs => do
      `(tactic| first $[| $(← tacs.mapM fun tac => trTactic tac):tactic]*)
    | Tactic.«[]» _tacs => warn! "unsupported (impossible)"
    | Tactic.exact_shortcut ⟨_, Expr.calc args⟩ => do
      `(tactic| calc $(← trCalcArgs args)*)
    | Tactic.exact_shortcut e => do `(tactic| exact $(← trExpr e))
    | Tactic.expr e =>
      match e.unparen with
      | ⟨_, Expr.«`[]» tacs⟩ => trIdTactic ⟨true, none, none, tacs⟩
      | e => do
        let rec head
        | Expr.ident x => x
        | Expr.paren e => head e.kind
        | Expr.app e _ => head e.kind
        | _ => Name.anonymous
        match Rename.resolveIdent? (← getEnv) (head e.kind) with
        | none =>
          -- warn! "unsupported non-interactive tactic {repr e}"
          match ← trExpr e with
          | `(do $[$els]*) => `(tactic| run_tac $[$els:doSeqItem]*)
          | stx => `(tactic| run_tac $stx:term)
        | some n =>
          match (← get).niTactics.find? n with
          | some f => try f e.kind catch e => warn! "in {n}: {← e.toMessageData.toString}"
          | none => warn! "unsupported non-interactive tactic {n}"
    | Tactic.interactive n args => do
      match (← get).tactics.find? n with
      | some f => try f args catch e => warn! "in {n} {repr args}: {← e.toMessageData.toString}"
      | none => warn! "unsupported tactic {repr n} {repr args}"

  partial def trTacticOrList : Spanned Tactic → M (Sum Syntax.Tactic (Array Syntax.Tactic))
    | ⟨_, Tactic.«[]» args⟩ => Sum.inr <$> args.mapM fun arg => trTactic arg
    | tac => Sum.inl <$> trTactic tac

  partial def trIdTactic : Block → M Syntax.Tactic
    | ⟨_, none, none, #[]⟩ => do `(tactic| skip)
    | ⟨_, none, none, #[tac]⟩ => trTactic tac
    | bl => do `(tactic| ($(← trBlock bl):tacticSeq))

end

def mkConvBlock (args : Array Syntax.Conv) : TSyntax ``Parser.Tactic.Conv.convSeq :=
  mkNode ``Parser.Tactic.Conv.convSeq #[mkNode ``Parser.Tactic.Conv.convSeq1Indented #[
    mkNullNode $ args.map fun tac => mkGroupNode #[tac, mkNullNode]]]

mutual

  partial def trConvBlock : Block → M (TSyntax ``Parser.Tactic.Conv.convSeq)
    | ⟨_, none, none, #[]⟩ => return mkConvBlock #[← `(conv| skip)]
    | ⟨_, none, none, tacs⟩ => mkConvBlock <$> tacs.mapM trConv
    | ⟨_, _cl, _cfg, _tacs⟩ => warn! "unsupported (TODO): conv block with cfg"

  partial def trConv : Spanned Tactic → M Syntax.Conv := spanningS fun
    | Tactic.block bl => do `(conv| · $(← trConvBlock bl):convSeq)
    | Tactic.by tac => do `(conv| · $(← trConv tac):conv)
    | Tactic.«;» _tacs => warn! "unsupported (impossible)"
    | Tactic.«<|>» tacs => do
      `(conv| first $[| $(← tacs.mapM trConv):conv]*)
    | Tactic.«[]» _tacs => warn! "unsupported (impossible)"
    | Tactic.exact_shortcut _ => warn! "unsupported (impossible)"
    | Tactic.expr e => do
      match ← trExpr e with
      | `(do $[$els]*) => `(conv| run_conv $[$els:doSeqItem]*)
      | stx => `(conv| run_conv $stx:term)
    | Tactic.interactive n args => do
      match (← get).convs.find? n with
      | some f => try f args catch e => warn! "in {n}: {← e.toMessageData.toString}"
      | none => warn! "unsupported conv tactic {repr n}"

end

def trBinderDefault : Default →
    M (TSyntax [``Parser.Term.binderTactic, ``Parser.Term.binderDefault])
  | Default.«:=» e => do `(Parser.Term.binderDefault| := $(← trExpr e))
  | Default.«.» ⟨m, e⟩ => do
    `(Parser.Term.binderTactic| := by
      $(← trTactic ⟨m, Tactic.expr ⟨m, Expr.ident e⟩⟩):tactic)

def trBinary (n : Name) (lhs rhs : Term) : M Term := do
  match ← getNotationEntry? n.getString! with
  | some ⟨_, _, NotationKind.unary f, _⟩ => pure $ f lhs
  | some ⟨_, _, NotationKind.binary f, _⟩ => pure $ f lhs rhs
  | some ⟨_, _, NotationKind.nary f, _⟩ => pure $ f #[lhs, rhs]
  | _ =>
    warn! "warning: unsupported binary notation {repr n}"
    `($(mkIdent n) $lhs $rhs)

def expandBinderCollection
  (trBinder : Array (Spanned BinderName) → Option (Spanned Expr) → M (Array (TSyntax ks)))
  (bi : BinderInfo) (vars : Array (Spanned BinderName))
  (n : Name) (e : Spanned Expr) : M (Array (TSyntax ks)) := do
  warn! "warning: expanding binder collection {
    bi.bracket true $ spaced repr vars ++ " " ++ n.toString ++ " " ++ repr e}"
  let vars := vars.map $ Spanned.map fun | BinderName.ident v => v | _ => `_x
  let vars1 := vars.map $ Spanned.map BinderName.ident
  let mut out ← trBinder vars1 none
  let H := #[Spanned.dummy BinderName._]
  for v in vars do
    let ty := Expr.notation (Choice.one n) #[v.map $ Arg.expr ∘ Expr.ident, e.map Arg.expr]
    out := out ++ (← trBinder H (some (Spanned.dummy ty)))
  pure out

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

def trExtendedBindersGrouped
  (reg : Array Syntax.SimpleOrBracketedBinder → Term → Term)
  (ext : TSyntax ``binderIdent → TSyntax `binderPred → Term → Term)
  (bc : BinderContext) (bis : Array Binder') (e : Spanned Expr) : M Term := do
  let tr1 : Array Syntax.SimpleOrBracketedBinder × (Term → Term) → Binder' →
      M (Array Syntax.SimpleOrBracketedBinder × (Term → Term))
    | (args, f), Binder'.basic stx => pure (args.push stx, f)
    | (args, f), bic@(Binder'.collection _bi vars n rhs) => do
      match vars, predefinedBinderPreds.find? n.getString! with
      | #[v], some g =>
        let v := trBinderIdent v.kind
        let pred := g (← trExpr rhs)
        pure (#[], fun e => f $ reg args $ ext v pred e)
      | _, _ => pure (args ++ (← expandBinder bc bic), f)
  let (args, f) ← bis.foldlM tr1 (#[], id)
  pure $ f $ reg args (← trExpr e)

def trExplicitBinders : Array (Spanned Binder) → M (TSyntax ``explicitBinders)
  | #[⟨_, Binder.binder _ (some vars) _ ty none⟩] => do
    let ty ← ty.mapM trExpr
    `(explicitBinders| $[$(vars.map (trBinderIdent ·.kind)):binderIdent]* $[: $ty]?)
  | bis => do
    let trBasicBinder (vars : Option (Array (Spanned BinderName)))
        (ty : Option (Spanned Expr)) : M (TSyntax ``bracketedExplicitBinders) := do
      let vars := match vars with
        | some vars => vars.map fun n => trBinderIdent n.kind
        | none => #[Id.run `(binderIdent| _)]
      let ty ← match ty with | none => `(_) | some ty => trExpr ty
      `(bracketedExplicitBinders| ($[$vars]* : $ty))
    let rec trBinder : AST3.Binder → M (Array (TSyntax ``bracketedExplicitBinders))
      | Binder.binder _ vars _ ty none => return #[← trBasicBinder vars ty]
      | Binder.collection bi vars n rhs =>
        expandBinderCollection (fun vars ty => return #[← trBasicBinder vars ty])
          bi vars n rhs
      | Binder.notation _ => warn! "unsupported: (notation) binder"
      | _ => warn! "unsupported (impossible)"
    let bis ← bis.concatMapM (spanning fun bi => trBinder bi)
    `(explicitBinders| $[$bis]*)

def trExplicitBindersExt
  (reg : TSyntax ``explicitBinders → Term → Term)
  (ext : Option (TSyntax ``binderIdent → TSyntax `binderPred → Term → Term))
  (bis : Array (Spanned Binder)) (e : Spanned Expr) : M Term := do
  let reg' (bis) : M (Term → Term) := do
    if bis.isEmpty then pure id else reg <$> trExplicitBinders bis
  match ext with
  | none => return (← reg' bis) (← trExpr e)
  | some ext => do
    let (left, f) ← bis.foldlM (init := (#[], id)) fun (left, f) bi => do
      if let Binder.collection _ #[v] n rhs := bi.kind then
        if let some g := predefinedBinderPreds.find? n.getString! then
          pure (#[], f ∘ (← reg' left) ∘ ext (trBinderIdent v.kind) (g (← trExpr rhs)))
        else pure (left.push bi, f)
      else pure (left.push bi, f)
    pure $ f ((← reg' left) (← trExpr e))

def trExtBinders (args : Array (Spanned Binder)) : M Syntax := do
  let out ← args.concatMapM fun
  | ⟨_, Binder.binder _ vars _ ty _⟩ =>
    trBasicBinder (vars.getD #[Spanned.dummy BinderName._]) ty
  | ⟨_, Binder.collection bi vars n rhs⟩ =>
    if let some g := predefinedBinderPreds.find? n.getString! then
      onVars vars fun v =>
        return #[← `(Mathlib.ExtendedBinder.extBinder|
          $(trBinderIdent v):binderIdent $(g (← trExpr rhs)):binderPred)]
    else
      expandBinderCollection trBasicBinder bi vars n rhs
  | ⟨_, Binder.notation _⟩ => warn! "unsupported: (notation) binder" | pure #[]
  if let #[bi] := out then `(Mathlib.ExtendedBinder.extBinders| $bi:extBinder)
  else `(Mathlib.ExtendedBinder.extBinders| $[($out:extBinder)]*)
where
  onVars {α} (vars) (f : BinderName → M (Array α)) : M (Array α) := do
    if vars.size > 1 then
      warn! "warning: expanding binder group ({spaced repr vars})"
    vars.concatMapM (fun ⟨_, v⟩ => f v)
  trBasicBinder (vars ty) :=
    onVars vars fun v =>
      return #[← `(Mathlib.ExtendedBinder.extBinder|
        $(trBinderIdent v):binderIdent $[: $(← ty.mapM fun ty => trExpr ty)]?)]

instance : Coe Term Syntax.FunBinder where
  coe s := Id.run `(funBinder| $s)

def implicitBinderF := Parser.Term.implicitBinder
def strictImplicitBinderF := Parser.Term.strictImplicitBinder

instance : Coe (TSyntax ``implicitBinderF) Syntax.FunBinder where coe s := ⟨s⟩
instance : Coe (TSyntax ``strictImplicitBinderF) Syntax.FunBinder where coe s := ⟨s⟩
instance : Coe (TSyntax ``Parser.Term.instBinder) Syntax.FunBinder where coe s := ⟨s⟩

partial def trFunBinder : Binder → M (Array Syntax.FunBinder)
  | .«notation» .. => warn! "unsupported notation binder"
  | .binder bi vars bis ty _dflt => do
    let ty ← ty.mapM fun ty => trExprUnspanned (.Pi bis ty)
    let vars' := vars.getD #[Spanned.dummy .«_»] |>.map (trIdent_ ·.2)
    match bi, ty with
    | .implicit, _ => return #[← `(implicitBinderF| { $[$vars']* $[: $ty]? })]
    | .strictImplicit, _ => return #[← `(strictImplicitBinderF| ⦃ $[$vars']* $[: $ty]? ⦄)]
    | .instImplicit, _ =>
      let var ← vars.mapM fun
        | #[⟨_, .ident id⟩] => pure (mkIdent id)
        | _ => warn! "unsupported" | pure (mkIdent "_inst")
      return #[← `(Parser.Term.instBinder| [$[$var :]? $(ty.getD (← `(_)))])]
    | _default, none => pure (vars'.map (·))
    | _default, some ty =>
      if h : vars'.size > 0 then
        let app ← `($(vars'[0]) $(vars'[1:])*)
        return #[← `(($app : $ty))]
      else
        pure #[]
  | .collection bi vars n e =>
    let trBinder vars ty := trFunBinder <| .binder .default (some vars) #[] ty none
    expandBinderCollection trBinder bi vars n e

def trLambdaBinder : LambdaBinder → M (Array Syntax.FunBinder)
  | .reg bi => trFunBinder bi
  | .«⟨⟩» args => return #[← trExprUnspanned (.«⟨⟩» args)]

def trOptType (ty : Option (Spanned Expr)) : M (Option (TSyntax ``Parser.Term.typeSpec)) :=
  ty.mapM trExpr >>= optTy

def trLetDecl : LetDecl → M (TSyntax ``Parser.Term.letDecl)
  | LetDecl.var x bis ty val => do
    let letId := mkNode ``Parser.Term.letIdDecl #[
      trIdent_ x.kind,
      mkNullNode $ ← trBinders {} bis,
      mkOptionalNode $ ← trOptType ty,
      mkAtom ":=", ← trExpr val]
    `(Parser.Term.letDecl| $letId:letIdDecl)
  | LetDecl.pat lhs val => do
    `(Parser.Term.letDecl| $(← trExpr lhs):term := $(← trExpr val))
  | LetDecl.notation _ => warn! "unsupported: let notation := ..."

def trArm : Arm → M (TSyntax ``Parser.Term.matchAltExpr)
  | ⟨lhs, rhs⟩ => do
    `(Parser.Term.matchAltExpr|
      | $(← lhs.mapM fun e => trExpr e),* => $(← trExpr rhs))

def trDoElem : DoElem → M (TSyntax `doElem)
  | DoElem.let decl => do `(doElem| let $(← spanningS trLetDecl decl):letDecl)
  | DoElem.eval e => do `(doElem| $(← trExpr e):term)
  | DoElem.«←» lhs ty rhs els => do
    let rhs ← trExpr rhs
    match lhs.kind.unparen, els with
    | Expr.ident lhs, none =>
      `(doElem| let $(mkIdent lhs):ident $(← trOptType ty)? ← $rhs:term)
    | _, _ =>
      let els ← els.mapM fun e => trExpr e
      `(doElem| let $(← trExpr lhs):term ← $rhs:term $[| $els:term]?)

def trProof : Proof → M Term
  | Proof.«from» _ e => trExpr e
  | Proof.block bl => do `(by $(← trBlock bl):tacticSeq)
  | Proof.by tac => do `(by $(← trTactic tac):tactic)

def trNotation (n : Choice) (args : Array (Spanned Arg)) : M Term := do
  let n ← match n with
  | Choice.one n => pure n
  | Choice.many ns =>
    if let some first := ns[0]? then
      if ns[1:].all (first == ·) then pure first else
        warn! "unsupported: ambiguous notation" | pure first
    else
      warn! "empty choice"
  match ← getNotationEntry? n.getString!, args with
  | some ⟨_, _, NotationKind.const stx, _⟩, #[] => pure stx
  | some ⟨_, _, NotationKind.const _, _⟩, _ => warn! "unsupported (impossible)"
  | some ⟨_, _, NotationKind.unary f, _⟩, #[⟨m, Arg.expr e⟩] => f <$> trExpr ⟨m, e⟩
  | some ⟨_, _, NotationKind.unary _, _⟩, _ => warn! "unsupported (impossible)"
  | some ⟨_, _, NotationKind.binary f, _⟩, #[⟨m₁, Arg.expr e₁⟩, ⟨m₂, Arg.expr e₂⟩] =>
    return f (← trExpr ⟨m₁, e₁⟩) (← trExpr ⟨m₂, e₂⟩)
  | some ⟨_, _, NotationKind.binary _, _⟩, _ => warn! "unsupported (impossible)"
  | some ⟨_, _, NotationKind.nary f, _⟩, args => f <$> args.mapM fun
    | ⟨m, Arg.expr e⟩ => trExpr ⟨m, e⟩
    | ⟨m, Arg.binder bi⟩ => trExtBinders #[⟨m, bi⟩]
    | ⟨_, Arg.binders bis⟩ => trExtBinders bis
    | _ => warn! "unsupported (impossible)"
  | some ⟨_, _, NotationKind.exprs f, _⟩, #[⟨_, Arg.exprs es⟩] => f <$> es.mapM fun e => trExpr e
  | some ⟨_, _, NotationKind.exprs _, _⟩, _ => warn! "unsupported (impossible)"
  | some ⟨_, _, NotationKind.binder f g, _⟩, #[⟨mbi, Arg.binder bi⟩, ⟨me, Arg.expr e⟩] =>
    trExplicitBindersExt f g #[⟨mbi, bi⟩] ⟨me, e⟩
  | some ⟨_, _, NotationKind.binder f g, _⟩, #[⟨_, Arg.binders bis⟩, ⟨me, Arg.expr e⟩] =>
    trExplicitBindersExt f g bis ⟨me, e⟩
  | some ⟨_, _, NotationKind.binder .., _⟩, _ => warn! "unsupported (impossible)"
  | some ⟨_, _, NotationKind.fail, _⟩, args =>
    warn! "warning: unsupported notation {repr n}"
    let args ← args.mapM fun
      | ⟨m, Arg.expr e⟩ => trExpr ⟨m, e⟩
      | _ => warn! "unsupported notation {repr n}"
    `($(mkIdent n) $args*)
  | none, args =>
    warn! "warning: unsupported notation {repr n}"
    let args ← args.mapM fun
      | ⟨m, Arg.expr e⟩ => trExpr ⟨m, e⟩
      | _ => warn! "unsupported notation {repr n}"
    `($(mkIdent n) $args*)

def trInfixFn (n : Choice) (e : Option (Spanned Expr)) : M Term := do
  let n ← match n with
  | Choice.one n => pure n
  | Choice.many ns =>
    if let some first := ns[0]? then
      if ns[1:].all (first == ·) then pure first else
        warn! "unsupported: ambiguous notation" | pure first
    else
      warn! "empty choice"
  let stx ← trBinary n mkCDot $ ← match e with
    | none => pure mkCDot
    | some e => trExpr e
  `(($stx))

partial def trAppArgs [Inhabited α] : (e : Spanned Expr) →
    (m : Spanned Expr → M α) → M (α × Array Term)
  | { kind := Expr.app f x, .. }, m => do
    let (f, args) ← trAppArgs f m
    pure (f, args.push (← trExpr x))
  | e, m => return (← m e, #[])

instance : Coe (TSyntax ``Parser.Term.structInst) Term where
  coe s := Unhygienic.run `($s:structInst)

instance : Coe (TSyntax scientificLitKind) Term where
  coe s := Unhygienic.run `($s:scientific)

def isSimpleBindersOnlyOptType? (bis : Array (Spanned Binder)) : Option (Array (Spanned BinderName) × Option (Spanned Expr)) := do
  if let #[⟨_, .binder .default (some bns) #[] ty none⟩] := bis then
    return (bns, ty)
  (·, none) <$> bis.concatMapM fun
    | ⟨_, .binder .default (some bns) #[] none none⟩ => bns
    | _ => none

def trExpr' : Expr → M Term
  | Expr.«...» => `(_)
  | Expr.sorry => `(sorry)
  | Expr.«_» => `(_)
  | Expr.«()» => `(())
  | Expr.«{}» => `(Parser.Term.structInst| {})
  | Expr.ident n => mkIdentI n
  | Expr.const n none choices => mkIdentI n.kind choices
  | Expr.const n (some #[]) choices => mkIdentI n.kind choices
  | Expr.const n (some l) choices => do
    `($(← mkIdentI n.kind choices):ident.{$[$(← l.mapM fun e => trLevel e.kind):level],*})
  | Expr.nat n => pure $ Quote.quote n
  | Expr.decimal n d => pure (scientificLitOfDecimal n d).get!
  | Expr.string s => pure $ Syntax.mkStrLit s
  | Expr.char c => pure ⟨Syntax.mkCharLit c⟩
  | Expr.paren e => trExpr e -- do `(($(← trExpr e)))
  | Expr.sort ty st u => do
    match ty, if st then some Level._ else u.map Spanned.kind with
    | false, none => `(Sort)
    | false, some u => do `(Sort $(← trLevel u))
    | true, none => `(Type)
    | true, some u => do `(Type $(← trLevel u))
  | Expr.«→» lhs rhs => do `($(← trExpr lhs) → $(← trExpr rhs))
  | Expr.fun true #[⟨_, LambdaBinder.reg (Binder.binder _ none _ (some ty) _)⟩] e => do
    `(fun $(mkIdent `this):ident: $(← trExpr ty) => $(← trExpr e))
  | Expr.fun _ bis e => do
    if let #[⟨_, .reg (.binder .default (some bns) #[] ty none)⟩] := bis then
      let bns := bns.map fun ⟨m, bn⟩ => setInfoT m <| trIdent_ bn
      return ← `(fun $bns* $[: $(← ty.mapM trExpr)]? => $(← trExpr e))
    let bis ← bis.concatMapM (fun bi => trLambdaBinder bi.kind)
    `(fun $bis* => $(← trExpr e))
  | Expr.Pi #[] e => trExpr e
  | Expr.Pi bis e => do
    -- let dArrowHeuristic := !bis.any fun | ⟨_, Binder.binder _ _ _ none _⟩ => true | _ => false
    let dArrowHeuristic := false
    if dArrowHeuristic then trDArrow bis e else
      let bc := {}
      if let some (bns, ty) := isSimpleBindersOnlyOptType? bis then
        let bns := bns.map fun ⟨m, bn⟩ => setInfoT m <| trIdent_ bn
        return ← `(∀ $bns* $[: $(← ty.mapM trExpr)]?, $(← trExpr e))
      trExtendedBindersGrouped
        (fun args e => Id.run `(∀ $args*, $e))
        (fun v pred e => Id.run `(∀ $v:binderIdent $pred:binderPred, $e))
        bc (← trBinders' bc bis) e
  | e@(Expr.app _ _) => do
    let (f, args) ← trAppArgs (Spanned.dummy e) trExpr
    `($f $args*)
  | Expr.show t pr => do
    `(show $(← trExpr t) from $(← trProof pr.kind))
  | Expr.have true h t pr e => do
    let h := h.map (mkIdent ·.kind)
    `(suffices $[$h:ident :]? $(← trExpr t) from $(← trProof pr.kind)
      $(← trExpr e))
  | Expr.have false h t pr e => do
    let t ← match t.kind with | Expr._ => pure none | _ => some <$> trExpr t
    let h := h.map (mkIdent ·.kind)
    `(have $[$h:ident]? $[: $t:term]? := $(← trProof pr.kind)
      $(← trExpr e))
  | Expr.«.» _ e pr => open Lean.TSyntax.Compat in do
    let pr ← match pr.kind with
    | Lean3.Proj.ident e => mkIdentF e
    | Lean3.Proj.nat n => pure $ Syntax.mkLit fieldIdxKind (toString n)
    pure $ mkNode ``Parser.Term.proj #[← trExpr e, mkAtom ".", pr]
  | Expr.if none c t e => do
    `(if $(← trExpr c) then $(← trExpr t) else $(← trExpr e))
  | Expr.if (some h) c t e => do
    `(if $(mkIdent h.kind):ident : $(← trExpr c)
      then $(← trExpr t) else $(← trExpr e))
  | Expr.calc args => do `(calc $(← trCalcArgs args)*)
  | Expr.«@» _ e => do `(@$(← trExpr e))
  | Expr.pattern e => trExpr e
  | Expr.«`()» _ true e => do `(quote $(← trExpr e))
  | Expr.«`()» false false e => do `(pquote $(← trExpr e))
  | Expr.«`()» true false e => do `(ppquote $(← trExpr e))
  | Expr.«%%» e => do `(%%ₓ$(← trExpr e))
  | Expr.«`[]» _tacs => do
    warn! "warning: unsupported (TODO): `[tacs]"
    `(sorry)
  | Expr.«`» false n => pure $ Quote.quote n
  | Expr.«`» true n => do `(``$(← mkIdentI n):ident)
  | Expr.«⟨⟩» es => do `(⟨$(← es.mapM fun e => trExpr e),*⟩)
  | Expr.infix_fn n e => trInfixFn n e
  | Expr.«(,)» es => do
    if h : es.size > 0 then
      `(($(← trExpr es[0]):term, $(← es[1:].toArray.mapM fun e => trExpr e),*))
    else
      warn! "unsupported: empty (,)"
  | Expr.«.()» e => trExpr e
  | Expr.«:» e ty => do `(($(← trExpr e) : $(← trExpr ty)))
  | Expr.hole _es => warn! "unsupported: \{! ... !}"
  | Expr.«#[]» _es => warn! "unsupported: #[...]"
  | Expr.by tac => do `(by $(← trTactic tac):tactic)
  | Expr.begin tacs => do `(by $(← trBlock tacs):tacticSeq)
  | Expr.let bis e => do
    bis.foldrM (init := ← trExpr e) fun bi stx => do
      `(let $(← trLetDecl bi.kind):letDecl
        $stx)
  | Expr.match #[x] _ #[] => do `(nomatch $(← trExpr x))
  | Expr.match xs _ #[] => do `(match $[$(← xs.mapM fun x => trExpr x):term],* with.)
  | Expr.match xs ty eqns => do
    `(match $[$(← xs.mapM fun x => trExpr x):term],* with $[$(← eqns.mapM trArm):matchAlt]*)
  | Expr.do _ els => do let els ← els.mapM fun e => trDoElem e.kind; `(do $[$els:doElem]*)
  | Expr.«{,}» es => do `({$(← es.mapM fun e => trExpr e):term,*})
  | Expr.subtype false x ty p => do
    `({$(mkIdent x.kind) $[: $(← ty.mapM fun e => trExpr e)]? // $(← trExpr p)})
  | Expr.subtype true x none p => do `({$(mkIdent x.kind):ident | $(← trExpr p)})
  | Expr.subtype true x (some ty) p => do
    `({ $(mkIdent x.kind):ident : $(← trExpr ty):term | $(← trExpr p):term })
  | Expr.sep x ty p => do
    `({$(mkIdent x.kind):ident ∈ $(← trExpr ty) | $(← trExpr p)})
  | stx@(Expr.setReplacement e bis) => do
    warn!"unsupported set replacement {repr stx}"
    -- `({$(← trExpr e) | $[$(← trBinders {} bis):bracketedBinder]*})
  | Expr.structInst _ src flds srcs catchall => do
    let srcs := match src with | none => srcs | some src => #[src] ++ srcs
    let srcs := (← srcs.mapM (trExpr ·)).asNonempty
    let flds ← flds.mapM fun (lhs, rhs) => do
      let lhsId ← spanningS mkIdentF lhs
      withSpanS (lhs.meta.map fun m => {m with end_ := (rhs.meta.getD m).end_}) do
      if (match rhs with | ⟨_, Expr.ident rhs⟩ => rhs == lhs.kind | _ => false : Bool) then
        `(Parser.Term.structInstFieldAbbrev| $lhsId:ident)
      else
        `(Parser.Term.structInstField| $lhsId:ident := $(← trExpr rhs))
    -- TODO(Mario): formatter has trouble if you omit the commas
    if catchall then
      `({ $[$srcs,* with]? $[$flds],* .. })
    else
      `({ $[$srcs,* with]? $[$flds],* })
  | Expr.atPat lhs rhs => do `($(mkIdent lhs.kind)@ $(← trExpr rhs))
  | Expr.notation n args => trNotation n args
  | Expr.userNotation n args => do
    match (← get).userNotas.find? n with
    | some f => try f args catch e => warn! "in {n}: {← e.toMessageData.toString}"
    | none => warn! "unsupported user notation {n}"

def mkSimpleAttr (n : Name) (args : Array Syntax := #[]) :=
  mkNode ``Parser.Attr.simple #[mkIdent n, mkNullNode args]

def trDerive (e : Spanned AST3.Expr) : M Name :=
  match e.kind.unparen with
  | Expr.ident n => renameIdent n
  | Expr.const ⟨_, n⟩ _ choices => renameIdent n choices
  | e => warn! "unsupported derive handler {repr e}"

inductive TrAttr
  | del : TSyntax ``Parser.Command.eraseAttr → TrAttr
  | add : Syntax.Attr → TrAttr
  | prio : Expr → TrAttr
  | parsingOnly : TrAttr
  | irreducible : TrAttr
  | derive : Array Name → TrAttr

instance : Coe (TSyntax ``Parser.Attr.simple) Syntax.Attr where
  coe s := Unhygienic.run `(attr| $s:simple)

def trAttr (prio : Option Expr) : Attribute → M (Option TrAttr)
  | Attribute.priority n => pure $ TrAttr.prio n.kind
  | Attribute.del n => do
    let n ← match n with
    | `instance => pure `instance
    | `simp => pure `simp
    | `congr => pure `congr
    | `inline => pure `inline
    | `pattern => pure `matchPattern
    | _ => warn! "warning: unsupported attr -{n}"; return none
    pure $ some $ TrAttr.del (← `(Parser.Command.eraseAttr| -$(← mkIdentI n)))
  | AST3.Attribute.add `parsing_only none => pure TrAttr.parsingOnly
  | AST3.Attribute.add `irreducible none => pure TrAttr.irreducible
  | AST3.Attribute.add n arg => do
    let attr ← match n, arg with
    | `class,         none => `(attr| class)
    | `instance,      none => `(attr| instance)
    | `simp,          none => `(attr| simp)
    | `recursor,      some ⟨_, AttrArg.indices #[]⟩ => warn! "unsupported: @[recursor]"
    | `recursor,      some ⟨_, AttrArg.indices #[⟨_, n⟩]⟩ =>
      `(attr| recursor $(Quote.quote n):num)
    | `intro,         none => `(attr| intro)
    | `intro,         some ⟨_, AttrArg.eager⟩ => `(attr| intro!)
    | `refl,          none => pure $ mkSimpleAttr `refl
    | `symm,          none => pure $ mkSimpleAttr `symm
    | `trans,         none => pure $ mkSimpleAttr `trans
    | `subst,         none => pure $ mkSimpleAttr `subst
    | `congr,         none => pure $ mkSimpleAttr `congr
    | `inline,        none => pure $ mkSimpleAttr `inline
    | `pattern,       none => pure $ mkSimpleAttr `matchPattern
    | `reducible,     none => pure $ mkSimpleAttr `reducible
    | `semireducible, none => pure $ mkSimpleAttr `semireducible
    | `irreducible,   none => pure $ mkSimpleAttr `irreducible
    | `elab_simple,   none => pure $ mkSimpleAttr `elabWithoutExpectedType
    | `vm_override,   some ⟨_, AttrArg.vmOverride n none⟩ =>
      pure $ mkSimpleAttr `implementedBy #[← mkIdentI n.kind]
    | `derive,        some ⟨_, AttrArg.user _ args⟩ =>
      return TrAttr.derive $ ← (← Parser.pExprListOrTExpr.run' args).mapM trDerive
    | _, none => mkSimpleAttr <$> renameAttr n
    | _, some ⟨_, AttrArg.user e args⟩ =>
      match (← get).userAttrs.find? n, args with
      | some f, _ =>
        try f #[Spanned.dummy (AST3.Param.parse e args)]
        catch e => warn! "in {n}: {← e.toMessageData.toString}"
      | none, #[] => mkSimpleAttr <$> renameAttr n
      | none, _ => warn! "unsupported user attr {n}"
    | _, _ =>
      warn! "warning: suppressing unknown attr {n}"
      return none
    pure $ TrAttr.add attr

def trAttrKind : AttributeKind → M Syntax
  | AttributeKind.global => `(Parser.Term.attrKind|)
  | AttributeKind.scoped => `(Parser.Term.attrKind| scoped)
  | AttributeKind.local => `(Parser.Term.attrKind| local)

structure SpecialAttrs where
  prio : Option AST3.Expr := none
  parsingOnly := false
  irreducible := false
  derive : Array Name := #[]

def AttrState := SpecialAttrs × Array Syntax.EraseOrAttrInstance

def trAttrInstance (attr : Attribute) (allowDel := false)
  (kind : AttributeKind := AttributeKind.global) : StateT AttrState M Unit := do
  match ← trAttr (← get).1.prio attr with
  | some (TrAttr.del stx) => do
    unless allowDel do warn! "unsupported (impossible)"
    modify fun s => { s with 2 := s.2.push stx }
  | some (TrAttr.add stx) => do
    let stx := mkNode ``Parser.Term.attrInstance #[← trAttrKind kind, stx]
    modify fun s => { s with 2 := s.2.push stx }
  | some (TrAttr.prio prio) => modify fun s => { s with 1.prio := prio }
  | some TrAttr.parsingOnly => modify fun s => { s with 1.parsingOnly := true }
  | some TrAttr.irreducible => modify fun s => { s with 1.irreducible := true }
  | some (TrAttr.derive ns) => modify fun s => { s with 1.derive := s.1.derive ++ ns }
  | none => pure ()

def trAttributes (attrs : Attributes) (allowDel := false)
  (kind : AttributeKind := AttributeKind.global) : StateT AttrState M Unit :=
  attrs.forM fun attr => trAttrInstance attr.kind allowDel kind

structure Modifiers4 where
  docComment : Option String := none
  attrs : AttrState := ({}, #[])
  vis : Visibility := Visibility.regular
  «noncomputable» : Option Unit := none
  safety : DefinitionSafety := DefinitionSafety.safe

def mkOpt (a : Option α) (f : α → M Syntax) : M Syntax :=
  match a with
  | none => pure mkNullNode
  | some a => return mkNullNode #[← f a]

instance : Coe (TSyntax ``Parser.Command.declModifiersF)
    (TSyntax ``Parser.Command.declModifiers) where
  coe s := ⟨s⟩

def trModifiers (mods : Modifiers) : M (SpecialAttrs × TSyntax ``Parser.Command.declModifiers) :=
  mods.foldlM trModifier {} >>= toSyntax
where
  trModifier (s : Modifiers4) (m : Spanned Modifier) : M Modifiers4 :=
    match m.kind with
    | Modifier.private => match s.vis with
      | Visibility.regular => pure { s with vis := Visibility.private }
      | _ => throw! "unsupported (impossible)"
    | Modifier.protected => match s.vis with
      | Visibility.regular => pure { s with vis := Visibility.protected }
      | _ => throw! "unsupported (impossible)"
    | Modifier.noncomputable => match s.noncomputable with
      | none => pure { s with «noncomputable» := some () }
      | _ => throw! "unsupported (impossible)"
    | Modifier.meta => match s.safety with
      | DefinitionSafety.safe => pure { s with safety := DefinitionSafety.unsafe }
      | _ => throw! "unsupported (impossible)"
    | Modifier.mutual => pure s -- mutual is duplicated elsewhere in the grammar
    | Modifier.attr loc _ attrs => do
      let kind := if loc then AttributeKind.local else AttributeKind.global
      pure { s with attrs := (← trAttributes attrs false kind |>.run ({}, #[])).2 }
    | Modifier.doc doc => match s.docComment with
      | none => pure { s with docComment := some doc }
      | _ => throw! "unsupported (impossible)"
  toSyntax : Modifiers4 → M (SpecialAttrs × TSyntax ``Parser.Command.declModifiers)
  | ⟨doc, (s, attrs), vis, nc, safety⟩ => do
    let doc := doc.map trDocComment
    let attrs : Array (TSyntax ``Parser.Term.attrInstance) :=
      attrs.map fun s => ⟨s⟩ -- HACK HACK HACK ignores @[-attr]
    let attrs ← attrs.asNonempty.mapM fun attrs => `(Parser.Term.attributes| @[$[$attrs],*])
    let vis ← show M (Option (TSyntax [``Parser.Command.private,
        ``Parser.Command.protected])) from match vis with
      | .regular => pure none
      | .private => `(Parser.Command.private| private)
      | .protected => `(Parser.Command.protected| protected)
    let nc ← nc.mapM fun () => `(Parser.Command.noncomputable| noncomputable)
    let part ← match safety with
      | .partial => some <$> `(Parser.Command.partial| partial)
      | _ => pure none
    let uns ← match safety with
      | DefinitionSafety.unsafe => some <$> `(Parser.Command.unsafe| unsafe)
      | _ => pure none
    return (s, ← `(Parser.Command.declModifiersF|
      $[$doc]? $[$attrs]? $[$vis]? $[$nc]? $[$uns]? $[$part]?))

def trOpenCmd (ops : Array Open) : M Unit := do
  let mut simple := #[]
  let pushSimple (s : Array Ident) :=
    unless s.isEmpty do pushElab $ ← `(command| open $[$s]*)
  for o in ops do
    match o with
    | ⟨tgt, none, clauses⟩ =>
      if clauses.isEmpty then
        simple := simple.push (← mkIdentN tgt.kind)
      else
        pushSimple simple; simple := #[]
        let mut explicit := #[]
        let mut renames := #[]
        let mut hides := #[]
        for c in clauses do
          match c.kind with
          | OpenClause.explicit ns => explicit := explicit ++ ns
          | OpenClause.renaming ns => renames := renames ++ ns
          | OpenClause.hiding ns => hides := hides ++ ns
        match explicit.isEmpty, renames.isEmpty, hides.isEmpty with
        | true, true, true => pure ()
        | false, true, true =>
          let ns ← explicit.mapM fun n => mkIdentF n.kind
          pushElab $ ← `(command| open $(← mkIdentN tgt.kind):ident ($ns*))
        | true, false, true =>
          let rs ← renames.mapM fun ⟨a, b⟩ => do
            `(Parser.Command.openRenamingItem|
              $(← mkIdentF a.kind):ident → $(← mkIdentF b.kind):ident)
          pushElab $ ← `(command| open $(← mkIdentN tgt.kind):ident renaming $rs,*)
        | true, true, false =>
          let ns ← hides.mapM fun n => mkIdentF n.kind
          pushElab $ ← `(command| open $(← mkIdentN tgt.kind):ident hiding $ns*)
        | _, _, _ => warn! "unsupported: advanced open style"
    | _ => warn! "unsupported: unusual advanced open style"
  pushSimple simple

def trExportCmd : Open → M Unit
  | ⟨tgt, none, clauses⟩ => do
    let mut args := #[]
    for c in clauses do
      match c.kind with
      | OpenClause.explicit ns =>
        for n in ns do args := args.push (← mkIdentF n.kind)
      | _ => warn! "unsupported: advanced export style"
    pushElab $ ← `(export $(← mkIdentN tgt.kind):ident ($args*))
  | _ => warn! "unsupported: advanced export style"

def trDeclId (n : Name) (us : LevelDecl) : M (TSyntax ``Parser.Command.declId) := do
  let us := us.map $ Array.map fun u => mkIdent u.kind
  let id ← mkIdentI n #[(← get).current.curNamespace ++ n]
  `(Parser.Command.declId| $id:ident $[.{$us,*}]?)

def trDeclSig (bis : Binders) (ty : Option (Spanned Expr)) :
    M (TSyntax ``Parser.Command.declSig) := do
  let bis ← trBinders {} bis
  let ty ← trExpr (ty.getD <| Spanned.dummy Expr.«_»)
  `(Parser.Command.declSig| $[$bis]* : $ty)

def trOptDeclSig (bis : Binders) (ty : Option (Spanned Expr)) :
    M (TSyntax ``Parser.Command.optDeclSig) := do
  let bis ← trBinders {} bis
  let ty ← ty.mapM trExpr
  `(Parser.Command.optDeclSig| $[$bis]* $[: $ty]?)

def trAxiom (mods : Modifiers) (n : Name)
  (us : LevelDecl) (bis : Binders) (ty : Option (Spanned Expr)) : M Unit := do
  let (s, mods) ← trModifiers mods
  unless s.derive.isEmpty do warn! "unsupported: @[derive] axiom"
  pushM `(command| $mods:declModifiers axiom $(← trDeclId n us) $(← trDeclSig bis ty))

def trDecl (dk : DeclKind) (mods : Modifiers) (n : Option (Spanned Name)) (us : LevelDecl)
  (bis : Binders) (ty : Option (Spanned Expr)) (val : DeclVal) : M Syntax.Command := do
  let (s, mods) ← trModifiers mods
  let id ← n.mapM fun n => trDeclId n.kind us
  let val ← match val with
    | DeclVal.expr e => do `(Parser.Command.declVal| := $(← trExprUnspanned e))
    | DeclVal.eqns #[] => `(Parser.Command.declVal| := fun.)
    | DeclVal.eqns arms => do `(Parser.Command.declVal| $[$(← arms.mapM trArm):matchAlt]*)
  if s.irreducible then
    unless dk matches DeclKind.def do warn! "unsupported irreducible non-definition"
    unless s.derive.isEmpty do warn! "unsupported: @[derive, irreducible] def"
    return ← `($mods:declModifiers irreducible_def $id.get! $(← trOptDeclSig bis ty) $val)
  match dk with
  | DeclKind.abbrev => do
    unless s.derive.isEmpty do warn! "unsupported: @[derive] abbrev"
    `($mods:declModifiers abbrev $id.get! $(← trOptDeclSig bis ty) $val)
  | DeclKind.def => do
    let ds := s.derive.map mkIdent |>.asNonempty
    `($mods:declModifiers def $id.get! $(← trOptDeclSig bis ty) $val $[deriving $ds,*]?)
  | DeclKind.example => do
    unless s.derive.isEmpty do warn! "unsupported: @[derive] example"
    `($mods:declModifiers example $(← trDeclSig bis ty) $val)
  | DeclKind.theorem => do
    unless s.derive.isEmpty do warn! "unsupported: @[derive] theorem"
    `($mods:declModifiers theorem $id.get! $(← trDeclSig bis ty) $val)
  | DeclKind.instance => do
    unless s.derive.isEmpty do warn! "unsupported: @[derive] instance"
    let prio ← s.prio.mapM fun prio => do
      `(Parser.Command.namedPrio| (priority := $(← trPrio prio)))
    `($mods:declModifiers instance $[$prio:namedPrio]? $[$id:declId]? $(← trDeclSig bis ty) $val)

def trOptDeriving : Array Name → M (TSyntax ``Parser.Command.optDeriving)
  | #[] => `(Parser.Command.optDeriving|)
  | ds => `(Parser.Command.optDeriving| deriving $[$(ds.map mkIdent):ident],*)

def trInductive (cl : Bool) (mods : Modifiers) (n : Spanned Name) (us : LevelDecl)
  (bis : Binders) (ty : Option (Spanned Expr))
  (nota : Option Notation) (intros : Array (Spanned Intro)) : M Syntax.Command := do
  let (s, mods) ← trModifiers mods
  let id ← trDeclId n.kind us
  let sig ← trOptDeclSig bis ty
  let ctors ← intros.mapM fun ⟨m, ⟨doc, name, ik, bis, ty⟩⟩ => withSpanS m do
    if let some ik := ik then warn! "infer kinds are unsupported in Lean 4: {name.2} {ik}"
    `(Parser.Command.ctor| |
      $[$(doc.map trDocComment):docComment]?
      $(← mkIdentI name.kind):ident
      $(← trOptDeclSig bis ty):optDeclSig)
  let ds ← trOptDeriving s.derive
  match cl with
  | true => `($mods:declModifiers class inductive
    $id:declId $sig:optDeclSig $[$ctors:ctor]* $ds:optDeriving)
  | false => `($mods:declModifiers inductive
    $id:declId $sig:optDeclSig $[$ctors:ctor]* $ds:optDeriving)

def trMutual (decls : Array (Mutual α)) (f : Mutual α → M Syntax.Command) : M Unit := do
  pushM `(mutual $(← decls.mapM f)* end)

def trField : Spanned Field → M (Array Syntax) := spanning fun
  | Field.binder bi ns ik bis ty dflt => do
    let ns ← ns.mapM fun n => mkIdentF n.kind
    if let some ik := ik then warn! "infer kinds are unsupported in Lean 4: {ns} {ik}"
    (#[·]) <$> match bi with
    | BinderInfo.implicit => do
      `(Parser.Command.structImplicitBinder| {$ns* $(← trDeclSig bis ty):declSig})
    | BinderInfo.instImplicit => do
      `(Parser.Command.structInstBinder| [$ns* $(← trDeclSig bis ty):declSig])
    | _ => do
      let sig ← trOptDeclSig bis ty
      let dflt ← dflt.mapM trBinderDefault
      if let #[n] := ns then
        `(Parser.Command.structSimpleBinder| $n:ident $sig:optDeclSig $[$dflt]?)
      else
        `(Parser.Command.structExplicitBinder| ($ns* $sig:optDeclSig $[$dflt]?))
  | Field.notation _ => warn! "unsupported: (notation) in structure"

def trFields (flds : Array (Spanned Field)) : M (TSyntax ``Parser.Command.structFields) := do
  let flds ← flds.concatMapM trField
  pure $ mkNode ``Parser.Command.structFields #[mkNullNode flds]

def trStructure (cl : Bool) (mods : Modifiers) (n : Spanned Name) (us : LevelDecl)
  (bis : Binders) (exts : Array (Spanned Parent)) (ty : Option (Spanned Expr))
  (mk : Option (Spanned Mk)) (flds : Array (Spanned Field)) : M Unit := do
  let (s, mods) ← trModifiers mods
  let id ← trDeclId n.kind us
  let bis ← trBracketedBinders {} bis
  let exts ← exts.mapM fun
    | ⟨_, false, none, ty, #[]⟩ => trExpr ty
    | _ => warn! "unsupported: advanced extends in structure"
  let exts ← exts.asNonempty.mapM fun exts => `(Parser.Command.extends| extends $[$exts],*)
  let ty ← trOptType ty
  let (ctor, flds) ← match mk, flds with
    | none, #[] => pure (none, none)
    | mk, flds => do
      let mk ← mk.mapM fun ⟨_, n, ik⟩ => do
        if let some ik := ik then warn! "infer kinds are unsupported in Lean 4: {n.2} {ik}"
        `(Parser.Command.structCtor| $(← mkIdentF n.kind):ident ::)
      pure (some mk, some (← trFields flds))
  let deriv ← trOptDeriving s.derive
  let decl ←
    if cl then
      `(Parser.Command.structure|
        class $id:declId $[$bis]* $[$exts]? $[$ty]? $[where $[$ctor]? $flds]? $deriv)
    else
      `(Parser.Command.structure|
        structure $id:declId $[$bis]* $[$exts]? $[$ty]? $[where $[$ctor]? $flds]? $deriv)
  pushM `(command| $mods:declModifiers $decl:structure)

partial def mkUnusedName [Monad m] [MonadResolveName m] [MonadEnv m]
  (baseName : Name) : m Name := do
  let ns ← getCurrNamespace
  let env ← getEnv
  return if env.contains (ns ++ baseName) then
    let rec loop (idx : Nat) :=
      let name := baseName.appendIndexAfter idx
      if env.contains (ns ++ name) then loop (idx+1) else name
    loop 1
  else baseName

section

private def mkNAry (lits : Array (Spanned AST3.Literal)) : Option (Array Literal) := do
  let mut i := 0
  let mut out := #[]
  for lit in lits do
    match lit with
    | ⟨_, AST3.Literal.sym tk⟩ => out := out.push (Literal.tk tk.1.kind.toString)
    | ⟨_, AST3.Literal.var _ _⟩ => out := out.push (Literal.arg i); i := i + 1
    | ⟨_, AST3.Literal.binder _⟩ => out := out.push (Literal.arg i); i := i + 1
    | ⟨_, AST3.Literal.binders _⟩ => out := out.push (Literal.arg i); i := i + 1
    | _ => none
  pure out

private def isIdentPrec : AST3.Literal → Bool
  | AST3.Literal.sym _ => true
  | AST3.Literal.var _ none => true
  | AST3.Literal.var _ (some ⟨_, Action.prec _⟩) => true
  | _ => false

private def truncatePrec (prec : Precedence) : Precedence := Id.run do
  -- https://github.com/leanprover-community/mathport/issues/114#issuecomment-1046582957
  if let Precedence.nat n := prec then
    if n > 1024 then
      return Precedence.nat 1024
  return prec

private def trMixfix (kind : TSyntax ``Parser.Term.attrKind)
  (prio : Option (TSyntax ``Parser.Command.namedPrio))
  (m : AST3.MixfixKind) (tk : String) (prec : Option (Spanned AST3.Precedence)) :
  M (NotationDesc × (Option (TSyntax ``Parser.Command.namedName) → Term → Id Syntax.Command)) := do
  let p ← match prec with
  | some p => trPrec p.kind
  | none => pure $ (← getPrecedence? tk m).getD (Precedence.nat 0)
  let p := truncatePrec p
  let p := p.toSyntax
  let s := Syntax.mkStrLit tk
  pure $ match m with
  | MixfixKind.infix =>
    (NotationDesc.infix tk, fun n e =>
      `($kind:attrKind infixl:$p $[$n:namedName]? $[$prio:namedPrio]? $s => $e))
  | MixfixKind.infixl =>
    (NotationDesc.infix tk, fun n e =>
      `($kind:attrKind infixl:$p $[$n:namedName]? $[$prio:namedPrio]? $s => $e))
  | MixfixKind.infixr =>
    (NotationDesc.infix tk, fun n e =>
      `($kind:attrKind infixr:$p $[$n:namedName]? $[$prio:namedPrio]? $s => $e))
  | MixfixKind.prefix =>
    (NotationDesc.prefix tk, fun n e =>
      `($kind:attrKind prefix:$p $[$n:namedName]? $[$prio:namedPrio]? $s => $e))
  | MixfixKind.postfix =>
    (NotationDesc.postfix tk, fun n e =>
      `($kind:attrKind postfix:$p $[$n:namedName]? $[$prio:namedPrio]? $s => $e))

private def trNotation4 (kind : TSyntax ``Parser.Term.attrKind)
    (prio : Option (TSyntax ``Parser.Command.namedPrio)) (p : Option Prec)
    (lits : Array (Spanned AST3.Literal)) :
    M (Option (TSyntax ``Parser.Command.namedName) → Term → Id Syntax.Command) := do
  let lits ← lits.mapM fun
  | ⟨_, AST3.Literal.sym tk⟩ =>
    `(Parser.Command.notationItem| $(Syntax.mkStrLit tk.1.kind.toString):str)
  | ⟨_, AST3.Literal.var x none⟩ =>
    `(Parser.Command.notationItem| $(mkIdent x.kind):ident)
  | ⟨_, AST3.Literal.var x (some ⟨_, Action.prec p⟩)⟩ => do
    `(Parser.Command.notationItem| $(mkIdent x.kind):ident : $((← trPrec p).toSyntax))
  | _ => warn! "unsupported (impossible)"
  pure fun n e =>
    `($kind:attrKind notation$[:$p]? $[$n:namedName]? $[$prio:namedPrio]? $lits* => $e)

open Lean.Parser.Command in
private def trNotation3Item : (lit : AST3.Literal) →
    M (Array (TSyntax ``Parser.Command.notation3Item))
  | .sym tk => pure #[sym tk]
  | .binder .. | .binders .. => return #[← `(notation3Item| (...))]
  | .var x none => pure #[var x]
  | .var x (some ⟨_, .prec _⟩) => pure #[var x]
  | .var x (some ⟨_, .prev⟩) => pure #[var x]
  | .var x (some ⟨_, .scoped _ sc⟩) => return #[← scope x sc]
  | .var x (some ⟨_, .fold r _ sep «rec» (some ini) term⟩) => do
    let f ← fold x r sep «rec» ini
    pure $ match term.map sym with | none => #[f] | some a => #[f, a]
  | lit => warn! "unsupported: advanced notation ({repr lit})"
where
  sym tk := Id.run `(notation3Item| $(Syntax.mkStrLit tk.1.kind.toString):str)
  var x := Id.run `(notation3Item| $(mkIdent x.kind):ident)
  scope x sc := do
    let (p, e) := match sc with
      | none => (`x, Spanned.dummy $ Expr.ident `x)
      | some (p, e) => (p.kind, e)
    `(notation3Item| $(mkIdent x.kind):ident : (scoped $(mkIdent p) => $(← trExpr e)))
  fold x r sep | (y, z, «rec»), ini => do
    let kind ← if r then `(foldKind| foldr) else `(foldKind| foldl)
    `(notation3Item| ($(mkIdent x.kind) $(Syntax.mkStrLit sep.1.kind.toString)* =>
        $kind ($(mkIdent y.kind) $(mkIdent z.kind) => $(← trExpr rec)) $(← trExpr ini)))

private def addSpaceBeforeBinders (lits : Array AST3.Literal) : Array AST3.Literal := Id.run do
  let mut lits := lits
  for i in [1:lits.size] do
    if lits[i]! matches AST3.Literal.binder .. || lits[i]! matches AST3.Literal.binders .. then
      if let AST3.Literal.sym (⟨s, Symbol.quoted tk⟩, prec) := lits[i-1]! then
        if !tk.endsWith " " then
          lits := lits.set! (i-1) <| AST3.Literal.sym (⟨s, Symbol.quoted (tk ++ " ")⟩, prec)
  lits

private def trNotation3 (kind : TSyntax ``Parser.Term.attrKind)
    (prio : Option (TSyntax ``Parser.Command.namedPrio)) (p : Option Prec)
    (lits : Array (Spanned AST3.Literal)) :
    M (Option (TSyntax ``Parser.Command.namedName) → Term → Id Syntax.Command) := do
  let lits := addSpaceBeforeBinders <| lits.map (·.kind)
  let lits ← lits.concatMapM trNotation3Item
  pure fun n e =>
    `($kind:attrKind notation3$[:$p]? $[$n:namedName]? $[$prio:namedPrio]? $lits* => $e)

def trNotationCmd (loc : LocalReserve) (attrs : Attributes) (nota : Notation)
  (ns : Name) : M Unit := do
  let (s, attrs) := (← trAttributes attrs false AttributeKind.global |>.run ({}, #[])).2
  unless s.derive.isEmpty do warn! "unsupported: @[derive] notation"
  unless attrs.isEmpty do warn! "unsupported (impossible)"
  if loc.2 then
    match nota with
    | Notation.mixfix m (tk, some prec) _ =>
      registerPrecedenceEntry tk.kind.toString m (← trPrec prec.kind)
    | _ => warn! "warning: suppressing unsupported reserve notation"
    return
  let kind ← if loc.1 then `(Parser.Term.attrKind| local) else `(Parser.Term.attrKind|)
  let n := nota.name3
  let skip : Bool := match ← getNotationEntry? n with
  | some ⟨_, _, _, skip⟩ => skip
  | none => false
  if skip && !loc.1 then return
  let prio ← s.prio.mapM fun prio => do
    `(Parser.Command.namedPrio| (priority := $(← trPrio prio)))
  let (e, desc, cmd) ← match nota with
  | Notation.mixfix m (tk, prec) (some e) =>
    pure (e, ← trMixfix kind prio m tk.kind.toString prec)
  | Notation.notation lits (some e) =>
    let p := match lits.get? 0 with
    | some ⟨_, AST3.Literal.sym tk⟩ => tk.2
    | some ⟨_, AST3.Literal.var _ _⟩ => match lits.get? 1 with
      | some ⟨_, AST3.Literal.sym tk⟩ => tk.2
      | _ => none
    | _ => none
    let p ← p.mapM fun p => return (← trPrec p.kind).toSyntax
    let desc := match lits with
    | #[⟨_, AST3.Literal.sym tk⟩] => NotationDesc.const tk.1.kind.trim
    | #[⟨_, AST3.Literal.sym left⟩,
        ⟨_, AST3.Literal.var v (some ⟨_, Action.fold _ _ sep _ _ (some term)⟩)⟩] =>
      NotationDesc.exprs left.1.kind.trim sep.1.kind.trim term.1.kind.trim
    | _ => match mkNAry lits with
      | some lits => NotationDesc.nary lits
      | none => NotationDesc.fail
    let cmd ← match lits.all fun lit => isIdentPrec lit.kind with
    | true => trNotation4 kind prio p lits
    | false => trNotation3 kind prio p lits
    pure (e, desc, cmd)
  | _ => warn! "unsupported (impossible)" | default
  let e ← trExpr e
  let n4 ← Elab.Command.withWeakNamespace (ns ++ (← getEnv).mainModule) $ do
    let n4 ← mkUnusedName nota.name4
    let nn ← `(Parser.Command.namedName| (name := $(mkIdent n4)))
    try elabCommand (cmd (some nn) e).1
    catch e => dbg_trace "warning: failed to add syntax {repr n4}: {← e.toMessageData.toString}"
    pure $ (← getCurrNamespace) ++ n4
  printOutput s!"-- mathport name: «{n}»\n"
  if ns == default then push (cmd none e).1
  else pushM `(command| localized [$(← mkIdentR ns)] $(cmd none e))
  registerNotationEntry loc.1 ⟨n, n4, desc⟩

end

def trInductiveCmd : InductiveCmd → M Unit
  | InductiveCmd.reg cl mods n us bis ty nota intros =>
     pushM $ trInductive cl mods n us bis ty nota intros
  | InductiveCmd.mutual cl mods us bis nota inds =>
    trMutual inds fun ⟨attrs, n, ty, intros⟩ => do
      trInductive cl mods n us bis ty nota intros

def trAttributeCmd (loc : Bool) (attrs : Attributes) (ns : Array (Spanned Name))
    (f : Syntax.Command → Syntax.Command) : M Unit := do
  if ns.isEmpty then return ()
  let kind := if loc then AttributeKind.local else AttributeKind.global
  let (s, attrs) := (← trAttributes attrs true kind |>.run ({}, #[])).2
  let ns ← ns.mapM fun n => mkIdentI n.kind
  unless s.derive.isEmpty do
    push $ f $ ← `(deriving instance $[$(s.derive.map mkIdent):ident],* for $ns,*)
  unless attrs.isEmpty do
    push $ f $ ← `(attribute [$attrs,*] $ns*)

def trCommand' : Command → M Unit
  | Command.initQuotient => pushM `(init_quot)
  | Command.mdoc doc =>
    push $ mkNode ``Parser.Command.moduleDoc #[mkAtom "/-!", mkAtom (doc ++ "-/")]
  | Command.«universe» _ _ ns =>
    pushM `(universe $(ns.map fun n => mkIdent n.kind)*)
  | Command.«namespace» n => do
    pushScope; modifyScope fun s => { s with curNamespace := s.curNamespace ++ n.kind }
    pushElab $ ← `(namespace $(← mkIdentN n.kind))
  | Command.«section» n => do
    pushScope; pushElab $ ← `(section $(← n.mapM fun n => mkIdentN n.kind)?)
  | Command.«end» n => do
    popScope; pushElab $ ← `(end $(← n.mapM fun n => mkIdentN n.kind)?)
  | Command.«variable» vk _ _ bis =>
    unless bis.isEmpty do
      let bis ← trBracketedBinders {} bis
      match vk with
      | VariableKind.variable => pushM `(variable $bis*)
      | VariableKind.parameter => pushM `(parameter $bis*)
  | Command.axiom _ mods n us bis ty => trAxiom mods n.kind us bis ty
  | Command.axioms _ mods bis => bis.forM fun
    | ⟨_, Binder.binder _ (some ns) bis (some ty) none⟩ => ns.forM fun
      | ⟨_, BinderName.ident n⟩ => trAxiom mods n none bis ty
      | _ => warn! "unsupported (impossible)"
    | _ => warn! "unsupported (impossible)"
  | Command.decl dk mods n us bis ty val => do
    pushM $ trDecl dk mods n us bis ty val.kind
  | Command.mutualDecl dk mods us bis arms =>
    trMutual arms fun ⟨attrs, n, ty, vals⟩ =>
      trDecl dk mods n us bis ty (DeclVal.eqns vals)
  | Command.inductive ind => trInductiveCmd ind
  | Command.structure cl mods n us bis exts ty m flds =>
    trStructure cl mods n us bis exts ty m flds
  | Command.attribute loc _ attrs ns => trAttributeCmd loc attrs ns id
  | Command.precedence sym prec => warn! "warning: unsupported: precedence command"
  | Command.notation loc attrs n => trNotationCmd loc attrs n default
  | Command.open true ops => ops.forM trExportCmd
  | Command.open false ops => trOpenCmd ops
  | Command.include true ops => unless ops.isEmpty do
      pushM `(include $(ops.map fun n => mkIdent n.kind)*)
  | Command.include false ops => unless ops.isEmpty do
      pushM `(omit $(ops.map fun n => mkIdent n.kind)*)
  | Command.hide ops => unless ops.isEmpty do
      warn! "unsupported: hide command"
      -- pushM `(hide $(ops.map fun n => mkIdent n.kind)*)
  | Command.theory #[⟨_, Modifier.noncomputable⟩] =>
    pushM `(command| noncomputable section)
  | Command.theory #[⟨_, Modifier.doc doc⟩, ⟨_, Modifier.noncomputable⟩] => do
    printOutput s!"/-!{doc}-/\n"
    pushM `(command| noncomputable section)
  | Command.theory _ => warn! "unsupported (impossible)"
  | Command.setOption o val => match o.kind, val.kind with
    | `old_structure_cmd, OptionVal.bool b =>
      modifyScope fun s => { s with oldStructureCmd := b }
    | o, OptionVal.bool true => do
      pushM `(command| set_option $(← mkIdentO o) true)
    | o, OptionVal.bool false => do
      pushM `(command| set_option $(← mkIdentO o) false)
    | o, OptionVal.str s => do
      pushM `(command| set_option $(← mkIdentO o) $(Syntax.mkStrLit s):str)
    | o, OptionVal.nat n => do
      pushM `(command| set_option $(← mkIdentO o) $(Quote.quote n):num)
    | o, OptionVal.decimal _ _ => warn! "unsupported: float-valued option"
  | Command.declareTrace n => do
    let n ← renameIdent n.kind
    pushM `(command| initialize registerTraceClass $(Quote.quote n))
  | Command.addKeyEquivalence a b => warn! "unsupported: add_key_equivalence"
  | Command.runCmd e => do let e ← trExpr e; pushM `(run_cmd $e:term)
  | Command.check e => do pushM `(#check $(← trExpr e))
  | Command.reduce _ e => do pushM `(#reduce $(← trExpr e))
  | Command.eval e => do pushM `(#eval $(← trExpr e))
  | Command.unify e₁ e₂ => warn! "unsupported: #unify"
  | Command.compile n => warn! "unsupported: #compile"
  | Command.help n => warn! "unsupported: #help"
  | Command.print (PrintCmd.str s) => pushM `(#print $(Syntax.mkStrLit s))
  | Command.print (PrintCmd.ident n) => do pushM `(#print $(← mkIdentI n.kind))
  | Command.print (PrintCmd.axioms (some n)) => do pushM `(#print axioms $(← mkIdentI n.kind))
  | Command.print _ => warn! "unsupported: advanced #print"
  | Command.userCommand n mods args => do
    match (← get).userCmds.find? n with
    | some f => try f mods args catch e => warn! "in {n} {repr args}: {← e.toMessageData.toString}"
    | none => warn! "unsupported user command {n}"
