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

open Lean hiding Expr Expr.app Expr.const Expr.sort Level Level.imax Level.max Level.param
open Lean.Elab (Visibility)
open Lean.Elab.Command (CommandElabM liftCoreM)

namespace Translate

open Std (HashMap)
open AST3

structure NotationData where
  n3 : String
  n4 : Name
  desc : NotationDesc

def NotationData.unpack : NotationData → NotationEntry
  | ⟨n3, n4, NotationDesc.builtin⟩ => (predefinedNotations.find? n3).get!
  | ⟨n3, n4, desc⟩ => ⟨n4, desc, desc.toKind n4, false⟩

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
  niTactics : NameMap (AST3.Expr → CommandElabM Syntax) := {}
  tactics : NameMap (Array (Spanned AST3.Param) → CommandElabM Syntax) := {}
  convs : NameMap (Array (Spanned AST3.Param) → CommandElabM Syntax) := {}
  userNotas : NameMap (Array (Spanned AST3.Param) → CommandElabM Syntax) := {}
  userAttrs : NameMap (Array (Spanned AST3.Param) → CommandElabM Syntax) := {}
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

def Precedence.toSyntax : Precedence → Syntax
  | Precedence.nat n => Quote.quote n
  | Precedence.max => Id.run `(prec| arg)
  | Precedence.maxPlus => Id.run `(prec| max)

structure Context where
  pcfg : Path.Config
  notations : Array Notation
  commands : Array Command
  trExpr : Expr → CommandElabM Syntax
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

instance [Inhabited α] : Warnable α where
  warn := default

instance (priority := high) [Monad m] : Warnable <| m Syntax where
  warn s := pure $ Syntax.mkStrLit s

open Lean Elab in
elab:max "warn!" interpStr:interpolatedStr(term) or:(checkColGt "|" term)? : term <= ty => do
  let pos ← Elab.getRefPosition
  let head := Syntax.mkStrLit $ mkErrorStringWithPos (← read).fileName pos ""
  let str ← Elab.liftMacroM <| interpStr.expandInterpolatedStr (← `(String)) (← `(toString))
  let or ← if or.getNumArgs == 2 then pure $ or.getArg 1 else `(Warnable.warn str)
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

def withSpanS (m : Option Meta) (k : M Syntax) : M Syntax :=
  setInfo m <$> withSpan m do k

def spanning (k : β → M α) (x : Spanned β) : M α := withSpan x.meta do k x.kind
def spanningS (k : β → M Syntax) (x : Spanned β) : M Syntax := withSpanS x.meta do k x.kind

def trExprUnspanned (e : Expr) : M Syntax := do (← read).trExpr e
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

def mkIdentR (n : Name) : M Syntax := return (mkIdent n).setInfo (← MonadRef.mkInfoFromRefPos)

def mkIdentI (n : Name) (choices : Array Name := #[]) : M Syntax := do mkIdentR (← renameIdent n choices)
def mkIdentA (n : Name) : M Syntax := do mkIdentR (← renameAttr n)
def mkIdentN (n : Name) : M Syntax := do mkIdentR (← renameNamespace n)
def mkIdentF (n : Name) : M Syntax := do mkIdentR (← renameField n)
def mkIdentO (n : Name) : M Syntax := do mkIdentR (← renameOption n)

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
      SourceInfo.original commentText.toSubstring (positionToStringPos comment.start) "".toSubstring (positionToStringPos comment.end)
    | SourceInfo.synthetic a b =>
      SourceInfo.original commentText.toSubstring a "".toSubstring b
    | SourceInfo.original leading a trailing b =>
      SourceInfo.original (commentText ++ leading.toString).toSubstring a trailing b

partial def addLeadingComment (comment : Comment) (stx : Syntax) : Option Syntax :=
  if let Syntax.node i k args := stx then Id.run do
    for j in [0:args.size] do
      if let some a' := addLeadingComment comment args[j] then
        return Syntax.node i k (args.set! j a')
    pure none
  else
    stx.setInfo (addLeadingComment' comment stx.getInfo)

def addTrailingComment' (comment : Comment) (info : SourceInfo) : SourceInfo :=
  let commentText := mkCommentString comment
  match info with
    | SourceInfo.none =>
      SourceInfo.original "".toSubstring (positionToStringPos comment.start) commentText.toSubstring (positionToStringPos comment.end)
    | SourceInfo.synthetic a b =>
      SourceInfo.original "".toSubstring a commentText.toSubstring b
    | SourceInfo.original leading a trailing b =>
      SourceInfo.original leading a (trailing.toString ++ commentText).toSubstring b

partial def addTrailingComment (comment : Comment) (stx : Syntax) : Option Syntax :=
  if let Syntax.node i k args := stx then Id.run do
    for j in [0:args.size] do
      let j := args.size - j - 1
      if let some a' := addTrailingComment comment args[j] then
        return Syntax.node i k (args.set! j a')
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
  | Syntax.node _ kind args =>
    match args.toList.filterMap reprintCore with
    | [] => none
    | [arg] => arg
    | args => Format.group <| Format.nest 2 <| Format.line.joinSep args

def reprint (stx : Syntax) : Format :=
  reprintCore stx |>.getD ""

def captureTraces [Monad m] [MonadTrace m] [MonadFinally m] (k : m α) : m (α × Std.PersistentArray TraceElem) := do
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

def trDocComment (doc : String) : Syntax :=
  mkNode ``Parser.Command.docComment #[mkAtom "/--", mkAtom (doc.trimLeft ++ "-/")]

partial def scientificLitOfDecimal (num den : Nat) : Option Syntax :=
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

def mkCDot : Syntax := mkNode ``Parser.Term.cdot #[mkAtom "·"]

structure BinderContext where
  -- if true, only allow simple for no type
  allowSimple : Option Bool := none
  requireType := false

inductive Binder'
  | basic : Syntax → Binder'
  | collection : BinderInfo →
    Array (Spanned BinderName) → (nota : Name) → (rhs : Spanned Expr) → Binder'

partial def trLevel : Level → M Syntax
  | Level.«_» => `(level| _)
  | Level.nat n => pure $ Quote.quote n
  | Level.add l n => do `(level| $(← trLevel l.kind) + $(Quote.quote n.kind))
  | Level.imax ls => do `(level| imax $(← ls.mapM fun l => trLevel l.kind)*)
  | Level.max ls => do `(level| max $(← ls.mapM fun l => trLevel l.kind)*)
  | Level.param u => pure $ mkIdent u
  | Level.paren l => trLevel l.kind -- do `(level| ($(← trLevel l.kind)))

partial def trPrio : Expr → M Syntax
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

def trBinderName : BinderName → Syntax
  | BinderName.ident n => mkIdent n
  | BinderName.«_» => mkHole default

def trIdent_ : BinderName → Syntax
  | BinderName.ident n => mkIdent n
  | BinderName.«_» => mkAtom "_"

def trBinderIdent (n : BinderName) : Syntax := mkNode ``binderIdent #[trIdent_ n]

def trBinderIdentI : BinderName → M Syntax
  | BinderName.ident n => return mkNode ``binderIdent #[← mkIdentI n]
  | BinderName.«_» => pure $ mkNode ``binderIdent #[mkAtom "_"]

def optTy (ty : Option Syntax) : M (Option Syntax) :=
  ty.mapM fun stx => do `(Parser.Term.typeSpec| : $stx)

def trCalcArgs (args : Array (Spanned Expr × Spanned Expr)) : M (Array Syntax) :=
  args.mapM fun (lhs, rhs) =>
    return mkNode ``calcStep #[← trExpr lhs, mkAtom ":=", ← trExpr rhs]

mutual

  partial def trBlock : Block → M Syntax
    | ⟨_, none, none, #[]⟩ => do `(Parser.Tactic.tacticSeq| {})
    | ⟨_, none, none, tacs⟩ =>
      return mkNode ``Parser.Tactic.tacticSeq #[mkNode ``Parser.Tactic.tacticSeq1Indented #[
        mkNullNode $ ← tacs.mapM fun tac => return mkGroupNode #[← trTactic tac, mkNullNode]]]
    | ⟨_, cl, cfg, tacs⟩ => warn! "unsupported (TODO): block with cfg"

  partial def trTactic : Spanned Tactic → M Syntax := spanningS fun
    | Tactic.block bl => do `(tactic| · ($(← trBlock bl):tacticSeq))
    | Tactic.by tac => do `(tactic| · $(← trTactic tac):tactic)
    | Tactic.«;» tacs => do
      let rec build (i : Nat) (lhs : Syntax) : M Syntax :=
        if h : i < tacs.size then do
          match ← trTacticOrList (tacs.get ⟨i, h⟩) with
          | Sum.inl tac => `(tactic| $lhs <;> $(← build (i+1) tac))
          | Sum.inr tacs => build (i+1) (← `(tactic| $lhs <;> [$tacs,*]))
        else pure lhs
      build 1 (← trTactic tacs[0])
    | Tactic.«<|>» tacs => do
      `(tactic| first $[| $(← tacs.mapM fun tac => trTactic tac):tactic]*)
    | Tactic.«[]» tacs => warn! "unsupported (impossible)"
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
      | some f => try f args catch e => warn! "in {n}: {← e.toMessageData.toString}"
      | none => warn! "unsupported tactic {repr n}"

  partial def trTacticOrList : Spanned Tactic → M (Sum Syntax (Array Syntax))
    | ⟨_, Tactic.«[]» args⟩ => Sum.inr <$> args.mapM fun arg => trTactic arg
    | tac => Sum.inl <$> trTactic tac

  partial def trIdTactic : Block → M Syntax
    | ⟨_, none, none, #[]⟩ => do `(tactic| skip)
    | ⟨_, none, none, #[tac]⟩ => trTactic tac
    | bl => do `(tactic| ($(← trBlock bl):tacticSeq))

end

def mkConvBlock (args : Array Syntax) : Syntax :=
  mkNode ``Parser.Tactic.Conv.convSeq #[mkNode ``Parser.Tactic.Conv.convSeq1Indented #[
    mkNullNode $ args.map fun tac => mkGroupNode #[tac, mkNullNode]]]

mutual

  partial def trConvBlock : Block → M Syntax
    | ⟨_, none, none, #[]⟩ => return mkConvBlock #[← `(conv| skip)]
    | ⟨_, none, none, tacs⟩ => mkConvBlock <$> tacs.mapM trConv
    | ⟨_, cl, cfg, tacs⟩ => warn! "unsupported (TODO): conv block with cfg"

  partial def trConv : Spanned Tactic → M Syntax := spanningS fun
    | Tactic.block bl => do `(conv| · $(← trConvBlock bl):convSeq)
    | Tactic.by tac => do `(conv| · $(← trConv tac):conv)
    | Tactic.«;» tacs => warn! "unsupported (impossible)"
    | Tactic.«<|>» tacs => do
      `(conv| first $[| $(← tacs.mapM trConv):conv]*)
    | Tactic.«[]» tacs => warn! "unsupported (impossible)"
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

def trBinderDefault : Default → M Syntax
  | Default.«:=» e => do `(Parser.Term.binderDefault| := $(← trExpr e))
  | Default.«.» ⟨m, e⟩ => do
    `(Parser.Term.binderTactic| := by
      $(← trTactic ⟨m, Tactic.expr ⟨m, Expr.ident e⟩⟩):tactic)

def trBinary (n : Name) (lhs rhs : Syntax) : M Syntax := do
  match ← getNotationEntry? n.getString! with
  | some ⟨_, _, NotationKind.unary f, _⟩ => pure $ f lhs
  | some ⟨_, _, NotationKind.binary f, _⟩ => pure $ f lhs rhs
  | some ⟨_, _, NotationKind.nary f, _⟩ => pure $ f #[lhs, rhs]
  | _ =>
    warn! "warning: unsupported binary notation {repr n}"
    pure $ mkNode ``Parser.Term.app #[mkIdent n, mkNullNode #[lhs, rhs]]

def expandBinderCollection
  (trBinder : Array (Spanned BinderName) → Option (Spanned Expr) → M (Array Syntax))
  (bi : BinderInfo) (vars : Array (Spanned BinderName))
  (n : Name) (e : Spanned Expr) : M (Array Syntax) := do
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
    Binders → Option (Spanned Expr) → Option Default → M Syntax
  | _, BinderInfo.instImplicit, vars, _, some ty, none => do
    let var ← match vars with
    | none => pure #[]
    | some #[v] => pure #[trBinderName v.kind, mkAtom ":"]
    | some _ => warn! "unsupported (impossible)"
    pure $ mkNode ``Parser.Term.instBinder
      #[mkAtom "[", mkNullNode var, ← trExpr ty, mkAtom "]"]
  | ⟨allowSimp, req⟩, bi, some vars, bis, ty, dflt => do
    let ty := match req || !bis.isEmpty, ty with
    | true, none => some (Spanned.dummy Expr.«_»)
    | _, _ => ty
    let ty ← ty.mapM fun ty => trExprUnspanned (Expr.Pi bis ty)
    let vars := mkNullNode $ vars.map fun v => trBinderName v.kind
    if let some stx ← trSimple allowSimp bi vars ty dflt then
      return stx
    let ty := mkOptionalNode' ty fun ty => #[mkAtom ":", ty]
    match bi with
    | BinderInfo.implicit =>
      pure $ mkNode ``Parser.Term.implicitBinder #[mkAtom "{", vars, ty, mkAtom "}"]
    | BinderInfo.strictImplicit =>
      pure $ mkNode ``Parser.Term.strictImplicitBinder #[mkAtom "⦃", vars, ty, mkAtom "⦄"]
    | _ => do
      let dflt ← mkOptionalNode <$> dflt.mapM trBinderDefault
      pure $ mkNode ``Parser.Term.explicitBinder #[mkAtom "(", vars, ty, dflt, mkAtom ")"]
  | _, _, _, _, _, _ => warn! "unsupported (impossible)"
where
  trSimple
  | some b, BinderInfo.default, vars, ty, none => do
    if b && ty.isSome then return none
    pure $ mkNode ``Parser.Term.simpleBinder #[vars, mkOptionalNode (← optTy ty)]
  | _, _, _, _, _ => pure none

def trBinder' : BinderContext → Spanned Binder → M (Array Binder')
  | bc, ⟨m, Binder.binder bi vars bis ty dflt⟩ =>
    return #[Binder'.basic <|<- withSpanS m do trBasicBinder bc bi vars bis ty dflt]
  | bc, ⟨_, Binder.collection bi vars n e⟩ => do
    return #[Binder'.collection bi vars n e]
  | _, ⟨_, Binder.notation _⟩ => warn! "unsupported: (notation) binder"

def trBinders' (bc : BinderContext)
  (bis : Array (Spanned Binder)) : M (Array Binder') := do
  bis.concatMapM (fun bi => trBinder' bc bi)

def expandBinder : BinderContext → Binder' → M (Array Syntax)
  | bc, Binder'.basic bi => pure #[bi]
  | bc, Binder'.collection bi vars n rhs =>
    expandBinderCollection
      (fun vars ty => return #[← trBasicBinder bc bi (some vars) #[] ty none])
      bi vars n rhs

def expandBinders (bc : BinderContext) (bis : Array Binder') : M (Array Syntax) := do
  bis.concatMapM (fun bi => expandBinder bc bi)

def trBinders (bc : BinderContext)
  (bis : Array (Spanned Binder)) : M (Array Syntax) := do
  expandBinders bc (← trBinders' bc bis)

def trDArrow (bis : Array (Spanned Binder)) (ty : Spanned Expr) : M Syntax := do
  let bis ← trBinders { requireType := true } bis
  pure $ bis.foldr (init := ← trExpr ty) fun bi ty =>
    mkNode ``Parser.Term.depArrow #[bi, mkAtom "→", ty]

def trExtendedBindersGrouped
  (reg : Array Syntax → Syntax → Syntax) (ext : Syntax → Syntax → Syntax → Syntax)
  (bc : BinderContext) (bis : Array Binder') (e : Spanned Expr) : M Syntax := do
  let tr1 : Array Syntax × (Syntax → Syntax) → Binder' → M (Array Syntax × (Syntax → Syntax))
  | (args, f), Binder'.basic stx => pure (args.push stx, f)
  | (args, f), bic@(Binder'.collection bi vars n rhs) => do
    match vars, predefinedBinderPreds.find? n.getString! with
    | #[v], some g =>
      let v := trBinderName v.kind
      let pred := g (← trExpr rhs)
      pure (#[], fun e => f $ reg args $ ext v pred e)
    | _, _ => pure (args ++ (← expandBinder bc bic), f)
  let (args, f) ← bis.foldlM tr1 (#[], id)
  pure $ f $ reg args (← trExpr e)

def trExplicitBinders : Array (Spanned Binder) → M Syntax
  | #[⟨_, Binder.binder _ (some vars) _ ty none⟩] => do
    let ty ← match ty with | none => pure #[] | some ty => pure #[mkAtom ":", ← trExpr ty]
    pure $ mkNode ``explicitBinders #[mkNode ``unbracketedExplicitBinders #[
      mkNullNode $ vars.map fun n => trBinderIdent n.kind, mkNullNode ty]]
  | bis => do
    let trBasicBinder (vars : Option (Array (Spanned BinderName)))
      (ty : Option (Spanned Expr)) : M Syntax := do
      let vars := match vars with
      | some vars => vars.map fun n => trBinderIdent n.kind
      | none => #[mkNode ``binderIdent #[mkAtom "_"]]
      let ty ← match ty with | none => `(_) | some ty => trExpr ty
      pure $ mkNode ``bracketedExplicitBinders #[
        mkAtom "(", mkNullNode vars, mkAtom ":", ty, mkAtom ")"]
    let rec trBinder : AST3.Binder → M (Array Syntax)
    | Binder.binder _ vars _ ty none => return #[← trBasicBinder vars ty]
    | Binder.collection bi vars n rhs =>
      expandBinderCollection (fun vars ty => return #[← trBasicBinder vars ty])
        bi vars n rhs
    | Binder.notation _ => warn! "unsupported: (notation) binder"
    | _ => warn! "unsupported (impossible)"
    let bis ← bis.concatMapM (spanning fun bi => trBinder bi)
    pure $ mkNode ``explicitBinders #[mkNullNode bis]

def trExplicitBindersExt
  (reg : Syntax → Syntax → Syntax) (ext : Option (Syntax → Syntax → Syntax → Syntax))
  (bis : Array (Spanned Binder)) (e : Spanned Expr) : M Syntax := do
  let reg' (bis) : M (Syntax → Syntax) := do
    if bis.isEmpty then pure id else reg <$> trExplicitBinders bis
  match ext with
  | none => return (← reg' bis) (← trExpr e)
  | some ext => do
    let (left, f) ← bis.foldlM (init := (#[], id)) fun (left, f) bi => do
      if let Binder.collection _ #[v] n rhs := bi.kind then
        if let some g := predefinedBinderPreds.find? n.getString! then
          pure (#[], f ∘ (← reg' left) ∘ ext (trBinderName v.kind) (g (← trExpr rhs)))
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

def trLambdaBinder : LambdaBinder → Array Syntax → M (Array Syntax)
  | LambdaBinder.reg bi, out => do
    let bc := { allowSimple := some false }
    (← trBinder' bc (Spanned.dummy bi)).concatMapM (fun bi => expandBinder bc bi)
  | LambdaBinder.«⟨⟩» args, out => out.push <$> trExprUnspanned (Expr.«⟨⟩» args)

def trOptType (ty : Option (Spanned Expr)) : M (Option Syntax) := ty.mapM trExpr >>= optTy

def trLetDecl : LetDecl → M Syntax
  | LetDecl.var x bis ty val => do
    let letId := mkNode ``Parser.Term.letIdDecl #[
      trBinderName x.kind,
      mkNullNode $ ← trBinders { allowSimple := some true } bis,
      mkOptionalNode $ ← trOptType ty,
      mkAtom ":=", ← trExpr val]
    `(Parser.Term.letDecl| $letId:letIdDecl)
  | LetDecl.pat lhs val => do
    `(Parser.Term.letDecl| $(← trExpr lhs):term := $(← trExpr val))
  | LetDecl.notation n => warn! "unsupported: let notation := ..."

def trArm : Arm → M Syntax
  | ⟨lhs, rhs⟩ => do
    `(Parser.Term.matchAltExpr|
      | $(← lhs.mapM fun e => trExpr e),* => $(← trExpr rhs))

def trDoElem : DoElem → M Syntax
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

def trProof : Proof → M Syntax
  | Proof.«from» _ e => trExpr e
  | Proof.block bl => do `(by $(← trBlock bl):tacticSeq)
  | Proof.by tac => do `(by $(← trTactic tac):tactic)

def trNotation (n : Choice) (args : Array (Spanned Arg)) : M Syntax := do
  let n ← match n with
  | Choice.one n => pure n
  | Choice.many ns =>
    if ns[1:].all (ns[0] == ·) then pure ns[0] else
      warn! "unsupported: ambiguous notation" | pure ns[0]
  match ← getNotationEntry? n.getString!, args with
  | some ⟨_, _, NotationKind.const stx, _⟩, #[] => pure stx
  | some ⟨_, _, NotationKind.const stx, _⟩, _ => warn! "unsupported (impossible)"
  | some ⟨_, _, NotationKind.unary f, _⟩, #[⟨m, Arg.expr e⟩] => f <$> trExpr ⟨m, e⟩
  | some ⟨_, _, NotationKind.unary f, _⟩, _ => warn! "unsupported (impossible)"
  | some ⟨_, _, NotationKind.binary f, _⟩, #[⟨m₁, Arg.expr e₁⟩, ⟨m₂, Arg.expr e₂⟩] =>
    return f (← trExpr ⟨m₁, e₁⟩) (← trExpr ⟨m₂, e₂⟩)
  | some ⟨_, _, NotationKind.binary f, _⟩, _ => warn! "unsupported (impossible)"
  | some ⟨_, _, NotationKind.nary f, _⟩, args => f <$> args.mapM fun
    | ⟨m, Arg.expr e⟩ => trExpr ⟨m, e⟩
    | ⟨m, Arg.binder bi⟩ => trExtBinders #[⟨m, bi⟩]
    | ⟨_, Arg.binders bis⟩ => trExtBinders bis
    | _ => warn! "unsupported (impossible)"
  | some ⟨_, _, NotationKind.exprs f, _⟩, #[⟨_, Arg.exprs es⟩] => f <$> es.mapM fun e => trExpr e
  | some ⟨_, _, NotationKind.exprs f, _⟩, _ => warn! "unsupported (impossible)"
  | some ⟨_, _, NotationKind.binder f g, _⟩, #[⟨mbi, Arg.binder bi⟩, ⟨me, Arg.expr e⟩] =>
    trExplicitBindersExt f g #[⟨mbi, bi⟩] ⟨me, e⟩
  | some ⟨_, _, NotationKind.binder f g, _⟩, #[⟨_, Arg.binders bis⟩, ⟨me, Arg.expr e⟩] =>
    trExplicitBindersExt f g bis ⟨me, e⟩
  | some ⟨_, _, NotationKind.binder .., _⟩, _ => warn! "unsupported (impossible)"
  | some ⟨_, _, NotationKind.fail, _⟩, args =>
    warn! "warning: unsupported notation {repr n}"
    let args ← args.mapM fun | ⟨m, Arg.expr e⟩ => trExpr ⟨m, e⟩ | _ => warn! "unsupported notation {repr n}"
    pure $ mkNode ``Parser.Term.app #[mkIdent n, mkNullNode args]
  | none, args =>
    warn! "warning: unsupported notation {repr n}"
    let args ← args.mapM fun | ⟨m, Arg.expr e⟩ => trExpr ⟨m, e⟩ | _ => warn! "unsupported notation {repr n}"
    pure $ mkNode ``Parser.Term.app #[mkIdent n, mkNullNode args]

def trInfixFn (n : Choice) (e : Option (Spanned Expr)) : M Syntax := do
  let n ← match n with
  | Choice.one n => pure n
  | Choice.many ns =>
    if ns[1:].all (ns[0] == ·) then pure ns[0] else
      warn! "unsupported: ambiguous notation" | pure ns[0]
  let stx ← trBinary n mkCDot $ ← match e with
  | none => pure mkCDot
  | some e => trExpr e
  `(($stx))

partial def trAppArgs [Inhabited α] : (e : Spanned Expr) → (m : Spanned Expr → M α) → M (α × Array Syntax)
  | { kind := Expr.app f x, .. }, m => do let (f, args) ← trAppArgs f m; pure (f, args.push (← trExpr x))
  | e, m => return (← m e, #[])

def trExpr' : Expr → M Syntax
  | Expr.«...» => `(_)
  | Expr.sorry => `(sorry)
  | Expr.«_» => `(_)
  | Expr.«()» => `(())
  | Expr.«{}» => `({})
  | Expr.ident n => mkIdentI n
  | Expr.const n none choices => mkIdentI n.kind choices
  | Expr.const n (some #[]) choices => mkIdentI n.kind choices
  | Expr.const n (some l) choices =>
    return mkNode ``Parser.Term.explicitUniv #[← mkIdentI n.kind choices,
      mkAtom ".{", (mkAtom ",").mkSep $ ← l.mapM fun e => trLevel e.kind, mkAtom "}"]
  | Expr.nat n => pure $ Quote.quote n
  | Expr.decimal n d => pure (scientificLitOfDecimal n d).get!
  | Expr.string s => pure $ Syntax.mkStrLit s
  | Expr.char c => pure $ Syntax.mkCharLit c
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
    let bis ← bis.foldlM (fun out bi => trLambdaBinder bi.kind out) #[]
    `(fun $bis* => $(← trExpr e))
  | Expr.Pi #[] e => trExpr e
  | Expr.Pi bis e => do
    -- let dArrowHeuristic := !bis.any fun | ⟨_, Binder.binder _ _ _ none _⟩ => true | _ => false
    let dArrowHeuristic := false
    if dArrowHeuristic then trDArrow bis e else
      let bc := { allowSimple := some false }
      trExtendedBindersGrouped
        (fun args e => Id.run `(∀ $args*, $e))
        (fun v pred e => Id.run `(∀ $v:ident $pred:binderPred, $e))
        bc (← trBinders' bc bis) e
  | e@(Expr.app _ _) => do
    let (f, args) ← trAppArgs (Spanned.dummy e) trExpr
    pure $ mkNode ``Parser.Term.app #[f, mkNullNode args]
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
  | Expr.«.» _ e pr => do
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
  | Expr.«`[]» tacs => do
    warn! "warning: unsupported (TODO): `[tacs]"
    `(sorry)
  | Expr.«`» false n => pure $ Quote.quote n
  | Expr.«`» true n => do `(``$(← mkIdentI n):ident)
  | Expr.«⟨⟩» es => do `(⟨$(← es.mapM fun e => trExpr e),*⟩)
  | Expr.infix_fn n e => trInfixFn n e
  | Expr.«(,)» es => do
    `(($(← trExpr es[0]):term, $(← es[1:].toArray.mapM fun e => trExpr e),*))
  | Expr.«.()» e => trExpr e
  | Expr.«:» e ty => do `(($(← trExpr e) : $(← trExpr ty)))
  | Expr.hole es => warn! "unsupported: \{! ... !}"
  | Expr.«#[]» es => warn! "unsupported: #[...]"
  | Expr.by tac => do `(by $(← trTactic tac):tactic)
  | Expr.begin tacs => do `(by $(← trBlock tacs):tacticSeq)
  | Expr.let bis e => do
    bis.foldrM (init := ← trExpr e) fun bi stx => do
      `(let $(← trLetDecl bi.kind):letDecl $stx)
  | Expr.match #[x] _ #[] => do `(nomatch $(← trExpr x))
  | Expr.match xs _ #[] => do `(match $[$(← xs.mapM fun x => trExpr x):term],* with.)
  | Expr.match xs ty eqns => do
    `(match $[$(← xs.mapM fun x => trExpr x):term],* with $[$(← eqns.mapM trArm):matchAlt]*)
  | Expr.do _ els => do let els ← els.mapM fun e => trDoElem e.kind; `(do $[$els:doElem]*)
  | Expr.«{,}» es => do `({$(← es.mapM fun e => trExpr e),*})
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
      `({ $[$srcs,* with]? $[$flds:structInstField, ]* .. })
    else if let some last := flds.back? then
      `({ $[$srcs,* with]? $[$(flds.pop):structInstField, ]* $last:structInstField })
    else
      `({ $[$srcs,* with]? })
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
  | del : Syntax → TrAttr
  | add : Syntax → TrAttr
  | prio : Expr → TrAttr
  | parsingOnly : TrAttr
  | irreducible : TrAttr
  | derive : Array Name → TrAttr

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
      `(attr| recursor $(Quote.quote n):numLit)
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

def AttrState := SpecialAttrs × Array Syntax

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

def trModifiers (mods : Modifiers) : M (SpecialAttrs × Syntax) :=
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
  toSyntax : Modifiers4 → M (SpecialAttrs × Syntax)
  | ⟨doc, (s, attrs), vis, nc, safety⟩ => do
    let doc := mkOptionalNode $ doc.map trDocComment
    let attrs ← mkOpt attrs.asNonempty fun attrs => `(Parser.Term.attributes| @[$attrs,*])
    let vis := mkOptionalNode $ ← match vis with
    | Visibility.regular => pure none
    | Visibility.private => `(Parser.Command.visibility| private)
    | Visibility.protected => `(Parser.Command.visibility| protected)
    let nc ← mkOpt nc fun () => `(Parser.Command.noncomputable| noncomputable)
    let part := mkOptionalNode $ ← match safety with
    | DefinitionSafety.partial => some <$> `(Parser.Command.partial| partial)
    | _ => pure none
    let uns := mkOptionalNode $ ← match safety with
    | DefinitionSafety.unsafe => some <$> `(Parser.Command.unsafe| unsafe)
    | _ => pure none
    pure (s, mkNode ``Parser.Command.declModifiers #[doc, attrs, vis, nc, uns, part])

def trOpenCmd (ops : Array Open) : M Unit := do
  let mut simple := #[]
  let pushSimple (s : Array Syntax) :=
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

def trDeclId (n : Name) (us : LevelDecl) : M Syntax := do
  let us := us.map $ Array.map fun u => mkIdent u.kind
  let id ← mkIdentI n #[(← get).current.curNamespace ++ n]
  `(Parser.Command.declId| $id:ident $[.{$us,*}]?)

def trDeclSig (req : Bool) (bis : Binders) (ty : Option (Spanned Expr)) : M Syntax := do
  let bis := mkNullNode (← trBinders { allowSimple := some true } bis)
  let ty ← trOptType $ if req then some (ty.getD <| Spanned.dummy Expr.«_») else ty
  if req then pure $ mkNode ``Parser.Command.declSig #[bis, ty.get!]
  else pure $ mkNode ``Parser.Command.optDeclSig #[bis, mkOptionalNode ty]

def trAxiom (mods : Modifiers) (n : Name)
  (us : LevelDecl) (bis : Binders) (ty : Option (Spanned Expr)) : M Unit := do
  let (s, mods) ← trModifiers mods
  unless s.derive.isEmpty do warn! "unsupported: @[derive] axiom"
  pushM `(command| $mods:declModifiers axiom $(← trDeclId n us) $(← trDeclSig true bis ty))

def trDecl (dk : DeclKind) (mods : Modifiers) (n : Option (Spanned Name)) (us : LevelDecl)
  (bis : Binders) (ty : Option (Spanned Expr)) (val : DeclVal) : M Syntax := do
  let (s, mods) ← trModifiers mods
  let id ← n.mapM fun n => trDeclId n.kind us
  let sig req := trDeclSig req bis ty
  let val ← match val with
  | DeclVal.expr e => do `(Parser.Command.declValSimple| := $(← trExprUnspanned e))
  | DeclVal.eqns #[] => `(Parser.Command.declValSimple| := fun.)
  | DeclVal.eqns arms => do `(Parser.Command.declValEqns| $[$(← arms.mapM trArm):matchAlt]*)
  if s.irreducible then
    unless dk matches DeclKind.def do warn! "unsupported irreducible non-definition"
    unless s.derive.isEmpty do warn! "unsupported: @[derive, irreducible] def"
    return ← `(command| $mods:declModifiers irreducible_def $id.get! $(← sig false) $val)
  match dk with
  | DeclKind.abbrev => do
    unless s.derive.isEmpty do warn! "unsupported: @[derive] abbrev"
    `(command| $mods:declModifiers abbrev $id.get! $(← sig false) $val)
  | DeclKind.def => do
    let ds := s.derive.map mkIdent |>.asNonempty
    `(command| $mods:declModifiers def $id.get! $(← sig false) $val $[deriving $ds,*]?)
  | DeclKind.example => do
    unless s.derive.isEmpty do warn! "unsupported: @[derive] example"
    `(command| $mods:declModifiers example $(← sig true) $val)
  | DeclKind.theorem => do
    unless s.derive.isEmpty do warn! "unsupported: @[derive] theorem"
    `(command| $mods:declModifiers theorem $id.get! $(← sig true) $val)
  | DeclKind.instance => do
    unless s.derive.isEmpty do warn! "unsupported: @[derive] instance"
    let prio ← s.prio.mapM fun prio => do
      `(Parser.Command.namedPrio| (priority := $(← trPrio prio)))
    `(command| $mods:declModifiers instance $[$prio:namedPrio]? $[$id:declId]? $(← sig true) $val)

def trInferKind : Option InferKind → M (Option Syntax)
  | some InferKind.implicit => `(Parser.Command.inferMod | {})
  | some InferKind.relaxedImplicit => `(Parser.Command.inferMod | {})
  | some InferKind.none => pure none
  | none => pure none

def trOptDeriving : Array Name → M Syntax
  | #[] => `(Parser.Command.optDeriving|)
  | ds => `(Parser.Command.optDeriving| deriving $[$(ds.map mkIdent):ident],*)

def trInductive (cl : Bool) (mods : Modifiers) (n : Spanned Name) (us : LevelDecl)
  (bis : Binders) (ty : Option (Spanned Expr))
  (nota : Option Notation) (intros : Array (Spanned Intro)) : M Syntax := do
  let (s, mods) ← trModifiers mods
  let id ← trDeclId n.kind us
  let sig ← trDeclSig false bis ty
  let ctors ← intros.mapM fun ⟨m, ⟨doc, name, ik, bis, ty⟩⟩ => withSpanS m do
    `(Parser.Command.ctor| |
      $[$(doc.map trDocComment):docComment]?
      $(← mkIdentI name.kind):ident
      $[$(← trInferKind ik):inferMod]?
      $(← trDeclSig false bis ty):optDeclSig)
  let ds ← trOptDeriving s.derive
  match cl with
  | true => `(command| $mods:declModifiers class inductive
    $id:declId $sig:optDeclSig $[$ctors:ctor]* $ds:optDeriving)
  | false => `(command| $mods:declModifiers inductive
    $id:declId $sig:optDeclSig $[$ctors:ctor]* $ds:optDeriving)

def trMutual (decls : Array (Mutual α)) (f : Mutual α → M Syntax) : M Unit := do
  pushM `(mutual $(← decls.mapM f)* end)

def trField : Spanned Field → M (Array Syntax) := spanning fun
  | Field.binder bi ns ik bis ty dflt => do
    let ns ← ns.mapM fun n => mkIdentF n.kind
    let im ← trInferKind ik
    let sig req := trDeclSig req bis ty
    (#[·]) <$> match bi with
    | BinderInfo.implicit => do
      `(Parser.Command.structImplicitBinder| {$ns* $[$im]? $(← sig true):declSig})
    | BinderInfo.instImplicit => do
      `(Parser.Command.structInstBinder| [$ns* $[$im]? $(← sig true):declSig])
    | _ => do
      let sig ← sig false
      let dflt ← dflt.mapM trBinderDefault
      if ns.size = 1 then
        `(Parser.Command.structSimpleBinder| $(ns[0]):ident $[$im]? $sig:optDeclSig $[$dflt]?)
      else
        `(Parser.Command.structExplicitBinder| ($ns* $[$im]? $sig:optDeclSig $[$dflt]?))
  | Field.notation _ => warn! "unsupported: (notation) in structure"

def trFields (flds : Array (Spanned Field)) : M Syntax := do
  let flds ← flds.concatMapM trField
  pure $ mkNode ``Parser.Command.structFields #[mkNullNode flds]

def trStructure (cl : Bool) (mods : Modifiers) (n : Spanned Name) (us : LevelDecl)
  (bis : Binders) (exts : Array (Spanned Parent)) (ty : Option (Spanned Expr))
  (mk : Option (Spanned Mk)) (flds : Array (Spanned Field)) : M Unit := do
  let (s, mods) ← trModifiers mods
  let id ← trDeclId n.kind us
  let bis := mkNullNode $ ← trBinders {} bis
  let exts ← exts.mapM fun
    | ⟨_, false, none, ty, #[]⟩ => trExpr ty
    | _ => warn! "unsupported: advanced extends in structure"
  let exts ← mkOpt exts.asNonempty fun exts => `(Parser.Command.extends| extends $exts,*)
  let ty ← mkOptionalNode <$> trOptType ty
  let flds ← @mkNullNode <$> match mk, flds with
  | none, #[] => pure #[]
  | mk, flds => do
    let mk ← mk.mapM fun ⟨_, n, ik⟩ => do
      `(Parser.Command.structCtor| $(← mkIdentF n.kind):ident $[$(← trInferKind ik)]? ::)
    pure #[mkAtom "where", mkOptionalNode mk, ← trFields flds]
  let decl := mkNode ``Parser.Command.structure #[
    ← if cl then `(Parser.Command.classTk| class) else `(Parser.Command.structureTk| structure),
    id, bis, exts, ty, flds, ← trOptDeriving s.derive]
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

private def mkNAry (lits : Array (Spanned AST3.Literal)) : OptionM (Array Literal) := do
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

private def trMixfix (kind : Syntax) (prio : Option Syntax)
  (m : AST3.MixfixKind) (tk : String) (prec : Option (Spanned AST3.Precedence)) :
  M (NotationDesc × (Option Syntax → Syntax → Id Syntax)) := do
  let p ← match prec with
  | some p => trPrec p.kind
  | none => pure $ (← getPrecedence? tk m).getD (Precedence.nat 0)
  let p := truncatePrec p
  let p := p.toSyntax
  let s := Syntax.mkStrLit tk
  pure $ match m with
  | MixfixKind.infix =>
    (NotationDesc.infix tk, fun (n : Option Syntax) e => `(command|
      $kind:attrKind infixl:$p $[$n:namedName]? $[$prio:namedPrio]? $s => $e))
  | MixfixKind.infixl =>
    (NotationDesc.infix tk, fun (n : Option Syntax) e => `(command|
      $kind:attrKind infixl:$p $[$n:namedName]? $[$prio:namedPrio]? $s => $e))
  | MixfixKind.infixr =>
    (NotationDesc.infix tk, fun (n : Option Syntax) e => `(command|
      $kind:attrKind infixr:$p $[$n:namedName]? $[$prio:namedPrio]? $s => $e))
  | MixfixKind.prefix =>
    (NotationDesc.prefix tk, fun (n : Option Syntax) e => `(command|
      $kind:attrKind prefix:$p $[$n:namedName]? $[$prio:namedPrio]? $s => $e))
  | MixfixKind.postfix =>
    (NotationDesc.postfix tk, fun (n : Option Syntax) e => `(command|
      $kind:attrKind postfix:$p $[$n:namedName]? $[$prio:namedPrio]? $s => $e))

private def trNotation4 (kind : Syntax) (prio p : Option Syntax)
  (lits : Array (Spanned AST3.Literal)) : M (Option Syntax → Syntax → Id Syntax) := do
  let lits ← lits.mapM fun
  | ⟨_, AST3.Literal.sym tk⟩ => pure $ Syntax.mkStrLit tk.1.kind.toString
  | ⟨_, AST3.Literal.var x none⟩ =>
    `(Parser.Command.identPrec| $(mkIdent x.kind):ident)
  | ⟨_, AST3.Literal.var x (some ⟨_, Action.prec p⟩)⟩ => do
    `(Parser.Command.identPrec| $(mkIdent x.kind):ident : $((← trPrec p).toSyntax))
  | _ => warn! "unsupported (impossible)"
  pure fun n e => `(command|
    $kind:attrKind notation$[:$p]? $[$n:namedName]? $[$prio:namedPrio]? $lits* => $e)

private def trNotation3Item (lit : AST3.Literal) : M (Array Syntax) := do
  let stxs ← match lit with
  | AST3.Literal.sym tk => pure #[sym tk]
  | AST3.Literal.binder _ => pure #[binders]
  | AST3.Literal.binders _ => pure #[binders]
  | AST3.Literal.var x none => pure #[var x]
  | AST3.Literal.var x (some ⟨_, Action.prec _⟩) => pure #[var x]
  | AST3.Literal.var x (some ⟨_, Action.prev⟩) => pure #[var x]
  | AST3.Literal.var x (some ⟨_, Action.scoped _ sc⟩) => scope x sc
  | AST3.Literal.var x (some ⟨_, Action.fold r _ sep «rec» (some ini) term⟩) => do
    let f ← fold x r sep «rec» ini
    pure $ match term.map sym with | none => #[f] | some a => #[f, a]
  | _ => warn! "unsupported: advanced notation ({repr lit})"
  pure $ stxs.map $ mkNode ``Parser.Command.notation3Item
where
  sym tk := #[Syntax.mkStrLit tk.1.kind.toString]
  var x := #[mkIdent x.kind, mkNullNode]
  binders := #[mkNode ``Parser.Command.bindersItem #[mkAtom "(", mkAtom "...", mkAtom ")"]]
  scope x sc := do
    let (p, e) := match sc with
    | none => (`x, Spanned.dummy $ Expr.ident `x)
    | some (p, e) => (p.kind, e)
    pure #[#[mkIdent x.kind, mkNullNode #[
      mkNode ``Parser.Command.identScope #[
        mkAtom ":", mkAtom "(", mkAtom "scoped",
        mkIdent p, mkAtom "=>", ← trExpr e, mkAtom ")"]]]]
  fold x r sep | (y, z, «rec»), ini => do
    let sep := mkNode ``Parser.Command.foldRep $ match sep.1.kind.trim with
    | "," => #[mkAtom ",*"]
    | _ => #[Syntax.mkStrLit sep.1.kind.toString, mkAtom "*"]
    pure #[mkNode ``Parser.Command.foldAction #[
      mkAtom "(", mkIdent x.kind, sep, mkAtom "=>", mkAtom (if r then "foldr" else "foldl"),
      mkAtom "(", mkIdent y.kind, mkIdent z.kind, mkAtom "=>", ← trExpr rec, mkAtom ")",
      ← trExpr ini, mkAtom ")"]]

private def addSpaceBeforeBinders (lits : Array AST3.Literal) : Array AST3.Literal := Id.run do
  let mut lits := lits
  for i in [1:lits.size] do
    if lits[i] matches AST3.Literal.binder .. || lits[i] matches AST3.Literal.binders .. then
      if let AST3.Literal.sym (⟨s, Symbol.quoted tk⟩, prec) := lits[i-1] then
        if !tk.endsWith " " then
          lits := lits.set! (i-1) <| AST3.Literal.sym (⟨s, Symbol.quoted (tk ++ " ")⟩, prec)
  lits

private def trNotation3 (kind : Syntax) (prio p : Option Syntax)
  (lits : Array (Spanned AST3.Literal)) : M (Option Syntax → Syntax → Id Syntax) := do
  let lits := addSpaceBeforeBinders <| lits.map (·.kind)
  let lits ← lits.concatMapM trNotation3Item
  pure fun n e => `(command|
    $kind:attrKind notation3$[:$p]? $[$n:namedName]? $[$prio:namedPrio]? $lits* => $e)

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
  | _ => warn! "unsupported (impossible)"
  let e ← trExpr e
  let n4 ← Elab.Command.withWeakNamespace (ns ++ (← getEnv).mainModule) $ do
    let n4 ← mkUnusedName nota.name4
    let nn ← `(Parser.Command.namedName| (name := $(mkIdent n4)))
    try elabCommand $ cmd (some nn) e
    catch e => dbg_trace "warning: failed to add syntax {repr n4}: {← e.toMessageData.toString}"
    pure $ (← getCurrNamespace) ++ n4
  printOutput s!"-- mathport name: «{n}»\n"
  if ns == default then push $ cmd none e
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
  (f : Syntax → Syntax) : M Unit := do
  if ns.isEmpty then return ()
  let kind := if loc then AttributeKind.local else AttributeKind.global
  let (s, attrs) := (← trAttributes attrs true kind |>.run ({}, #[])).2
  let ns ← ns.mapM fun n => mkIdentI n.kind
  unless s.derive.isEmpty do
    push $ f $ ← `(command| deriving instance $[$(s.derive.map mkIdent):ident],* for $ns,*)
  unless attrs.isEmpty do
    push $ f $ ← `(command| attribute [$attrs,*] $ns*)

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
      let bis ← trBinders {} bis
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
      pushM `(command| set_option $(← mkIdentO o) $(Syntax.mkStrLit s):strLit)
    | o, OptionVal.nat n => do
      pushM `(command| set_option $(← mkIdentO o) $(Quote.quote n):numLit)
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
    | some f => try f mods args catch e => warn! "in {n}: {← e.toMessageData.toString}"
    | none => warn! "unsupported user command {n}"
