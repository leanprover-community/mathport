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
  deriving Inhabited

def NotationEntries.insert (m : NotationEntries) : NotationData → NotationEntries
  | d => HashMap.insert m d.n3 d

initialize synportNotationExtension : SimplePersistentEnvExtension NotationData NotationEntries ←
  registerSimplePersistentEnvExtension {
    name          := `Mathport.Translate.synportNotationExtension
    addEntryFn    := NotationEntries.insert
    addImportedFn := fun es => mkStateFromImportedEntries NotationEntries.insert {} es
  }

def getGlobalNotationEntry? (s : String) : CommandElabM (Option NotationEntry) := do
  match synportNotationExtension.getState (← getEnv) |>.find? s with
  | none => predefinedNotations.find? s
  | some d => d.unpack

def registerGlobalNotationEntry (d : NotationData) : CommandElabM Unit := do
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

def getPrecedence? (tk : String) (kind : MixfixKind) : CommandElabM (Option Precedence) := do
  let tk := tk.trim
  let kind := PrecedenceKind.ofMixfixKind kind
  synportPrecedenceExtension.getState (← getEnv) |>.find? (tk, kind)

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
  warn := arbitrary

instance (priority := high) [Monad m] : Warnable <| m Syntax where
  warn s := Syntax.mkStrLit s

open Lean Elab in
elab:max "warn!" interpStr:interpolatedStr(term) or:(checkColGt "|" term)? : term <= ty => do
  let pos ← Elab.getRefPosition
  let head := Syntax.mkStrLit $ mkErrorStringWithPos (← read).fileName pos ""
  let str ← Elab.liftMacroM <| interpStr.expandInterpolatedStr (← `(String)) (← `(toString))
  let or ← if or.getNumArgs == 2 then or.getArg 1 else `(Warnable.warn str)
  (Term.elabTerm · ty) <|<- `(do
    let str : String := $head ++ $str
    logComment str
    $or:term)

def trExpr (e : Expr) : M Syntax := do (← read).trExpr e
def trCommand (e : Command) : M Unit := do (← read).trCommand e

def renameIdent (n : Name) : M Name := do Rename.resolveIdent! (← getEnv) n
def renameNamespace (n : Name) : M Name := do Rename.renameNamespace (← getEnv) n
def renameAttr (n : Name) : M Name := do Rename.renameAttr n
def renameModule (n : Name) : M Name := do Rename.renameModule (← read).pcfg n
def renameField (n : Name) : M Name := do Rename.renameField? (← getEnv) n |>.getD n
def renameOption : Name → M Name
  | n => warn! "warning: unsupported option {n}" | n

def mkIdentI (n : Name) : M Syntax := do mkIdent (← renameIdent n)
def mkIdentA (n : Name) : M Syntax := do mkIdent (← renameAttr n)
def mkIdentN (n : Name) : M Syntax := do mkIdent (← renameNamespace n)
def mkIdentF (n : Name) : M Syntax := do mkIdent (← renameField n)
def mkIdentO (n : Name) : M Syntax := do mkIdent (← renameOption n)

def Parser.ParserM.run' (p : ParserM α) (args : Array (Spanned VMCall)) : M α := do
  match p.run ⟨(← read).commands, args⟩ with
  | Except.ok a => a
  | Except.error e => throw! "unsupported: {e}"

def AST3toData4 : AST3 → M Data4
  | ⟨prel, imp, commands, _, _⟩ => do
    let prel := prel.map fun _ => mkNode ``Parser.Module.prelude #[mkAtom "prelude"]
    let imp ← imp.foldlM (init := #[]) fun imp ns =>
      ns.foldlM (init := imp) fun imp n => do
        imp.push $ mkNode ``Parser.Module.import #[mkAtom "import",
          mkNullNode, mkIdent (← renameModule n.kind)]
    let fmt ← liftCoreM $ PrettyPrinter.format Parser.Module.header.formatter $
      mkNode ``Parser.Module.header #[mkOptionalNode prel, mkNullNode imp]
    modify fun s => { s with output := fmt }
    commands.forM fun c => do
      try trCommand c.kind
      catch e =>
        let e := s!"error in {(← getEnv).mainModule}: {← e.toMessageData.toString}"
        println! e
        -- println! (repr c.kind)
        printOutput f!"/- {e}\nLean 3 AST:\n{(repr c.kind).group}-/\n\n"
    let s ← get
    pure ⟨s.output, HashMap.empty⟩

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
    let res ← k
    (res, ← getTraces)
  finally
    modifyTraces fun _ => old

private def tryParenthesizeCommand (stx : Syntax) : CoreM <| Syntax × Format := do
  try
    (← Lean.PrettyPrinter.parenthesizeCommand stx, f!"")
  catch e =>
    let (_, traces) ← captureTraces do
      withOptions (·.setBool `trace.PrettyPrinter.parenthesize true) do
        try Lean.PrettyPrinter.parenthesizeCommand stx catch _ => stx
    let traces ← traces.toList.mapM (·.msg.format)
    (stx, f!"/- failed to parenthesize: {← e.toMessageData.toString}\n{Format.joinSep traces "\n"}-/")

def push (stx : Syntax) : M Unit := do
  let stx ← try (← read).transform stx catch ex =>
    warn! "failed to transform: {← ex.toMessageData.toString}" | stx
  let fmt ← liftCoreM $ do
    let (stx, parenthesizerErr) ← tryParenthesizeCommand stx
    parenthesizerErr ++ (←
      try Lean.PrettyPrinter.formatCommand stx
      catch e =>
        f!"-- failed to format: {← e.toMessageData.toString}\n{reprint stx}")
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
  | some d => d.unpack

def registerNotationEntry (loc : Bool) (d : NotationData) : M Unit :=
  if loc then modifyScope fun sc => { sc with localNotations := sc.localNotations.insert d }
  else registerGlobalNotationEntry d

def mkOptionalNode' (x : Option α) (f : α → Array Syntax) : Syntax :=
  mkNullNode $ match x with
  | none => #[]
  | some a => f a

def mkOptionalNodeM [Monad m] (x : Option α) (f : α → m (Array Syntax)) : m Syntax := do
  mkNullNode $ ← match x with
  | none => #[]
  | some a => f a

def trDocComment (doc : String) : Syntax :=
  mkNode ``Parser.Command.docComment #[mkAtom "/--", mkAtom (doc ++ "-/")]

partial def scientificLitOfDecimal (num den : Nat) : Option Syntax :=
  findExp num den 0 |>.map fun (m, e) =>
    let str := toString m
    if e == str.length then
      Syntax.mkScientificLit ("0." ++ str)
    else if e < str.length then
      let mStr := str.extract 0 (str.length - e)
      let eStr := str.extract (str.length - e) str.length
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
  | Level.nat n => Quote.quote n
  | Level.add l n => do `(level| $(← trLevel l.kind) + $(Quote.quote n.kind))
  | Level.imax ls => do `(level| imax $(← ls.mapM fun l => trLevel l.kind)*)
  | Level.max ls => do `(level| max $(← ls.mapM fun l => trLevel l.kind)*)
  | Level.param u => mkIdent u
  | Level.paren l => trLevel l.kind -- do `(level| ($(← trLevel l.kind)))

partial def trPrio : Expr → M Syntax
  | Expr.nat n => Quote.quote n
  | Expr.paren e => trPrio e.kind -- do `(prio| ($(← trPrio e.kind)))
  | _ => warn! "unsupported: advanced prio syntax" | quote (999 : Nat)

partial def trPrecExpr : Expr → M Precedence
  | Expr.nat n => Precedence.nat n
  | Expr.paren e => trPrecExpr e.kind -- do `(prec| ($(← trPrecExpr e.kind)))
  | Expr.ident `max => Precedence.max
  | Expr.ident `std.prec.max_plus => Precedence.maxPlus
  | Expr.notation (Choice.one `«expr + ») #[
      ⟨_, Arg.expr (Expr.ident `max)⟩,
      ⟨_, Arg.expr (Expr.nat 1)⟩
    ] => Precedence.maxPlus
  | _ => warn! "unsupported: advanced prec syntax" | Precedence.nat 999

def trPrec : AST3.Precedence → M Precedence
  | AST3.Precedence.nat n => Precedence.nat n
  | AST3.Precedence.expr e => trPrecExpr e.kind

def trBinderName : BinderName → Syntax
  | BinderName.ident n => mkIdent n
  | BinderName.«_» => mkHole arbitrary

def trIdent_ : BinderName → Syntax
  | BinderName.ident n => mkIdent n
  | BinderName.«_» => mkAtom "_"

def trBinderIdent (n : BinderName) : Syntax := mkNode ``binderIdent #[trIdent_ n]

def trBinderIdentI : BinderName → M Syntax
  | BinderName.ident n => do mkNode ``binderIdent #[← mkIdentI n]
  | BinderName.«_» => mkNode ``binderIdent #[mkAtom "_"]

inductive TacticContext | seq | one

def optTy (ty : Option Syntax) : M (Option Syntax) :=
  ty.mapM fun stx => do `(Parser.Term.typeSpec| : $stx)

def trCalcArgs (args : Array (Spanned Expr × Spanned Expr)) : M (Array Syntax) :=
  args.mapM fun (lhs, rhs) => do
    mkNode ``calcStep #[← trExpr lhs.kind, mkAtom ":=", ← trExpr rhs.kind]

mutual

  partial def trBlock : Block → (c :_:= TacticContext.seq) → M Syntax
    | ⟨_, none, none, #[]⟩, TacticContext.seq => do `(Parser.Tactic.tacticSeq| {})
    | ⟨_, none, none, tacs⟩, TacticContext.seq => do
      mkNode ``Parser.Tactic.tacticSeq #[mkNode ``Parser.Tactic.tacticSeq1Indented #[
        mkNullNode $ ← tacs.mapM fun tac => do mkGroupNode #[← trTactic tac.kind, mkNullNode]]]
    | bl, TacticContext.one => do `(tactic| · $(← trBlock bl):tacticSeq)
    | ⟨_, cl, cfg, tacs⟩, _ => warn! "unsupported (TODO): block with cfg"

  partial def trTactic : Tactic → (c :_:= TacticContext.one) → M Syntax
    | Tactic.block bl, c => trBlock bl c
    | Tactic.by tac, c => trBlock ⟨true, none, none, #[tac]⟩ c
    | tac, TacticContext.seq => trBlock ⟨true, none, none, #[Spanned.dummy tac]⟩
    | Tactic.«;» tacs, TacticContext.one => do
      let rec build (i : Nat) (lhs : Syntax) : M Syntax :=
        if h : i < tacs.size then do
          match ← trTacticOrList (tacs.get ⟨i, h⟩).kind with
          | Sum.inl tac => `(tactic| $lhs <;> $(← build (i+1) tac))
          | Sum.inr tacs => build (i+1) (← `(tactic| $lhs <;> [$tacs,*]))
        else lhs
      build 1 (← trTactic tacs[0].kind)
    | Tactic.«<|>» tacs, TacticContext.one => do
      let tacs ← tacs.mapM fun tac => trTactic tac.kind TacticContext.seq
      `(tactic| first $[| $tacs:tacticSeq]*)
    | Tactic.«[]» tacs, _ => warn! "unsupported (impossible)"
    | Tactic.exact_shortcut ⟨_, Expr.calc args⟩, TacticContext.one => do
      `(tactic| calc $(← trCalcArgs args)*)
    | Tactic.exact_shortcut e, TacticContext.one => do `(tactic| exact $(← trExpr e.kind))
    | Tactic.expr e, TacticContext.one => do
      let rec head
      | Expr.ident x => x
      | Expr.paren e => head e.kind
      | Expr.app e _ => head e.kind
      | _ => Name.anonymous
      match Rename.resolveIdent? (← getEnv) (head e.kind) with
      | none =>
        -- warn! "unsupported non-interactive tactic {repr e}"
        match ← trExpr e.kind with
        | `(do $[$els]*) => `(tactic| run_tac $[$els:doSeqItem]*)
        | stx => `(tactic| run_tac $stx:term)
      | some n =>
        match (← get).niTactics.find? n with
        | some f => try f e.kind catch e => warn! "in {n}: {← e.toMessageData.toString}"
        | none => warn! "unsupported non-interactive tactic {n}"
    | Tactic.interactive n args, TacticContext.one => do
      match (← get).tactics.find? n with
      | some f => try f args catch e => warn! "in {n}: {← e.toMessageData.toString}"
      | none => warn! "unsupported tactic {repr n}"

  partial def trTacticOrList : Tactic → M (Sum Syntax (Array Syntax))
    | Tactic.«[]» args => Sum.inr <$> args.mapM fun arg => trTactic arg.kind
    | tac => Sum.inl <$> trTactic tac

end

def trIdTactic : Block → (c :_:= TacticContext.one) → M Syntax
  | bl, TacticContext.seq => trBlock bl
  | ⟨_, none, none, #[]⟩, _ => do `(tactic| skip)
  | ⟨_, none, none, #[tac]⟩, _ => trTactic tac.kind
  | bl, _ => do `(tactic| ($(← trBlock bl):tacticSeq))

def mkConvBlock (args : Array Syntax) : Syntax :=
  mkNode ``Parser.Tactic.Conv.convSeq #[mkNode ``Parser.Tactic.Conv.convSeq1Indented #[
    mkNullNode $ args.map fun tac => mkGroupNode #[tac, mkNullNode]]]

mutual

  partial def trConvBlock : Block → (c :_:= TacticContext.seq) → M Syntax
    | ⟨_, none, none, #[]⟩, TacticContext.seq => do mkConvBlock #[← `(conv| skip)]
    | ⟨_, none, none, tacs⟩, TacticContext.seq => do
      mkConvBlock $ ← tacs.mapM fun tac => trConv tac.kind
    | bl, TacticContext.one => do `(conv| · $(← trConvBlock bl):convSeq)
    | ⟨_, cl, cfg, tacs⟩, _ => warn! "unsupported (TODO): conv block with cfg"

  partial def trConv : Tactic → (c :_:= TacticContext.one) → M Syntax
    | Tactic.block bl, c => trConvBlock bl c
    | Tactic.by tac, c => trConvBlock ⟨true, none, none, #[tac]⟩ c
    | tac, TacticContext.seq => trConvBlock ⟨true, none, none, #[Spanned.dummy tac]⟩
    | Tactic.«;» tacs, _ => warn! "unsupported (impossible)"
    | Tactic.«<|>» tacs, TacticContext.one => do
      let tacs ← tacs.mapM fun tac => trConv tac.kind TacticContext.seq
      `(conv| first $[| $tacs:convSeq]*)
    | Tactic.«[]» tacs, _ => warn! "unsupported (impossible)"
    | Tactic.exact_shortcut _, _ => warn! "unsupported (impossible)"
    | Tactic.expr e, TacticContext.one => do
      match ← trExpr e.kind with
      | `(do $[$els]*) => `(conv| run_conv $[$els:doSeqItem]*)
      | stx => `(conv| run_conv $stx:term)
    | Tactic.interactive n args, TacticContext.one => do
      match (← get).convs.find? n with
      | some f => try f args catch e => warn! "in {n}: {← e.toMessageData.toString}"
      | none => warn! "unsupported conv tactic {repr n}"

end

def trBinderDefault : Default → M Syntax
  | Default.«:=» e => do `(Parser.Term.binderDefault| := $(← trExpr e.kind))
  | Default.«.» e => do
    `(Parser.Term.binderTactic| := by
      $(← trTactic (Tactic.expr $ e.map Expr.ident) TacticContext.seq):tacticSeq)

def trBinary (n : Name) (lhs rhs : Syntax) : M Syntax := do
  match ← getNotationEntry? n.getString! with
  | some ⟨_, _, NotationKind.unary f, _⟩ => f lhs
  | some ⟨_, _, NotationKind.binary f, _⟩ => f lhs rhs
  | some ⟨_, _, NotationKind.nary f, _⟩ => f #[lhs, rhs]
  | _ =>
    warn! "warning: unsupported binary notation {repr n}"
    mkNode ``Parser.Term.app #[mkIdent n, mkNullNode #[lhs, rhs]]

def expandBinderCollection
  (trBinder : Array (Spanned BinderName) → Option (Spanned Expr) → Array Syntax → M (Array Syntax))
  (bi : BinderInfo) (vars : Array (Spanned BinderName))
  (n : Name) (e : Spanned Expr) (out : Array Syntax) : M (Array Syntax) := do
  warn! "warning: expanding binder collection {
    bi.bracket true $ spaced repr vars ++ " " ++ n.toString ++ " " ++ repr e}"
  let vars := vars.map $ Spanned.map fun | BinderName.ident v => v | _ => `_x
  let vars1 := vars.map $ Spanned.map BinderName.ident
  let mut out ← trBinder vars1 none out
  let H := #[Spanned.dummy BinderName._]
  for v in vars do
    let ty := Expr.notation (Choice.one n) #[v.map $ Arg.expr ∘ Expr.ident, e.map Arg.expr]
    out ← trBinder H (some (Spanned.dummy ty)) out
  out

def trBasicBinder : BinderContext → BinderInfo → Option (Array (Spanned BinderName)) →
    Binders → Option (Spanned Expr) → Option Default → M Syntax
  | _, BinderInfo.instImplicit, vars, _, some ty, none => do
    let var ← match vars with
    | none => #[]
    | some #[v] => pure #[trBinderName v.kind, mkAtom ":"]
    | some _ => warn! "unsupported (impossible)"
    mkNode ``Parser.Term.instBinder
      #[mkAtom "[", mkNullNode var, ← trExpr ty.kind, mkAtom "]"]
  | ⟨allowSimp, req⟩, bi, some vars, bis, ty, dflt => do
    let ty := match req || !bis.isEmpty, ty with
    | true, none => some (Spanned.dummy Expr.«_»)
    | _, _ => ty
    let ty ← ty.mapM fun ty => trExpr (Expr.Pi bis ty)
    let vars := mkNullNode $ vars.map fun v => trBinderName v.kind
    if let some stx ← trSimple allowSimp bi vars ty dflt then
      return stx
    let ty := mkOptionalNode' ty fun ty => #[mkAtom ":", ty]
    match bi with
    | BinderInfo.implicit =>
      mkNode ``Parser.Term.implicitBinder #[mkAtom "{", vars, ty, mkAtom "}"]
    | BinderInfo.strictImplicit =>
      mkNode ``Parser.Term.strictImplicitBinder #[mkAtom "⦃", vars, ty, mkAtom "⦄"]
    | _ => do
      let dflt ← mkOptionalNode <$> dflt.mapM trBinderDefault
      mkNode ``Parser.Term.explicitBinder #[mkAtom "(", vars, ty, dflt, mkAtom ")"]
  | _, _, _, _, _, _ => warn! "unsupported (impossible)"
where
  trSimple
  | some b, BinderInfo.default, vars, ty, none => do
    if b && ty.isSome then return none
    mkNode ``Parser.Term.simpleBinder #[vars, mkOptionalNode (← optTy ty)]
  | _, _, _, _, _ => none

def trBinder' : BinderContext → Binder → Array Binder' → M (Array Binder')
  | bc, Binder.binder bi vars bis ty dflt, out => do
    out.push $ Binder'.basic $ ← trBasicBinder bc bi vars bis ty dflt
  | bc, Binder.collection bi vars n e, out =>
    out.push $ Binder'.collection bi vars n e
  | _, Binder.notation _, _ => warn! "unsupported: (notation) binder"

def trBinders' (bc : BinderContext)
  (bis : Array (Spanned Binder)) : M (Array Binder') := do
  bis.foldlM (fun out bi => trBinder' bc bi.kind out) #[]

def expandBinder : BinderContext → Binder' → Array Syntax → M (Array Syntax)
  | bc, Binder'.basic bi, out => out.push bi
  | bc, Binder'.collection bi vars n rhs, out =>
    expandBinderCollection
      (fun vars ty out => out.push <$> trBasicBinder bc bi (some vars) #[] ty none)
      bi vars n rhs out

def expandBinders (bc : BinderContext) (bis : Array Binder') : M (Array Syntax) := do
  bis.foldlM (fun out bi => expandBinder bc bi out) #[]

def trBinders (bc : BinderContext)
  (bis : Array (Spanned Binder)) : M (Array Syntax) := do
  expandBinders bc (← trBinders' bc bis)

def trDArrow (bis : Array (Spanned Binder)) (ty : Expr) : M Syntax := do
  let bis ← trBinders { requireType := true } bis
  pure $ bis.foldr (init := ← trExpr ty) fun bi ty =>
    mkNode ``Parser.Term.depArrow #[bi, mkAtom "→", ty]

def trExtendedBindersGrouped
  (reg : Array Syntax → Syntax → Syntax) (ext : Syntax → Syntax → Syntax → Syntax)
  (bc : BinderContext) (bis : Array Binder') (e : Expr) : M Syntax := do
  let tr1 : Array Syntax × (Syntax → Syntax) → Binder' → M (Array Syntax × (Syntax → Syntax))
  | (args, f), Binder'.basic stx => (args.push stx, f)
  | (args, f), bic@(Binder'.collection bi vars n rhs) => do
    match vars, predefinedBinderPreds.find? n.getString! with
    | #[v], some g =>
      let v ← trBinderName v.kind
      let pred := g (← trExpr rhs.kind)
      (#[], fun e => f $ reg args $ ext v pred e)
    | _, _ => (← expandBinder bc bic args, f)
  let (args, f) ← bis.foldlM tr1 (#[], id)
  f $ reg args (← trExpr e)

def trExplicitBinders : Array (Spanned Binder) → M Syntax
  | #[⟨_, Binder.binder _ (some vars) _ ty none⟩] => do
    let ty ← match ty with | none => #[] | some ty => do #[mkAtom ":", ← trExpr ty.kind]
    mkNode ``explicitBinders #[mkNode ``unbracketedExplicitBinders #[
      mkNullNode $ vars.map fun n => trBinderIdent n.kind, mkNullNode ty]]
  | bis => do
    let trBasicBinder (vars : Option (Array (Spanned BinderName)))
      (ty : Option (Spanned Expr)) : M Syntax := do
      let vars ← match vars with
      | some vars => vars.mapM fun n => trBinderIdent n.kind
      | none => #[mkNode ``binderIdent #[mkAtom "_"]]
      let ty ← match ty with | none => `(_) | some ty => trExpr ty.kind
      mkNode ``bracketedExplicitBinders #[mkAtom "(", mkNullNode vars, mkAtom ":", ty, mkAtom ")"]
    let rec trBinder : AST3.Binder → Array Syntax → M (Array Syntax)
    | Binder.binder _ vars _ ty none, bis => bis.push <$> trBasicBinder vars ty
    | Binder.collection bi vars n rhs, bis =>
      expandBinderCollection (fun vars ty out => out.push <$> trBasicBinder vars ty)
        bi vars n rhs bis
    | Binder.notation _, _ => warn! "unsupported: (notation) binder"
    | _, _ => warn! "unsupported (impossible)"
    let bis ← bis.foldlM (fun out bi => trBinder bi.kind out) #[]
    mkNode ``explicitBinders #[mkNullNode bis]

def trExplicitBindersExt
  (reg : Syntax → Syntax → Syntax) (ext : Option (Syntax → Syntax → Syntax → Syntax))
  (bis : Array (Spanned Binder)) (e : Expr) : M Syntax := do
  let reg' (bis) : M (Syntax → Syntax) := do
    if bis.isEmpty then pure id else reg (← trExplicitBinders bis)
  match ext with
  | none => (← reg' bis) (← trExpr e)
  | some ext => do
    let (left, f) ← bis.foldlM (init := (#[], id)) fun (left, f) bi => do
      if let Binder.collection _ #[v] n rhs := bi.kind then
        if let some g := predefinedBinderPreds.find? n.getString! then
          (#[], f ∘ (← reg' left) ∘ ext (← trBinderName v.kind) (g (← trExpr rhs.kind)))
        else (left.push bi, f)
      else (left.push bi, f)
    pure $ f ((← reg' left) (← trExpr e))

def trExtBinders (args : Array (Spanned Binder)) : M Syntax := do
  let out ← args.foldlM (init := #[]) fun
  | out, ⟨_, Binder.binder _ vars _ ty _⟩ =>
    trBasicBinder (vars.getD #[Spanned.dummy BinderName._]) ty out
  | out, ⟨_, Binder.collection bi vars n rhs⟩ =>
    if let some g := predefinedBinderPreds.find? n.getString! then
      onVars vars out fun v out => do
        out.push $ ← `(Mathlib.ExtendedBinder.extBinder|
          $(trBinderIdent v):binderIdent $(g (← trExpr rhs.kind)):binderPred)
    else
      expandBinderCollection trBasicBinder bi vars n rhs out
  | out, ⟨_, Binder.notation _⟩ => warn! "unsupported: (notation) binder" | out
  if let #[bi] := out then `(Mathlib.ExtendedBinder.extBinders| $bi:extBinder)
  else `(Mathlib.ExtendedBinder.extBinders| $[($out:extBinder)]*)
where
  onVars {α} (vars) (out : α) (f : BinderName → α → M α) : M α := do
    if vars.size > 1 then
      warn! "warning: expanding binder group ({spaced repr vars})"
    vars.foldlM (fun out ⟨_, v⟩ => f v out) out
  trBasicBinder (vars ty out) :=
    onVars vars out fun v out => do
      out.push $ ← `(Mathlib.ExtendedBinder.extBinder|
        $(trBinderIdent v):binderIdent $[: $(← ty.mapM fun ty => trExpr ty.kind)]?)

def trLambdaBinder : LambdaBinder → Array Syntax → M (Array Syntax)
  | LambdaBinder.reg bi, out => do
    let bc := { allowSimple := some false }
    (← trBinder' bc bi #[]).foldlM (fun out bi => expandBinder bc bi out) out
  | LambdaBinder.«⟨⟩» args, out => do out.push $ ← trExpr (Expr.«⟨⟩» args)

def trOptType (ty : Option Expr) : M (Option Syntax) := ty.mapM trExpr >>= optTy

def trLetDecl : LetDecl → M Syntax
  | LetDecl.var x bis ty val => do
    let letId := mkNode ``Parser.Term.letIdDecl #[
      trBinderName x.kind,
      mkNullNode $ ← trBinders { allowSimple := some true } bis,
      mkOptionalNode $ ← trOptType $ ty.map (·.kind),
      mkAtom ":=", ← trExpr val.kind]
    `(Parser.Term.letDecl| $letId:letIdDecl)
  | LetDecl.pat lhs val => do
    `(Parser.Term.letDecl| $(← trExpr lhs.kind):term := $(← trExpr val.kind))
  | LetDecl.notation n => warn! "unsupported: let notation := ..."

def trArm : Arm → M Syntax
  | ⟨lhs, rhs⟩ => do
    `(Parser.Term.matchAltExpr|
      | $(← lhs.mapM fun e => trExpr e.kind),* => $(← trExpr rhs.kind))

def trDoElem : DoElem → M Syntax
  | DoElem.let decl => do `(doElem| let $(← trLetDecl decl.kind):letDecl)
  | DoElem.eval e => do `(doElem| $(← trExpr e.kind):term)
  | DoElem.«←» lhs ty rhs els => do
    let rhs ← trExpr rhs.kind
    match lhs.kind.unparen, els with
    | Expr.ident lhs, none =>
      `(doElem| let $(mkIdent lhs):ident $(← trOptType (ty.map (·.kind)))? ← $rhs:term)
    | _, _ =>
      let els ← els.mapM fun e => trExpr e.kind
      `(doElem| let $(← trExpr lhs.kind):term ← $rhs:term $[| $els:term]?)

def trProof : Proof → (useFrom : Bool := true) → M Syntax
  | Proof.«from» _ e, useFrom => do
    let e ← trExpr e.kind
    if useFrom then `(Parser.Term.fromTerm| from $e) else e
  | Proof.block bl, _ => do `(by $(← trBlock bl):tacticSeq)
  | Proof.by tac, _ => do `(by $(← trTactic tac.kind TacticContext.seq):tacticSeq)

def trNotation (n : Choice) (args : Array (Spanned Arg)) : M Syntax := do
  let n ← match n with
  | Choice.one n => n
  | Choice.many ns =>
    if ns[1:].all (ns[0] == ·) then ns[0] else
      warn! "unsupported: ambiguous notation" | ns[0]
  match ← getNotationEntry? n.getString!, args.map (·.kind) with
  | some ⟨_, _, NotationKind.const stx, _⟩, #[] => stx
  | some ⟨_, _, NotationKind.const stx, _⟩, _ => warn! "unsupported (impossible)"
  | some ⟨_, _, NotationKind.unary f, _⟩, #[Arg.expr e] => f (← trExpr e)
  | some ⟨_, _, NotationKind.unary f, _⟩, _ => warn! "unsupported (impossible)"
  | some ⟨_, _, NotationKind.binary f, _⟩, #[Arg.expr e₁, Arg.expr e₂] => f (← trExpr e₁) (← trExpr e₂)
  | some ⟨_, _, NotationKind.binary f, _⟩, _ => warn! "unsupported (impossible)"
  | some ⟨_, _, NotationKind.nary f, _⟩, args => f <$> args.mapM fun
    | Arg.expr e => trExpr e
    | Arg.binder bi => trExtBinders #[Spanned.dummy bi]
    | Arg.binders bis => trExtBinders bis
    | _ => warn! "unsupported (impossible)"
  | some ⟨_, _, NotationKind.exprs f, _⟩, #[Arg.exprs es] => f $ ← es.mapM fun e => trExpr e.kind
  | some ⟨_, _, NotationKind.exprs f, _⟩, _ => warn! "unsupported (impossible)"
  | some ⟨_, _, NotationKind.binder f g, _⟩, #[Arg.binder bi, Arg.expr e] =>
    trExplicitBindersExt f g #[Spanned.dummy bi] e
  | some ⟨_, _, NotationKind.binder f g, _⟩, #[Arg.binders bis, Arg.expr e] =>
    trExplicitBindersExt f g bis e
  | some ⟨_, _, NotationKind.binder .., _⟩, _ => warn! "unsupported (impossible)"
  | some ⟨_, _, NotationKind.fail, _⟩, args =>
    warn! "warning: unsupported notation {repr n}"
    let args ← args.mapM fun | Arg.expr e => trExpr e | _ => warn! "unsupported notation {repr n}"
    mkNode ``Parser.Term.app #[mkIdent n, mkNullNode args]
  | none, args =>
    warn! "warning: unsupported notation {repr n}"
    let args ← args.mapM fun | Arg.expr e => trExpr e | _ => warn! "unsupported notation {repr n}"
    mkNode ``Parser.Term.app #[mkIdent n, mkNullNode args]

def trInfixFn (n : Choice) (e : Option (Spanned Expr)) : M Syntax := do
  let n ← match n with
  | Choice.one n => n
  | Choice.many ns =>
    if ns[1:].all (ns[0] == ·) then ns[0] else
      warn! "unsupported: ambiguous notation" | ns[0]
  trBinary n mkCDot $ ← match e with
  | none => mkCDot
  | some e => trExpr e.kind

partial def trAppArgs [Inhabited α] : (e : Expr) → (m : Expr → M α) → M (α × Array Syntax)
  | Expr.app f x, m => do let (f, args) ← trAppArgs f.kind m; (f, args.push (← trExpr x.kind))
  | e, m => do (← m e, #[])

def trExpr' : Expr → M Syntax
  | Expr.«...» => `(_)
  | Expr.sorry => `(sorry)
  | Expr.«_» => `(_)
  | Expr.«()» => `(())
  | Expr.«{}» => `({})
  | Expr.ident n => mkIdentI n
  | Expr.const _ n none => mkIdentI n.kind
  | Expr.const _ n (some #[]) => mkIdentI n.kind
  | Expr.const _ n (some l) => do
    mkNode ``Parser.Term.explicitUniv #[← mkIdentI n.kind,
      mkAtom ".{", (mkAtom ",").mkSep $ ← l.mapM fun e => trLevel e.kind, mkAtom "}"]
  | Expr.nat n => Quote.quote n
  | Expr.decimal n d => (scientificLitOfDecimal n d).get!
  | Expr.string s => Syntax.mkStrLit s
  | Expr.char c => Syntax.mkCharLit c
  | Expr.paren e => trExpr e.kind -- do `(($(← trExpr e.kind)))
  | Expr.sort ty st u => do
    match ty, if st then some Level._ else u.map Spanned.kind with
    | false, none => `(Sort)
    | false, some u => do `(Sort $(← trLevel u))
    | true, none => `(Type)
    | true, some u => do `(Type $(← trLevel u))
  | Expr.«→» lhs rhs => do `($(← trExpr lhs.kind) → $(← trExpr rhs.kind))
  | Expr.fun true #[⟨_, LambdaBinder.reg (Binder.binder _ none _ (some ty) _)⟩] e => do
    `(fun $(mkIdent `this):ident: $(← trExpr ty.kind) => $(← trExpr e.kind))
  | Expr.fun _ bis e => do
    let bis ← bis.foldlM (fun out bi => trLambdaBinder bi.kind out) #[]
    `(fun $bis* => $(← trExpr e.kind))
  | Expr.Pi #[] e => trExpr e.kind
  | Expr.Pi bis e => do
    -- let dArrowHeuristic := !bis.any fun | ⟨_, Binder.binder _ _ _ none _⟩ => true | _ => false
    let dArrowHeuristic := false
    if dArrowHeuristic then trDArrow bis e.kind else
      let bc := { allowSimple := some false }
      trExtendedBindersGrouped
        (fun args e => Id.run `(∀ $args*, $e))
        (fun v pred e => Id.run `(∀ $v:ident $pred:binderPred, $e))
        bc (← trBinders' bc bis) e.kind
  | e@(Expr.app _ _) => do
    let (f, args) ← trAppArgs e trExpr
    mkNode ``Parser.Term.app #[f, mkNullNode args]
  | Expr.show t pr => do
    mkNode ``Parser.Term.show #[mkAtom "show", ← trExpr t.kind, ← trProof pr.kind]
  | Expr.have true h t pr e => do
    let decl := mkNode ``Parser.Term.sufficesDecl #[
      mkOptionalNode' h fun h => #[mkIdent h.kind, mkAtom ":"], ← trExpr t.kind, ← trProof pr.kind]
    mkNode ``Parser.Term.suffices #[mkAtom "suffices", decl, mkNullNode, ← trExpr e.kind]
  | Expr.have false h t pr e => do
    let t := match t.kind with | Expr._ => none | t => some t
    let haveId := mkNode ``Parser.Term.haveIdDecl #[
      mkOptionalNode' h fun h => #[mkIdent h.kind, mkNullNode],
      mkOptionalNode $ ← trOptType t, mkAtom ":=", ← trProof pr.kind false]
    mkNode ``Parser.Term.have #[mkAtom "have",
      mkNode ``Parser.Term.haveDecl #[haveId], mkNullNode, ← trExpr e.kind]
  | Expr.«.» _ e pr => do
    let pr ← match pr.kind with
    | Lean3.Proj.ident e => mkIdentF e
    | Lean3.Proj.nat n => Syntax.mkLit fieldIdxKind (toString n)
    mkNode ``Parser.Term.proj #[← trExpr e.kind, mkAtom ".", pr]
  | Expr.if none c t e => do
    `(if $(← trExpr c.kind) then $(← trExpr t.kind) else $(← trExpr e.kind))
  | Expr.if (some h) c t e => do
    `(if $(mkIdent h.kind):ident : $(← trExpr c.kind)
      then $(← trExpr t.kind) else $(← trExpr e.kind))
  | Expr.calc args => do `(calc $(← trCalcArgs args)*)
  | Expr.«@» _ e => do `(@$(← trExpr e.kind))
  | Expr.pattern e => trExpr e.kind
  | Expr.«`()» _ true e => do `(quote $(← trExpr e.kind))
  | Expr.«`()» false false e => do `(pquote $(← trExpr e.kind))
  | Expr.«`()» true false e => do `(ppquote $(← trExpr e.kind))
  | Expr.«%%» e => do `(%%ₓ$(← trExpr e.kind))
  | Expr.«`[]» tacs => do
    warn! "warning: unsupported (TODO): `[tacs]"
    `(sorry)
  | Expr.«`» false n => Quote.quote n
  | Expr.«`» true n => do `(``$(← mkIdentI n):ident)
  | Expr.«⟨⟩» es => do `(⟨$(← es.mapM fun e => trExpr e.kind),*⟩)
  | Expr.infix_fn n e => trInfixFn n e
  | Expr.«(,)» es => do
    `(($(← trExpr es[0].kind):term, $(← es[1:].toArray.mapM fun e => trExpr e.kind),*))
  | Expr.«.()» e => trExpr e.kind
  | Expr.«:» e ty => do `(($(← trExpr e.kind) : $(← trExpr ty.kind)))
  | Expr.hole es => warn! "unsupported: \{! ... !}"
  | Expr.«#[]» es => warn! "unsupported: #[...]"
  | Expr.by tac => do `(by $(← trTactic tac.kind TacticContext.seq):tacticSeq)
  | Expr.begin tacs => do `(by $(← trBlock tacs):tacticSeq)
  | Expr.let bis e => do
    bis.foldrM (init := ← trExpr e.kind) fun bi stx => do
      `(let $(← trLetDecl bi.kind):letDecl $stx)
  | Expr.match #[x] _ #[] => do `(nomatch $(← trExpr x.kind))
  | Expr.match xs _ #[] => do `(match $[$(← xs.mapM fun x => trExpr x.kind):term],* with.)
  | Expr.match xs ty eqns => do
    `(match $[$(← xs.mapM fun x => trExpr x.kind):term],* with $[$(← eqns.mapM trArm):matchAlt]*)
  | Expr.do _ els => do let els ← els.mapM fun e => trDoElem e.kind; `(do $[$els:doElem]*)
  | Expr.«{,}» es => do `({$(← es.mapM fun e => trExpr e.kind),*})
  | Expr.subtype false x ty p => do
    `({$(mkIdent x.kind) $[: $(← ty.mapM fun e => trExpr e.kind)]? // $(← trExpr p.kind)})
  | Expr.subtype true x none p => do `({$(mkIdent x.kind) | $(← trExpr p.kind)})
  | Expr.subtype true x (some ty) p => do
    `({ $(mkIdent x.kind):ident : $(← trExpr ty.kind):term | $(← trExpr p.kind):term })
  | Expr.sep x ty p => do
    `({$(mkIdent x.kind) ∈ $(← trExpr ty.kind) | $(← trExpr p.kind)})
  | stx@(Expr.setReplacement e bis) => do
    warn!"unsupported set replacement {repr stx}"
    -- `({$(← trExpr e.kind) | $[$(← trBinders {} bis):bracketedBinder]*})
  | Expr.structInst _ src flds srcs catchall => do
    let srcs := match src with | none => srcs | some src => #[src] ++ srcs
    let srcs : Array _ ← srcs.mapM fun s => trExpr s.kind
    let srcs := if srcs.isEmpty then none else some srcs
    let flds ← flds.mapM fun (⟨_, lhs⟩, ⟨_, rhs⟩) => do
      if (match rhs with | Expr.ident rhs => rhs == lhs | _ => false : Bool) then
        `(Parser.Term.structInstFieldAbbrev| $(← mkIdentF lhs):ident)
      else
        `(Parser.Term.structInstField| $(← mkIdentF lhs):ident := $(← trExpr rhs))
    -- TODO(Mario): formatter has trouble if you omit the commas
    if catchall then
      `({ $[$srcs,* with]? $[$flds:structInstField, ]* .. })
    else if let some last := flds.back? then
      `({ $[$srcs,* with]? $[$(flds.pop):structInstField, ]* $last:structInstField })
    else
      `({ $[$srcs,* with]? })
  | Expr.atPat lhs rhs => do `($(mkIdent lhs.kind)@ $(← trExpr rhs.kind))
  | Expr.notation n args => trNotation n args
  | Expr.userNotation n args => do
    match (← get).userNotas.find? n with
    | some f => try f args catch e => warn! "in {n}: {← e.toMessageData.toString}"
    | none => warn! "unsupported user notation {n}"

def mkSimpleAttr (n : Name) (args : Array Syntax := #[]) :=
  mkNode ``Parser.Attr.simple #[mkIdent n, mkNullNode args]

def trDerive (e : AST3.Expr) : M Name :=
  match e.unparen with
  | Expr.ident n => renameIdent n
  | e => warn! "unsupported derive handler {repr e}"

inductive TrAttr
  | del : Syntax → TrAttr
  | add : Syntax → TrAttr
  | prio : Expr → TrAttr
  | parsingOnly : TrAttr
  | irreducible : TrAttr
  | derive : Array Name → TrAttr

def trAttr (prio : Option Expr) : Attribute → M (Option TrAttr)
  | Attribute.priority n => TrAttr.prio n.kind
  | Attribute.del n => do
    let n ← match n with
    | `instance => `instance
    | `simp => `simp
    | `congr => `congr
    | `inline => `inline
    | `pattern => `matchPattern
    | _ =>
      warn! "warning: unsupported attr -{n}"
      return none
    TrAttr.del (← `(Parser.Command.eraseAttr| -$(← mkIdentI n)))
  | AST3.Attribute.add `parsing_only none => TrAttr.parsingOnly
  | AST3.Attribute.add `irreducible none => TrAttr.irreducible
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
    | `refl,          none => mkSimpleAttr `refl
    | `symm,          none => mkSimpleAttr `symm
    | `trans,         none => mkSimpleAttr `trans
    | `subst,         none => mkSimpleAttr `subst
    | `congr,         none => mkSimpleAttr `congr
    | `inline,        none => mkSimpleAttr `inline
    | `pattern,       none => mkSimpleAttr `matchPattern
    | `reducible,     none => mkSimpleAttr `reducible
    | `semireducible, none => mkSimpleAttr `semireducible
    | `irreducible,   none => mkSimpleAttr `irreducible
    | `elab_simple,   none => mkSimpleAttr `elabWithoutExpectedType
    | `vm_override,   some ⟨_, AttrArg.vmOverride n none⟩ =>
      mkSimpleAttr `implementedBy #[← mkIdentI n.kind]
    | `derive,        some ⟨_, AttrArg.user _ args⟩ =>
      return TrAttr.derive $ ← (← Parser.pExprListOrTExpr.run' args).mapM trDerive
    | _, none => mkSimpleAttr (← renameAttr n)
    | _, some ⟨_, AttrArg.user e args⟩ =>
      match (← get).userAttrs.find? n, args with
      | some f, _ =>
        try f #[Spanned.dummy (AST3.Param.parse e args)]
        catch e => warn! "in {n}: {← e.toMessageData.toString}"
      | none, #[] => mkSimpleAttr (← renameAttr n)
      | none, _ => warn! "unsupported user attr {n}"
    | _, _ =>
      warn! "warning: suppressing unknown attr {n}"
      return none
    TrAttr.add attr

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
  | none => mkNullNode
  | some a => do mkNullNode #[← f a]

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
    | Modifier.mutual => s -- mutual is duplicated elsewhere in the grammar
    | Modifier.attr loc _ attrs => do
      let kind := if loc then AttributeKind.local else AttributeKind.global
      pure { s with attrs := (← trAttributes attrs false kind |>.run ({}, #[])).2 }
    | Modifier.doc doc => match s.docComment with
      | none => pure { s with docComment := some doc }
      | _ => throw! "unsupported (impossible)"
  toSyntax : Modifiers4 → M (SpecialAttrs × Syntax)
  | ⟨doc, (s, attrs), vis, nc, safety⟩ => do
    let doc := mkOptionalNode $ doc.map trDocComment
    let attrs ← mkOpt (if attrs.isEmpty then none else some attrs) fun attrs =>
      `(Parser.Term.attributes| @[$attrs,*])
    let vis := mkOptionalNode $ ← match vis with
    | Visibility.regular => none
    | Visibility.private => `(Parser.Command.visibility| private)
    | Visibility.protected => `(Parser.Command.visibility| protected)
    let nc ← mkOpt nc fun () => `(Parser.Command.noncomputable| noncomputable)
    let part := mkOptionalNode $ ← match safety with
    | DefinitionSafety.partial => some <$> `(Parser.Command.partial| partial)
    | _ => none
    let uns := mkOptionalNode $ ← match safety with
    | DefinitionSafety.unsafe => some <$> `(Parser.Command.unsafe| unsafe)
    | _ => none
    (s, mkNode ``Parser.Command.declModifiers #[doc, attrs, vis, nc, uns, part])

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
          pushElab $ ← `(command| open $(mkIdent tgt.kind):ident ($ns*))
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
  `(Parser.Command.declId| $(← mkIdentI n):ident $[.{$us,*}]?)

def trDeclSig (req : Bool) (bis : Binders) (ty : Option (Spanned Expr)) : M Syntax := do
  let bis := mkNullNode (← trBinders { allowSimple := some true } bis)
  let ty := ty.map Spanned.kind
  let ty ← trOptType $ if req then some (ty.getD Expr.«_») else ty
  if req then mkNode ``Parser.Command.declSig #[bis, ty.get!]
  else mkNode ``Parser.Command.optDeclSig #[bis, mkOptionalNode ty]

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
  | DeclVal.expr e => do `(Parser.Command.declValSimple| := $(← trExpr e))
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
    let ds := match s.derive with | #[] => none | ds => some (ds.map mkIdent)
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
  | some InferKind.none => none
  | none => none

def trOptDeriving : Array Name → M Syntax
  | #[] => `(Parser.Command.optDeriving|)
  | ds => `(Parser.Command.optDeriving| deriving $[$(ds.map mkIdent):ident],*)

def trInductive (cl : Bool) (mods : Modifiers) (n : Spanned Name) (us : LevelDecl)
  (bis : Binders) (ty : Option (Spanned Expr))
  (nota : Option Notation) (intros : Array (Spanned Intro)) : M Syntax := do
  let (s, mods) ← trModifiers mods
  let id ← trDeclId n.kind us
  let sig ← trDeclSig false bis ty
  let ctors ← intros.mapM fun ⟨_, ⟨doc, name, ik, bis, ty⟩⟩ => do
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

def trField : Field → Array Syntax → M (Array Syntax)
  | Field.binder bi ns ik bis ty dflt, out => do
    let ns ← ns.mapM fun n => mkIdentF n.kind
    let im ← trInferKind ik
    let sig req := trDeclSig req bis ty
    out.push <$> match bi with
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
  | Field.notation _, out => warn! "unsupported: (notation) in structure"

def trFields (flds : Array (Spanned Field)) : M Syntax := do
  let flds ← flds.foldlM (fun out fld => trField fld.kind out) #[]
  mkNode ``Parser.Command.structFields #[mkNullNode flds]

def trStructure (cl : Bool) (mods : Modifiers) (n : Spanned Name) (us : LevelDecl)
  (bis : Binders) (exts : Array (Spanned Parent)) (ty : Option (Spanned Expr))
  (mk : Option (Spanned Mk)) (flds : Array (Spanned Field)) : M Unit := do
  let (s, mods) ← trModifiers mods
  let id ← trDeclId n.kind us
  let bis := mkNullNode $ ← trBinders {} bis
  let exts ← exts.mapM fun
    | ⟨_, false, none, ty, #[]⟩ => trExpr ty.kind
    | _ => warn! "unsupported: advanced extends in structure"
  let exts ← mkOpt (if exts.isEmpty then none else some exts) fun exts =>
    `(Parser.Command.extends| extends $exts,*)
  let ty ← mkOptionalNode <$> trOptType (ty.map Spanned.kind)
  let flds ← @mkNullNode <$> match mk, flds with
  | none, #[] => #[]
  | mk, flds => do
    let mk ← mk.mapM fun ⟨_, n, ik⟩ => do
      `(Parser.Command.structCtor| $(← mkIdentF n.kind):ident $[$(← trInferKind ik)]? ::)
    #[mkAtom "where", mkOptionalNode mk, ← trFields flds]
  let decl := mkNode ``Parser.Command.structure #[
    ← if cl then `(Parser.Command.classTk| class) else `(Parser.Command.structureTk| structure),
    id, bis, exts, ty, flds, ← trOptDeriving s.derive]
  pushM `(command| $mods:declModifiers $decl:structure)

partial def mkUnusedName [Monad m] [MonadResolveName m] [MonadEnv m]
  (baseName : Name) : m Name := do
  let ns ← getCurrNamespace
  let env ← getEnv
  if env.contains (ns ++ baseName) then
    let rec loop (idx : Nat) := do
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
  out

private def isIdentPrec : AST3.Literal → Bool
  | AST3.Literal.sym _ => true
  | AST3.Literal.var _ none => true
  | AST3.Literal.var _ (some ⟨_, Action.prec _⟩) => true
  | _ => false

private def trMixfix (kind : Syntax) (prio : Option Syntax)
  (m : AST3.MixfixKind) (tk : String) (prec : Option (Spanned AST3.Precedence)) :
  M (NotationDesc × (Option Syntax → Syntax → Id Syntax)) := do
  let p ← match prec with
  | some p => trPrec p.kind
  | none => (← getPrecedence? tk m).getD (Precedence.nat 0)
  let p := p.toSyntax
  let s := Syntax.mkStrLit tk
  match m with
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
  | ⟨_, AST3.Literal.sym tk⟩ => Syntax.mkStrLit tk.1.kind.toString
  | ⟨_, AST3.Literal.var x none⟩ =>
    `(Parser.Command.identPrec| $(mkIdent x.kind):ident)
  | ⟨_, AST3.Literal.var x (some ⟨_, Action.prec p⟩)⟩ => do
    `(Parser.Command.identPrec| $(mkIdent x.kind):ident : $((← trPrec p).toSyntax))
  | _ => warn! "unsupported (impossible)"
  pure fun n e => `(command|
    $kind:attrKind notation$[:$p]? $[$n:namedName]? $[$prio:namedPrio]? $lits* => $e)

private def trNotation3Item (lit : AST3.Literal) : M Syntax := do
  let stxs ← match lit with
  | AST3.Literal.sym tk => sym tk
  | AST3.Literal.binder _ => binders
  | AST3.Literal.binders _ => binders
  | AST3.Literal.var x none => var x
  | AST3.Literal.var x (some ⟨_, Action.prec _⟩) => var x
  | AST3.Literal.var x (some ⟨_, Action.prev⟩) => var x
  | AST3.Literal.var x (some ⟨_, Action.scoped _ sc⟩) => scope x sc
  | _ => warn! "unsupported: advanced notation ({repr lit})"
  mkNode ``Parser.Command.notation3Item stxs
where
  sym tk := #[Syntax.mkStrLit tk.1.kind.toString]
  var x := #[mkIdent x.kind, mkNullNode]
  binders := #[mkNode ``Parser.Command.bindersItem #[mkAtom "(", mkAtom "...", mkAtom ")"]]
  scope x sc := do
    let (p, e) := match sc with
    | none => (`x, Expr.ident `x)
    | some (p, e) => (p.kind, e.kind)
    #[mkIdent x.kind, mkNullNode #[
      mkNode ``Parser.Command.identScope #[
        mkAtom ":", mkAtom "(", mkAtom "scoped",
        mkIdent p, mkAtom "=>", ← trExpr e, mkAtom ")"]]]

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
  let lits ← lits.mapM trNotation3Item
  pure fun n e => `(command|
    $kind:attrKind notation3$[:$p]? $[$n:namedName]? $[$prio:namedPrio]? $lits* => $e)

def trNotationCmd (loc : LocalReserve) (attrs : Attributes) (nota : Notation)
  (f : Syntax → M Unit) : M Unit := do
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
    (e, ← trMixfix kind prio m tk.kind.toString prec)
  | Notation.notation lits (some e) =>
    let p ← match lits.get? 0 with
    | some ⟨_, AST3.Literal.sym tk⟩ => tk.2
    | some ⟨_, AST3.Literal.var _ _⟩ => match lits.get? 1 with
      | some ⟨_, AST3.Literal.sym tk⟩ => tk.2
      | _ => none
    | _ => none
    let p ← p.mapM fun p => do (← trPrec p.kind).toSyntax
    let desc := match lits with
    | #[⟨_, AST3.Literal.sym tk⟩] => NotationDesc.const tk.1.kind.toString
    | _ => match mkNAry lits with
      | some lits => NotationDesc.nary lits
      | none => NotationDesc.fail
    let cmd ← match lits.all fun lit => isIdentPrec lit.kind with
    | true => trNotation4 kind prio p lits
    | false => trNotation3 kind prio p lits
    (e, desc, cmd)
  | _ => warn! "unsupported (impossible)"
  let e ← trExpr e.kind
  let n4 ← Elab.Command.withWeakNamespace (← getEnv).mainModule $ do
    let n4 ← mkUnusedName nota.name4
    let nn ← `(Parser.Command.namedName| (name := $(mkIdent n4)))
    try elabCommand $ cmd (some nn) e
    catch e => dbg_trace "warning: failed to add syntax {repr n4}: {← e.toMessageData.toString}"
    pure $ (← getCurrNamespace) ++ n4
  f $ cmd none e
  registerNotationEntry loc.1 ⟨n, n4, desc⟩

end

def trInductiveCmd : InductiveCmd → M Unit
  | InductiveCmd.reg cl mods n us bis ty nota intros =>
     pushM $ trInductive cl mods n us bis ty nota intros
  | InductiveCmd.mutual cl mods us bis nota inds =>
    trMutual inds fun ⟨attrs, n, ty, intros⟩ => do
      trInductive cl mods n us bis ty nota intros

def trAttributeCmd (loc : Bool) (attrs : Attributes) (ns : Array (Spanned Name))
  (f : Syntax → M Unit) : M Unit := do
  if ns.isEmpty then return ()
  let kind := if loc then AttributeKind.local else AttributeKind.global
  let (s, attrs) := (← trAttributes attrs true kind |>.run ({}, #[])).2
  let ns ← ns.mapM fun n => mkIdentI n.kind
  unless s.derive.isEmpty do
    f $ ← `(command| deriving instance $[$(s.derive.map mkIdent):ident],* for $ns,*)
  unless attrs.isEmpty do
    f $ ← `(command| attribute [$attrs,*] $ns*)

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
  | Command.attribute loc _ attrs ns => trAttributeCmd loc attrs ns push
  | Command.precedence sym prec => warn! "warning: unsupported: precedence command"
  | Command.notation loc attrs n => trNotationCmd loc attrs n push
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
    warn! "ignoring doc comment on noncomputable theory"
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
  | Command.runCmd e => do let e ← trExpr e.kind; pushM `(run_cmd $e:term)
  | Command.check e => do pushM `(#check $(← trExpr e.kind))
  | Command.reduce _ e => do pushM `(#reduce $(← trExpr e.kind))
  | Command.eval e => do pushM `(#eval $(← trExpr e.kind))
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
