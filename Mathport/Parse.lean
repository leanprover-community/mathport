/-
Copyright (c) 2021 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Daniel Selsam
-/
import Lean.Expr
import Mathport.Util
import Mathport.AST3

namespace Mathport

open Lean (Json FromJson Position Name BinderInfo)
open Lean.FromJson (fromJson?)

namespace Parse

abbrev AstId := Nat
abbrev LevelId := Nat
abbrev ExprId := Nat
abbrev Tag := Option AstId

structure RawNode3 where
  start    : Position
  «end»    : Option Position
  kind     : String
  value    : Name
  children : Option (Array AstId)
  pexpr    : Option ExprId
  expr     : Option ExprId
  deriving FromJson, Repr

def RawNode3.children' (n : RawNode3) : Array AstId := n.children.getD #[]
def RawNode3.end' (n : RawNode3) : Position := n.end.getD n.start

section
open AST3
open Lean3 (Proj)

structure Context where
  ast : Array (Option RawNode3)
  expr : Array Lean3.Expr

abbrev M := ReaderT Context $ Except String

def RawNode3.map (n : RawNode3) (f : String → Name → Array AstId → M α) : M (Spanned α) := do
  pure ⟨n.start, n.end', ← f n.kind n.value n.children'⟩

def RawNode3.pexpr' (n : RawNode3) : M Lean3.Expr :=
  match n.pexpr with
  | none => arbitrary
  | some e => do (← read).expr[e]

def RawNode3.expr' (n : RawNode3) : M Lean3.Expr :=
  match n.expr with
  | none => arbitrary
  | some e => do (← read).expr[e]

def opt (f : AstId → M α) (i : AstId) : M (Option α) :=
  if i = 0 then pure none else some <$> f i

def getRaw (i : AstId) : M RawNode3 := do
  match (← read).ast[i] with
  | some a => a
  | none => throw $ if i = 0 then "unexpected null node" else "missing node"

def withNodeK (f : String → Name → Array AstId → M α) (i : AstId) : M α := do
  let r ← getRaw i
  f r.kind r.value r.children'

def withNode (f : String → Name → Array AstId → M α) (i : AstId) : M (Spanned α) := do
  let r ← getRaw i
  pure { start := r.start, end_ := r.end', kind := ← f r.kind r.value r.children' }

def withNodeR (f : RawNode3 → M α) (i : AstId) : M (Spanned α) := do
  let r ← getRaw i
  pure { start := r.start, end_ := r.end', kind := ← f r }

def getRaw? : AstId → M (Option RawNode3) := opt getRaw

inductive NodeK : Type
  | mk (kind : String) (value : Name) (children : Array (Option (Spanned NodeK))) : NodeK
  deriving Inhabited

def Node := Spanned NodeK
instance : Inhabited Node := inferInstanceAs (Inhabited (Spanned NodeK))

open Std (Format) in
mutual

partial def optNode_repr : Option Node → Format
  | none => ("⬝" : Format)
  | some a => NodeK_repr a.kind

partial def NodeK_repr : NodeK → Format
  | ⟨k, v, c⟩ =>
    let s := (Lean.Name.escapePart k).getD k ++
      if v.isAnonymous then "" else "[" ++ v.toString ++ "]"
    if c.isEmpty then s else
      "(" ++ s ++ Format.join (c.toList.map fun c => Format.line ++ optNode_repr c) ++ ")"
        |>.nest 2 |>.group

end

instance : Repr NodeK := ⟨fun n _ => NodeK_repr n⟩
instance : Repr Node := inferInstanceAs (Repr (Spanned NodeK))

mutual

partial def getNode : AstId → M Node := withNode mkNodeK

partial def mkNodeK (k : String) (v : Name) (c : Array AstId) : M NodeK := NodeK.mk k v <$> c.mapM (opt getNode)

end

def decodeNat! (v : Name) : Nat :=
  (Lean.Syntax.decodeNatLitVal? v.getString!).get!

def decodeDecimal! (v : Name) : Nat × Nat :=
  match String.split v.getString! (· = '/') with
  | [n, d] => ((Lean.Syntax.decodeNatLitVal? n).get!, (Lean.Syntax.decodeNatLitVal? d).get!)
  | _ => panic! "decodeDecimal! failed"

def getNat : AstId → M (Spanned Nat) := withNode fun _ v _ => decodeNat! v

def getNameK : AstId → M Name := withNodeK fun _ v _ => v
def getName : AstId → M (Spanned Name) := withNode fun _ v _ => v

def getStrK : AstId → M String := withNodeK fun _ v _ => v.getString!
def getStr : AstId → M (Spanned String) := withNode fun _ v _ => v.getString!

def getSym : AstId → M (Spanned Symbol) :=
  withNode fun
  | "quoted", v, _ => Symbol.quoted v.getString!
  | "ident", v, _ => Symbol.ident v.getString!
  | k, _, _ => throw s!"getSym parse error, unknown kind {k}"

def getChoice : AstId → M Choice :=
  withNodeK fun
  | "choice", _, args => Choice.many <$> args.mapM getNameK
  | "notation", v, _ => Choice.one v
  | k, _, _ => throw s!"getChoice parse error, unknown kind {k}"

def getProj : AstId → M (Spanned Proj) :=
  withNode fun
  | "nat", v, _ => Proj.nat (decodeNat! v)
  | "ident", v, _ => Proj.ident v.getString!
  | k, _, _ => throw s!"getSym parse error, unknown kind {k}"

def getOptionVal : AstId → M (Spanned OptionVal) :=
  withNode fun
  | "nat", v, _ => OptionVal.nat (decodeNat! v)
  | "ident", v, _ => OptionVal.str v.getString!
  | "bool", v, _ => OptionVal.bool (v == `true)
  | "decimal", v, _ => let (n, d) := decodeDecimal! v; OptionVal.decimal n d
  | k, _, _ => throw s!"getOptionVal parse error, unknown kind {k}"

def getInferKind : AstId → M InferKind :=
  withNodeK fun
  | "{}", _, _ => InferKind.relaxedImplicit
  | "()", _, _ => InferKind.none
  | "[]", _, _ => InferKind.implicit
  | k, _, _ => throw s!"getInferKind parse error, unknown kind {k}"

def arr (f : AstId → M α) (i : AstId) : M (Array α) := do
  match ← getRaw? i with
  | some n => n.children'.mapM f
  | none => pure #[]

def ctx (s : String) (m : M α) : M α := do
  try m catch e => throw $ "at " ++ s ++ ": " ++ e

abbrev NotationKind := Option MixfixKind

def toNotationKind : String → Option NotationKind
| "infix" => some (some MixfixKind.infix)
| "infixl" => some (some MixfixKind.infixl)
| "infixr" => some (some MixfixKind.infixr)
| "postfix" => some (some MixfixKind.postfix)
| "prefix" => some (some MixfixKind.prefix)
| "notation" => some none
| _ => none

open Level in
partial def getLevel : AstId → M (Spanned Level) :=
  withNode fun
  | "_", _, _ => «_»
  | "param", v, _ => «param» v
  | "max", _, args => Level.«max» <$> args.mapM getLevel
  | "imax", _, args => Level.«imax» <$> args.mapM getLevel
  | "nat", v, _ => Level.nat $ decodeNat! v
  | "+", _, args => do Level.add (← getLevel args[0]) (← getNat args[1])
  | "(", _, args => Level.paren <$> getLevel args[0]
  | k, _, _ => throw s!"getLevel parse error, unknown kind {k}"

def getLevels : AstId → M Levels := opt (arr getLevel)
def getLevelDecl : AstId → M LevelDecl := opt (arr getName)

def wrapperNotations : Lean.NameHashSet :=
  List.foldl (·.insert ·) {} [
    `by, `have, `assume, `show, `suffices, `if, `«(», `«⟨», `«{», `«{!», `«.(», `«._»,
    `«```(», `«``(», `«`(», `«`[», `«`», `«%%», `«#[», `«(:», `«(::)», `fun, `Type,
    `«Type*», `Sort, `«Sort*», `let, `calc, `«@», `«@@», `begin, `sorry, `match, `do, `«^.»]

mutual

partial def getArg : AstId → M (Spanned Arg) :=
  withNode fun
  | "exprs", _, args => Arg.exprs <$> args.mapM getExpr
  | "binders", _, args => Arg.binders <$> args.mapM getBinder
  | k, v, args => if k.startsWith "binder"
    then Arg.binder <$> getBinder_aux k v args
    else Arg.expr <$> getExpr_aux k v args

partial def getExpr : AstId → M (Spanned Expr) := withNode getExpr_aux

partial def getExpr_aux : String → Name → Array AstId → M Expr
  | "notation", v, args => match v with
    | `«->» => do Expr.«→» (← getExpr args[0]) (← getExpr args[1])
    | `Pi => do Expr.«Pi» (← getBinders args[0]) (← getExpr args[1])
    | _ => if wrapperNotations.contains v
      then Spanned.kind <$> getExpr args[0]
      else Expr.notation (Choice.one v) <$> args.mapM getArg
  | "sorry", _, _ => Expr.«sorry»
  | "_", _, _ => Expr.«_»
  | "()", _, _ => Expr.«()»
  | "{}", _, _ => Expr.«{}»
  | "ident", v, _ => Expr.ident v
  | "const", _, args => do Expr.const false (← getName args[0]) (← opt (arr getLevel) args[1])
  | "choice_const", _, args => do Expr.const true (← getName args[0]) (← opt (arr getLevel) args[1])
  | "nat", v, _ => Expr.nat $ decodeNat! v
  | "decimal", v, _ => let (n, d) := decodeDecimal! v; Expr.decimal n d
  | "string", v, _ => Expr.string v.getString!
  | "char", v, _ => Expr.char v.getString!.front
  | "(", _, args => Expr.paren <$> getExpr args[0]
  | "Sort*", _, _ => Expr.sort false true none
  | "Type*", _, _ => Expr.sort true true none
  | "Sort", _, args => Expr.sort false false <$> opt getLevel args[0]
  | "Type", _, args => Expr.sort true false <$> opt getLevel args[0]
  | "app", _, args => do Expr.app (← getExpr args[0]) (← getExpr args[1])
  | "fun", _, args => do Expr.fun false (← getBinders args[0]) (← getExpr args[1])
  | "assume", _, args => do Expr.fun true (← getBinders args[0]) (← getExpr args[1])
  | "show", _, args => do Expr.show (← getExpr args[0]) (← getProof args[1])
  | "have", _, args => getHave false args
  | "suffices", _, args => getHave true args
  | "field", _, args => do Expr.«.» true (← getExpr args[0]) (← getProj args[1])
  | "^.", _, args => do Expr.«.» false (← getExpr args[0]) (← getProj args[1])
  | "if", _, args => do {Expr.if (← opt getName args[0])
      (← getExpr args[1]) (← getExpr  args[2]) (← getExpr args[3])}
  | "calc", _, args => Expr.calc <$> args.mapM getStep
  | "@", _, args => Expr.«@» false <$> getExpr args[0]
  | "@@", _, args => Expr.«@» true <$> getExpr args[0]
  | "(:", _, args => Expr.pattern <$> getExpr args[0]
  | "```()", _, args => Expr.«`()» true false <$> getExpr args[0]
  | "``()", _, args => Expr.«`()» false false <$> getExpr args[0]
  | "`()", _, args => Expr.«`()» false true <$> getExpr args[0]
  | "%%", _, args => Expr.«%%» <$> getExpr args[0]
  | "`[", _, args => Expr.«`[]» <$> args.mapM getTactic
  | "`", v, _ => Expr.«`» false v
  | "``", v, _ => Expr.«`» true v
  | "⟨", _, args => Expr.«⟨⟩» <$> args.mapM getExpr
  | "infix_fn", _, args => do Expr.infix_fn (← getChoice args[0]) (← opt getExpr args[1])
  | "tuple", _, args => Expr.«(,)» <$> args.mapM getExpr
  | ":", _, args => do Expr.«:» (← getExpr args[0]) (← getExpr args[1])
  | "{!", _, args => Expr.hole <$> args.mapM getExpr
  | "#[", _, args => Expr.«#[]» <$> args.mapM getExpr
  | "by", _, args => Expr.by <$> getTactic args[0]
  | "begin", _, args => Expr.begin <$> getBlock false args
  | "let", _, args => do Expr.let (← getBinders args[0]) (← getExpr args[1])
  | "match", _, args => do
    Expr.match (← arr getExpr args[0]) (← opt getExpr args[1]) (← arr getArm args[2])
  | "do", v, args => Expr.do (!v.isAnonymous) <$> args.mapM getDoElem
  | "fin_set", _, args => Expr.«{,}» <$> args.mapM getExpr
  | "subtype", _, args => getSubtype false args
  | "set_of", _, args => getSubtype true args
  | "sep", _, args => do Expr.sep (← getName args[0]) (← getExpr args[1]) (← getExpr args[2])
  | "set_replacement", _, args => do Expr.setReplacement (← getExpr args[0]) (← getBinders args[1])
  | "structinst", _, args => do
    Expr.structInst (← opt getName args[0]) (← opt getExpr args[1])
      (← arr getField args[2]) (← arr getExpr args[3]) (args[4] ≠ 0)
  | "at_pat", _, args => do Expr.atPat (← getExpr args[0]) (← getExpr args[1])
  | ".(", _, args => Expr.«.()» <$> getExpr args[0]
  | "...", _, _ => Expr.«...»
  | "choice", _, args => do
    Expr.notation (Choice.many (← arr getNameK args[0])) (← args[1:].toArray.mapM getArg)
  | "user_notation", v, args => Expr.userNotation v <$> args.mapM getParam
  | k, v, args => do
    throw s!"getExpr parse error, unknown kind {k}" -- at\n {repr (← Expr.other <$> mkNodeK k v args)}"
where
  getHave (suff : Bool) (args) : M _ := do
    Expr.have suff (← opt getName args[0])
      (← getExpr args[1]) (← getProof args[2]) (← getExpr args[3])
  getStep := withNodeK fun _ _ args => do pure (← getExpr args[0], ← getExpr args[1])
  getField := withNodeK fun _ _ args => do pure (← getName args[0], ← getExpr args[1])
  getSubtype (setOf : Bool) (args) : M _ := do
    Expr.subtype setOf (← getName args[0]) (← opt getExpr args[1]) (← getExpr args[2])

partial def getBinder : AstId → M (Spanned Binder) := withNode getBinder_aux

partial def getBinder_aux
  | "binder_0", _, args => binder BinderInfo.default args
  | "binder_1", _, args => binder BinderInfo.instImplicit args
  | "binder_2", _, args => binder BinderInfo.strictImplicit args
  | "binder_4", _, args => binder BinderInfo.implicit args
  | "binder_8", _, args => binder BinderInfo.auxDecl args
  | "⟨", _, args => Binder.«⟨⟩» <$> args.mapM getExpr
  | "var", _, args => do {Binder.var (← getName args[0])
    (← getBinders args[1]) (← opt getExpr args[2]) (← getExpr args[3])}
  | "pat", _, args => do {Binder.pat (← getExpr args[0]) (← getExpr args[1])}
  | k, v, args => match toNotationKind k with
    | some nk => Binder.notation <$> getNotationDef nk args
    | none => throw s!"getBinder parse error, unknown kind {k}"
where
  binder (bi : BinderInfo) (args : Array AstId) : M Binder := do
    Binder.binder bi (← opt (arr getName) args[0]) (← getBinders args[1]) (← opt getExpr args[2])

partial def getBinders : AstId → M Binders := arr getBinder

partial def getDoElem : AstId → M (Spanned DoElem) :=
  withNode fun
  | "let", _, args => DoElem.let <$> getBinder args[0]
  | "<-", _, args => do
    DoElem.«←» (← getExpr args[0]) (← opt getExpr args[1])
      (← getExpr args[2]) (← opt getExpr args[3])
  | "eval", _, args => DoElem.eval <$> getExpr args[0]
  | k, _, _ => throw s!"getDoElem parse error, unknown kind {k}"

partial def getProof : AstId → M (Spanned Proof) :=
  withNode fun
  | ":=", _, args => Proof.from true <$> getExpr args[0]
  | "from", _, args => Proof.from false <$> getExpr args[0]
  | "begin", _, args => Proof.block <$> getBlock false args
  | "{", _, args => Proof.block <$> getBlock true args
  | "by", _, args => Proof.by <$> getTactic args[0]
  | k, _, _ => throw s!"getProof parse error, unknown kind {k}"

partial def getTactic : AstId → M (Spanned Tactic) :=
  withNode fun
  | ";", _, args => Tactic.«;» <$> args.mapM getTactic
  | "<|>", _, args => Tactic.«<|>» <$> args.mapM getTactic
  | "[", _, args => Tactic.«[]» <$> args.mapM getTactic
  | "begin", _, args => Tactic.block <$> getBlock false args
  | "{", _, args => Tactic.block <$> getBlock true args
  | "by", _, args => Tactic.by <$> getTactic args[0]
  | "exact_shortcut", _, args => Tactic.exact_shortcut <$> getExpr args[0]
  | "(", _, args => Tactic.expr <$> getExpr args[0]
  | "tactic", v, args => Tactic.interactive v <$> args.mapM getParam
  | k, _, _ => throw s!"getTactic parse error, unknown kind {k}"

partial def getBlock (curly : Bool) (args : Array AstId) : M Block := do
  pure ⟨curly, ← opt getName args[0], ← opt getExpr args[1], ← args[2:].toArray.mapM getTactic⟩

partial def getParam : AstId → M (Spanned Param) :=
  withNodeR fun r => match r.kind with
  | "parse" => Param.parse <$> r.pexpr'
  | "expr" => Param.expr <$> getExpr r.children'[0]
  | "begin" => Param.block <$> getBlock false r.children'
  | "{" => Param.block <$> getBlock true r.children'
  | k => throw s!"getParam parse error, unknown kind {k}"

partial def getPrec : AstId → M (Spanned Precedence) :=
  withNode fun
  | "nat", v, _ => Precedence.nat $ decodeNat! v
  | "expr", _, args => Precedence.expr <$> getExpr args[0]
  | k, _, _ => throw s!"getPrec parse error, unknown kind {k}"

partial def getPrecSym : AstId → M PrecSymbol := withNodeK fun _ _ => getPrecSym_aux

partial def getPrecSym_aux (args : Array AstId) : M PrecSymbol := do
  (← getSym args[0], ← opt getPrec args[1])

partial def getAction : AstId → M (Spanned Action) :=
  withNode fun
  | "nat", v, _ => Action.prec $ Precedence.nat $ decodeNat! v
  | "expr", _, args => do Action.prec $ Precedence.expr $ ← getExpr args[0]
  | "prev", _, _ => Action.prev
  | "scoped", _, args => do
    let scope i := do let args := (← getRaw i).children'; (← getName args[0], ← getExpr args[1])
    Action.scoped (← opt getPrec args[0]) (← opt scope args[1])
  | "foldl", _, args => getFold false args
  | "foldr", _, args => getFold true args
  | k, _, _ => throw s!"getAction parse error, unknown kind {k}"
where
  getFold (r) (args : Array AstId) : M Action := do
    let sc := (← getRaw args[2]).children'
    Action.fold r
      (← opt getPrec args[0]) (← getPrecSym args[1])
      (← getName sc[0], ← getName sc[1], ← getExpr sc[2])
      (← opt getExpr args[3]) (← opt getPrecSym args[4])

partial def getLiteral : AstId → M (Spanned Literal) :=
  withNode fun
  | "nat", v, _ => Literal.nat $ decodeNat! v
  | "var", _, args => do Literal.var (← getName args[0]) (← opt getAction args[1])
  | "sym", _,  args => Literal.sym <$> getPrecSym_aux args
  | "binder", _, args => Literal.binder <$> opt getPrec args[0]
  | "binders", _, args => Literal.binders <$> opt getPrec args[0]
  | k, _, _ => throw s!"getLiteral parse error, unknown kind {k}"

partial def getNotationDef (nk : NotationKind) (args : Subarray AstId) : M Notation := do
  match nk with
  | some nk => Notation.mixfix nk (← getSym args[0], ← opt getPrec args[1]) (← opt getExpr args[2])
  | none => Notation.notation (← arr getLiteral args[0]) (← opt getExpr args[1])

partial def getNotation : AstId → M Notation :=
  withNodeK fun k _ a => getNotationDef (toNotationKind k).get! a

partial def getArm : AstId → M Arm := withNodeK fun _ _ args => do
  pure ⟨← arr getExpr args[0], ← getExpr args[1]⟩

end

partial def getField : AstId → M (Spanned Field) := withNode fun
  | "field_0", _, args => field BinderInfo.default args
  | "field_1", _, args => field BinderInfo.instImplicit args
  | "field_2", _, args => field BinderInfo.strictImplicit args
  | "field_4", _, args => field BinderInfo.implicit args
  | "field_8", _, args => field BinderInfo.auxDecl args
  | k, v, args => match toNotationKind k with
    | some nk => Field.notation <$> getNotationDef nk args
    | none => throw s!"getField parse error, unknown kind {k}"
where
  field (bi : BinderInfo) (args : Array AstId) : M Field := do
    Field.binder bi (← arr getName args[0])
      (← opt getInferKind args[1]) (← getBinders args[2]) (← opt getExpr args[3])

def getAttrArg : AstId → M (Spanned AttrArg) := withNodeR fun r =>
  match r.kind with
  | "!" => AttrArg.eager
  | "indices" => AttrArg.indices <$> r.children'.mapM getNat
  | "key_value" => do AttrArg.keyValue (← getStr r.children'[0]) (← getStr r.children'[1])
  | "vm_override" => do AttrArg.vmOverride (← getName r.children'[0]) (← opt getName r.children'[1])
  | "parse" => AttrArg.user <$> r.pexpr'
  | k => throw s!"getAttrArg parse error, unknown kind {k}"

def getAttr : AstId → M (Spanned Attribute) := withNode fun
  | "priority", _, args => do Attribute.priority <$> getExpr args[0]
  | "attr", v, args => Attribute.mk (args[0] ≠ 0) v <$> opt getAttrArg args[1]
  | k, _, _ => throw s!"getAttr parse error, unknown kind {k}"

open DeclVal in
def getDeclVal : AstId → M (Spanned DeclVal) :=
  withNode fun
  | "eqns", _, args => eqns <$> args.mapM getArm
  | k, v, args => expr <$> getExpr_aux k v args

open Modifier in
def getModifier : AstId → M (Spanned Modifier) := withNode fun
  | "private", _, _ => «private»
  | "protected", _, _ => «protected»
  | "noncomputable", _, _ => «noncomputable»
  | "meta", _, _ => «meta»
  | "mutual", _, _ => «mutual»
  | "doc", v, _ => doc v.getString!
  | "@[", _, args => attr false true <$> arr getAttr args[0]
  | "attribute", _, args => attr (args[0] ≠ 0) false <$> arr getAttr args[1]
  | k, _, _ => throw s!"getModifier parse error, unknown kind {k}"

def getModifiers : AstId → M Modifiers := arr getModifier

def getLocal (i : AstId) : M LocalReserve := do
  match (← getRaw? i).map fun n => n.kind with
  | some "local"   => (true, false)
  | some "reserve" => (false, true)
  | none           => (false, false)
  | _ => throw "getLocal parse error"

def getIntro : AstId → M (Spanned Intro) := withNode fun _ _ args => do
  pure ⟨← opt getStrK args[0], ← getName args[1],
    ← opt getInferKind args[2], ← getBinders args[3], ← opt getExpr args[4]⟩

def getRename : AstId → M Rename := withNodeK fun _ _ args => do
  pure ⟨← getName args[0], ← getName args[1]⟩

def getParent : AstId → M (Spanned Parent) := withNode fun _ _ args => do
  pure ⟨args[0] ≠ 0, ← opt getName args[1], ← getExpr args[2], ← arr getRename args[3]⟩

def getMk : AstId → M (Spanned Mk) := withNode fun _ _ args => do
  pure ⟨← getName args[0], ← opt getInferKind args[1]⟩

def getMutual {α} (f : AstId → M α) : AstId → M (Mutual α) := withNodeK fun _ _ args => do
  pure ⟨← arr getAttr args[0], ← getName args[1], ← getExpr args[2], ← arr f args[3]⟩

open OpenClause in
def getOpenClause : AstId → M (Spanned OpenClause) :=
  withNode fun
  | "explicit", _, args => explicit <$> args.mapM getName
  | "renaming", _, args => «renaming» <$> args.mapM getRename
  | "hiding", _, args => «hiding» <$> args.mapM getName
  | k, _, _ => throw s!"getOpenClause parse error, unknown kind {k}"

def getOpen : AstId → M Open := withNodeK fun _ _ args => do
  pure ⟨← getName args[0], ← opt getName args[1], ← args[2:].toArray.mapM getOpenClause⟩

open HelpCmd in
def getHelpCmd : AstId → M HelpCmd := withNodeK fun
  | "options", _, _ => options
  | "commands", _, _ => commands
  | k, _, _ => throw s!"getHelpCmd parse error, unknown kind {k}"

open PrintAttrCmd in
def getPrintAttrCmd : AstId → M (Spanned PrintAttrCmd) := withNode fun
  | "recursor", _, _ => recursor
  | "unify", _, _ => unify
  | "simp", _, _ => simp
  | "congr", _, _ => congr
  | "attr", v, _ => attr v
  | k, _, _ => throw s!"getPrintAttrCmd parse error, unknown kind {k}"

open PrintCmd in
def getPrintCmd (args : Array AstId) : M PrintCmd := do
  let r ← getRaw args[0]
  match r.kind with
  | "string" => str r.value.getString!
  | "raw" => raw <$> getExpr args[1]
  | "options" => options
  | "trust" => trust
  | "key_equivalences" => keyEquivalences
  | "definition" => «def» <$> getName args[1]
  | "instances" => instances <$> getName args[1]
  | "classes" => classes
  | "attributes" => attributes
  | "prefix" => «prefix» <$> getName args[1]
  | "aliases" => aliases
  | "axioms" => axioms <$> opt getName args[1]
  | "fields" => fields <$> getName args[1]
  | "notation" => «notation» <$> args.mapM getName
  | "inductive" => «inductive» <$> getName args[1]
  | "attribute" => attr <$> getPrintAttrCmd args[1]
  | "token" => token <$> r.map fun _ v _ => v
  | "ident" => ident <$> r.map fun _ v _ => v
  | k => throw s!"getPrintCmd parse error, unknown kind {k}"

open Command in
def getCommand : AstId → M (Spanned Command) :=
  withNode fun
  | "prelude", _, _ => «prelude»
  | "init_quotient", _, _ => initQuotient
  | "import", _, args => «import» <$> args.mapM getName
  | "mdoc", v, _ => mdoc v.getString!
  | "namespace", _, args => «namespace» <$> getName args[0]
  | "section", _, args => «section» <$> opt getName args[0]
  | "end", _, args => «end» <$> opt getName args[0]
  | "universe", _, args => «universe» false false <$> args.mapM getName
  | "universes", _, args => «universe» false true <$> args.mapM getName
  | "universe_variable", _, args => «universe» true false <$> args.mapM getName
  | "universe_variables", _, args => «universe» true true <$> args.mapM getName
  | "axiom", _, args => getAxiom AxiomKind.axiom args
  | "constant", _, args => getAxiom AxiomKind.constant args
  | "axioms", _, args => getVars args $ «axioms» AxiomKind.axiom
  | "constants", _, args => getVars args $ «axioms» AxiomKind.constant
  | "variable", _, args => getVars args $ «variable» VariableKind.variable false
  | "parameter", _, args => getVars args $ «variable» VariableKind.parameter false
  | "variables", _, args => getVars args $ «variable» VariableKind.variable true
  | "parameters", _, args => getVars args $ «variable» VariableKind.parameter true
  | "definition", _, args => getDecl DeclKind.def args
  | "theorem", _, args => getDecl DeclKind.theorem args
  | "abbreviation", _, args => getDecl DeclKind.abbrev args
  | "example", _, args => getDecl DeclKind.example args
  | "instance", _, args => getDecl DeclKind.instance args
  | "inductive", _, args => getInductive false args
  | "class_inductive", _, args => getInductive true args
  | "structure", _, args => getStructure false args
  | "class", _, args => getStructure true args
  | "attribute", _, args => getAttribute args
  | "precedence", _, args => do precedence (← getSym args[0]) (← getPrec args[1])
  | "open", _, args => «open» false <$> args.mapM getOpen
  | "export", _, args => «open» true <$> args.mapM getOpen
  | "include", _, args => «include» true <$> args.mapM getName
  | "omit", _, args => «include» false <$> args.mapM getName
  | "hide", _, args => «hide» <$> args.mapM getName
  | "theory", _, args => «theory» <$> getModifiers args[0]
  | "set_option", _, args => do setOption (← getName args[0]) (← getOptionVal args[1])
  | "declare_trace", _, args => declareTrace <$> getName args[0]
  | "add_key_equivalence", _, args => do addKeyEquivalence (← getName args[0]) (← getName args[1])
  | "run_cmd", _, args => runCmd <$> getExpr args[0]
  | "#check", _, args => check <$> getExpr args[0]
  | "#reduce", _, args => reduce (args[0] ≠ 0) <$> getExpr args[1]
  | "#eval", _, args => eval <$> getExpr args[0]
  | "#unify", _, args => do unify (← getExpr args[0]) (← getExpr args[1])
  | "#compile", _, args => eval <$> getExpr args[0]
  | "#help", _, args => help <$> getHelpCmd args[0]
  | "#print", _, args => print <$> getPrintCmd args
  | "user_command", v, args => do
    userCommand v (← getModifiers args[0]) (← args[1:].toArray.mapM getParam)
  | k, v, args => match toNotationKind k with
    | some nk => getNotationCmd nk args
    | none => throw s!"getCommand parse error, unknown kind {k}"
where
  getAxiom (ak) (args : Array AstId) : M Command := do
    Command.axiom ak
      (← getModifiers args[0]) (← getName args[2]) (← getLevelDecl args[1])
      (← getBinders args[3]) (← getExpr args[4])

  getVars (args : Array AstId) (f : Modifiers → Binders → Command) : M Command := do
    f (← getModifiers args[0]) <$> args[1:].toArray.mapM getBinder

  getHeader (args : Subarray AstId) : M _ := do
    (← getLevelDecl args[0], ← opt getName args[1], ← getBinders args[2], ← opt getExpr args[3])

  getMutualHeader (args : Subarray AstId) : M (LevelDecl × Binders) := do
    pure (← getLevelDecl args[0], /- ← arr getName args[1], -/ ← getBinders args[2])

  getDecl (dk) (args : Array AstId) : M Command := do
    let mods ← getModifiers args[0]
    if args[1] = 0 then
      let (us, n, bis, ty) ← getHeader args[2:6]
      let val ← opt getDeclVal args[6]
      Command.decl dk mods n us bis ty val
    else
      let (us, bis) ← getMutualHeader args[2:5]
      Command.mutualDecl dk mods us bis (← arr (getMutual getArm) args[5])

  getNotationCmd (mk : Option MixfixKind) (args : Array AstId) : M Command := do
    Command.notation (← getLocal args[0]) (← arr getAttr args[1]) (← getNotationDef mk args[2:])

  getInductive (cl args) : M Command := do
    let mods ← getModifiers args[0]
    if args[1] = 0 then
      let (us, n, bis, ty) ← getHeader args[2:6]
      let nota ← opt getNotation args[6]
      Command.inductive cl mods n.get! us bis ty nota (← arr getIntro args[7])
    else
      let (us, bis) ← getMutualHeader args[2:5]
      let nota ← opt getNotation args[5]
      Command.mutualInductive cl mods us bis nota (← arr (getMutual getIntro) args[6])

  getStructure (cl args) : M Command := do
    Command.structure cl (← getModifiers args[0]) (← getName args[2])
      (← getLevelDecl args[1]) (← getBinders args[3]) (← arr getParent args[4])
      (← opt getExpr args[5]) (← opt getMk args[6]) (← arr getField args[7])

  getAttribute (args) : M Command := do
    let mods ← getModifiers args[0]
    «attribute» (args[1] ≠ 0) mods (← arr getAttr args[2]) (← args[3:].toArray.mapM getName)

end

inductive RawLevel where
  | «0»
  | suc : LevelId → RawLevel
  | max : Array LevelId → RawLevel
  | imax : Array LevelId → RawLevel
  | param : Name → RawLevel
  | mvar : Name → RawLevel
  deriving FromJson

instance : FromJson RawLevel :=
  ⟨fun x => do
    try fromJson? x
    catch e => throw s!"at: {x}\n{e}"⟩

instance : FromJson BinderInfo where
  fromJson? j := do
    match ← j.getNat? with
    | 0 => BinderInfo.default
    | 1 => BinderInfo.instImplicit
    | 2 => BinderInfo.strictImplicit
    | 4 => BinderInfo.implicit
    | 8 => BinderInfo.auxDecl
    | _ => throw "unknown binder type"

inductive Annotation1
  | no_univ
  | do_failure_eq
  | infix_fn
  | begin_hole
  | end_hole
  | anonymous_constructor
  | «calc»
  | no_info
  | frozen_name
  deriving FromJson

inductive Annotation2
  | «have»
  | «show»
  | «suffices»
  | checkpoint
  | «@»
  | «@@»
  | as_atomic
  | as_is
  deriving FromJson

inductive Annotation3
  | antiquote
  | expr_quote_pre
  | comp_irrel
  | inaccessible
  | «by»
  | pattern_hint
  | th_proof
  deriving FromJson

abbrev Annotation := Sum Annotation1 $ Sum Annotation2 Annotation3

inductive RawExpr1 where
  | var : Nat → RawExpr1
  | sort : LevelId → RawExpr1
  | const : Name → Array LevelId → RawExpr1
  | app : ExprId → ExprId → RawExpr1
  | lam (name : Name) (bi : BinderInfo) (dom body : ExprId)
  | Pi (name : Name) (bi : BinderInfo) (dom body : ExprId)
  | «let» (name : Name) (type value body : ExprId)
  deriving FromJson

inductive RawExpr2 where
  | «local» (name pp : Name) (bi : BinderInfo) (type : ExprId)
  | mvar (name pp : Name) (type : ExprId)
  | annotation (name : Annotation) (args : Array ExprId)
  | field_notation (field : Name) (idx : Nat) (args : Array ExprId)
  | typed_expr (args : Array ExprId)
  | «structure instance» (struct : Name) (catchall : Bool) (fields : Array Name) (args : Array ExprId)
  | projection_macro (I constr proj : Name) (idx : Nat) (params : Array Name)
    (type val : ExprId) (args : Array ExprId)
  deriving FromJson

inductive RawExpr3 where
  | «sorry» (synthetic : Bool) (args : Array ExprId)
  | prenum (value : String)
  | nat_value (value : String)
  | string_macro (value : String)
  | expr_quote_macro (value : ExprId) (reflected : Bool)
  | choice (args : Array ExprId)
  | as_pattern (args : Array ExprId)
  | rec_fn (name : Name) (args : Array ExprId)
  | delayed_abstraction (value : Array Name) (args : Array ExprId)
  deriving FromJson

inductive RawExpr4 where
  | no_equation : Unit → RawExpr4
  | equation (ignore_if_unused : Bool) (args : Array ExprId)
  | equations (num_fns : Nat) (fn_names fn_actual_names : Array Name)
    (prev_errors is_private is_noncomputable is_meta is_lemma gen_code aux_lemmas : Bool)
    (args : Array ExprId)
  | equations_result (args : Array ExprId)
  | ac_app (args : Array ExprId)
  | perm_ac (args : Array ExprId)
  | cc_proof (args : Array ExprId)
  deriving FromJson

abbrev RawExpr := Sum (Sum RawExpr1 RawExpr2) (Sum RawExpr3 RawExpr4)

instance : FromJson RawExpr :=
  ⟨fun x => do
    try fromJson? x
    catch e => throw s!"at: {x}\n{e}"⟩

structure RawAST3 where
  ast      : Array (Option RawNode3)
  commands : Array AstId
  level    : Array RawLevel
  expr     : Array (Option RawExpr)
  deriving FromJson

section
open Lean (Level)
open Lean3 (EquationsHeader LambdaEquation Expr Proj)

variable (lvls : Array Level)
def buildLevel : RawLevel → Level
  | RawLevel.«0» => Lean.levelZero
  | RawLevel.suc l => Lean.mkLevelSucc lvls[l]
  | RawLevel.max ls => Lean.mkLevelMax lvls[ls[0]] lvls[ls[1]]
  | RawLevel.imax ls => Lean.mkLevelIMax lvls[ls[0]] lvls[ls[1]]
  | RawLevel.param n => Lean.mkLevelParam n
  | RawLevel.mvar n => Lean.mkLevelMVar n

variable (exprs : Array Expr)

def buildLevels (ls : Array RawLevel) : Array Level := do
  let mut out := #[]
  for l in ls do
    let l' := buildLevel out l
    out := out.push l'
  out

def Annotation1.build : Annotation1 → Lean3.Annotation
  | no_univ => Lean3.Annotation.no_univ
  | do_failure_eq => Lean3.Annotation.do_failure_eq
  | infix_fn => Lean3.Annotation.infix_fn
  | begin_hole => Lean3.Annotation.begin_hole
  | end_hole => Lean3.Annotation.end_hole
  | anonymous_constructor => Lean3.Annotation.anonymous_constructor
  | «calc» => Lean3.Annotation.«calc»
  | no_info => Lean3.Annotation.no_info
  | frozen_name => Lean3.Annotation.frozen_name

def Annotation2.build : Annotation2 → Lean3.Annotation
  | «have» => Lean3.Annotation.«have»
  | «show» => Lean3.Annotation.«show»
  | «suffices» => Lean3.Annotation.«suffices»
  | checkpoint => Lean3.Annotation.checkpoint
  | «@» => Lean3.Annotation.«@»
  | «@@» => Lean3.Annotation.«@@»
  | as_atomic => Lean3.Annotation.as_atomic
  | as_is => Lean3.Annotation.as_is

def Annotation3.build : Annotation3 → Lean3.Annotation
  | antiquote => Lean3.Annotation.antiquote
  | expr_quote_pre => Lean3.Annotation.expr_quote_pre
  | comp_irrel => Lean3.Annotation.comp_irrel
  | inaccessible => Lean3.Annotation.inaccessible
  | «by» => Lean3.Annotation.«by»
  | pattern_hint => Lean3.Annotation.pattern_hint
  | th_proof => Lean3.Annotation.th_proof

def Annotation.build : Annotation → Lean3.Annotation
  | Sum.inl a => a.build
  | Sum.inr $ Sum.inl a => a.build
  | Sum.inr $ Sum.inr a => a.build

def RawExpr1.build : RawExpr1 → Expr
  | var i => Expr.var i
  | sort l => Expr.sort lvls[l]
  | const c ls => Expr.const c $ ls.map fun l => lvls[l]
  | app f a => Expr.app exprs[f] exprs[a]
  | lam n bi d b => Expr.lam n bi exprs[d] exprs[b]
  | Pi n bi d b => Expr.Pi n bi exprs[d] exprs[b]
  | «let» n t v b => Expr.let n exprs[t] exprs[v] exprs[b]

def RawExpr2.build : RawExpr2 → Expr
  | mvar n pp t => Expr.mvar n pp exprs[t]
  | «local» n pp bi t => Expr.local n pp bi exprs[t]
  | annotation n args => Expr.annotation n.build exprs[args[0]]
  | field_notation field idx args => Expr.field exprs[args[0]] $
    if field.isAnonymous then Proj.ident field else Proj.nat idx
  | typed_expr args => Expr.typed_expr exprs[args[0]] exprs[args[1]]
  | «structure instance» s ca flds args => Expr.structinst s ca
    (flds.zipWith args fun n a => (n, exprs[a]))
    (args[flds.size:].toArray.map fun a => exprs[a])
  | projection_macro I c p i ps ty val args =>
    Expr.proj I c p i ps exprs[ty] exprs[val] exprs[args[0]]

def RawExpr3.build : RawExpr3 → Expr
  | «sorry» s args => Expr.sorry s exprs[args[0]]
  | prenum n => Expr.prenum (Lean.Syntax.decodeNatLitVal? n).get!
  | nat_value n => Expr.nat (Lean.Syntax.decodeNatLitVal? n).get!
  | string_macro v => Expr.string v
  | expr_quote_macro v r => Expr.quote exprs[v] r
  | choice args => Expr.choice $ args.map fun v => exprs[v]
  | as_pattern args => Expr.as_pattern exprs[args[0]] exprs[args[1]]
  | rec_fn n args => Expr.rec_fn n exprs[args[0]]
  | delayed_abstraction ns args =>
    let args := args.map fun a => exprs[a]
    Expr.delayed_abstraction args.back (ns.zip args.pop)

def RawExpr4.build : RawExpr4 → Expr
  | no_equation _ => Expr.no_equation
  | equation iu args => Expr.equation exprs[args[0]] exprs[args[1]] iu
  | equations n ns as _ p nc m l gc al args =>
    let args : Array Expr := args.map fun a => exprs[a]
    let h := EquationsHeader.mk n ns as p nc m l gc al
    let (args, wf) :=
      if args.size ≥ 2 ∧ args.back.toLambdaEqn.isNone then (args.pop, some args.back)
      else (args, none)
    Expr.equations h (args.map fun e => e.toLambdaEqn.get!) wf
  | equations_result args => Expr.equations_result $ args.map fun a => exprs[a]
  | ac_app args =>
    let args : Array Expr := args.map fun a => exprs[a]
    Expr.ac_app args.pop args.back
  | perm_ac args => Expr.perm_ac exprs[args[0]] exprs[args[1]] exprs[args[2]] exprs[args[3]]
  | cc_proof args => Expr.cc_proof exprs[args[0]] exprs[args[1]]

def buildExprs (es : Array (Option RawExpr)) : Array Expr := do
  let mut out := #[]
  for e in es do
    let e' : Expr := match e with
    | some $ Sum.inl $ Sum.inl e => e.build lvls out
    | some $ Sum.inl $ Sum.inr e => e.build out
    | some $ Sum.inr $ Sum.inl e => e.build out
    | some $ Sum.inr $ Sum.inr e => e.build out
    | none => arbitrary
    out := out.push e'
  out

end

def RawAST3.toAST3 : RawAST3 → Except String AST3
| ⟨ast, commands, level, expr⟩ => do
  let level := buildLevels level
  let expr := buildExprs level expr
  commands.mapM getCommand |>.run ⟨ast, expr⟩ |>.map AST3.mk

end Parse

def parseAST3 (filename : System.FilePath) : IO AST3 := do
  -- println! "Reading {filename}..."
  let s ← IO.FS.readFile filename
  -- println! "Parsing Json..."
  let json ← Json.parse s
  -- println! "Decoding RawAST3..."
  let rawAST3 ← fromJson? json (α := Parse.RawAST3)
  -- println! "Converting RawAST3 to AST3..."
  rawAST3.toAST3

-- #eval show IO Unit from do
--   let s ← IO.FS.readFile "/home/mario/Documents/lean/lean/library/init/function.ast.json"
--   let json ← Json.parse s
--   let ⟨ast, commands, level, expr⟩ ← fromJson? json (α := Parse.RawAST3)
--   let level := Parse.buildLevels level
--   let expr := Parse.buildExprs level expr
--   for c in commands[6:7] do
--     println! (repr (← Parse.getNode c |>.run ⟨ast, expr⟩)).group ++ "\n"
--     println! (repr (← Parse.getCommand c |>.run ⟨ast, expr⟩).kind).group ++ "\n"
