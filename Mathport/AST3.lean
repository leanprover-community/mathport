/-
Copyright (c) 2021 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Daniel Selsam
-/
import Mathport.Util

def Lean.BinderInfo.bracket (paren : Bool) : BinderInfo → Format → Format
  | BinderInfo.default,        f => if paren then f.paren else f.group
  | BinderInfo.implicit,       f => f.bracket "{" "}"
  | BinderInfo.strictImplicit, f => f.bracket "{{" "}}"
  | BinderInfo.instImplicit,   f => f.sbracket
  | BinderInfo.auxDecl,        f => f.group

namespace Mathport

open Lean (Position Name BinderInfo)
open Std (Format)

structure Spanned (α : Type u) where
  start : Position
  end_ : Position
  kind  : α
  deriving Inhabited

instance [Repr α] : Repr (Spanned α) := ⟨fun n p => reprPrec n.kind p⟩

def Spanned.map (f : α → β) : Spanned α → Spanned β
  | ⟨s, e, a⟩ => ⟨s, e, f a⟩

local prefix:max "#" => Spanned

namespace AST3

inductive VariableKind | «variable» | «parameter»
  deriving Inhabited

instance : Repr VariableKind where
  reprPrec
  | VariableKind.«variable», _ => "variable"
  | VariableKind.«parameter», _ => "parameter"

inductive AxiomKind | «axiom» | «constant»
  deriving Inhabited

instance : Repr AxiomKind where
  reprPrec
  | AxiomKind.«axiom», _ => "axiom"
  | AxiomKind.«constant», _ => "constant"

inductive DeclKind | «def» | «theorem» | «abbrev» | «example» | «instance»
  deriving Inhabited

instance : Repr DeclKind where
  reprPrec
  | DeclKind.«def», _ => "def"
  | DeclKind.«theorem», _ => "theorem"
  | DeclKind.«abbrev», _ => "abbreviation"
  | DeclKind.«example», _ => "example"
  | DeclKind.«instance», _ => "instance"

def LocalReserve := Bool × Bool

instance : Repr LocalReserve := ⟨fun ⟨loc, res⟩ _ =>
  ((if loc then "local " else "") ++ (if res then "reserve " else "") : String)⟩

inductive MixfixKind | «infix» | «infixl» | «infixr» | «postfix» | «prefix»
  deriving Inhabited

instance : Repr MixfixKind where
  reprPrec
  | MixfixKind.«infix», _ => "infix"
  | MixfixKind.«infixl», _ => "infixl"
  | MixfixKind.«infixr», _ => "infixr"
  | MixfixKind.«postfix», _ => "postfix"
  | MixfixKind.«prefix», _ => "prefix"

inductive InferKind | implicit | relaxedImplicit | none

instance : Inhabited InferKind := ⟨InferKind.relaxedImplicit⟩

instance : Repr InferKind where
  reprPrec
  | InferKind.implicit, _ => "[]"
  | InferKind.relaxedImplicit, _ => "{}"
  | InferKind.none, _ => "( )"

def InferKind.optRepr : Option InferKind → Format
  | Option.none => ""
  | some ik => " " ++ repr ik

inductive Symbol
  | quoted : String → Symbol
  | ident : String → Symbol
  deriving Inhabited

instance : Repr Symbol where
  reprPrec
  | Symbol.quoted s, _ => ("`" ++ s ++ "`" : String)
  | Symbol.ident n, _ => n

inductive Choice
  | one : Name → Choice
  | many : Array Name → Choice
  deriving Inhabited

instance : Repr Choice where
  reprPrec
  | Choice.one n, _ => n.toString
  | Choice.many ns, _ => (Format.joinSep (ns.toList.map (·.toString)) "/").sbracket

inductive Proj
  | nat : Nat → Proj
  | ident : Name → Proj
  deriving Inhabited

instance : Repr Proj where
  reprPrec
  | Proj.nat n, _ => repr n
  | Proj.ident n, _ => n.toString

inductive NodeK : Type
  | mk (kind : String) (value : Name) (children : Array (Option #NodeK)) : NodeK
  deriving Inhabited

def Node := #NodeK
instance : Inhabited Node := inferInstanceAs (Inhabited #NodeK)

inductive Level
  | nat : Nat → Level
  | add : #Level → #Nat → Level
  | max : Array #Level → Level
  | imax : Array #Level → Level
  | param : Name → Level
  | paren : #Level → Level
  | placeholder : Level
  | other : NodeK → Level
  deriving Inhabited

def Levels := Option (Array #Level)
instance : Inhabited Levels := ⟨none⟩

section
set_option hygiene false
local notation "Modifiers" => Array #Modifier
local notation "Binders" => Array #Binder
local notation "Attributes" => Array #Attribute
local notation "PrecSymbol" => #Symbol × Option #Precedence

mutual

inductive Attribute
  | mk (del : Bool) (name : #Name) (args : Array (Option Node)) : Attribute
  deriving Inhabited

inductive Precedence
  | nat : Nat → Precedence
  | expr : #Expr → Precedence
  deriving Inhabited

inductive Binder
  | binder : BinderInfo → Option (Array #Name) → Binders → Option #Expr → Binder
  | «⟨⟩» : Array #Expr → Binder
  | «notation» : Notation → Binder
  | var : #Name → Binders → Option #Expr → #Expr → Binder
  | pat : #Expr → #Expr → Binder
  deriving Inhabited

inductive Arg
  | expr : Expr → Arg
  | exprs : Array #Expr → Arg
  | binder : Binder → Arg
  | binders : Binders → Arg
  deriving Inhabited

inductive Expr
  | «...» : Expr
  | «sorry» : Expr
  | «_» : Expr
  | «()» : Expr
  | «{}» : Expr
  | ident : Name → Expr
  | const (ambiguous : Bool) : #Name → Levels → Expr
  | nat : Nat → Expr
  | decimal : Nat → Nat → Expr
  | string : String → Expr
  | char : Char → Expr
  | paren : #Expr → Expr
  | sort (isType isStar : Bool) : Option #Level → Expr
  | app : #Expr → #Expr → Expr
  | «fun» (isAssume : Bool) : Binders → #Expr → Expr
  | «→» : #Expr → #Expr → Expr
  | Pi : Binders → #Expr → Expr
  | «show» : #Expr → #Proof → Expr
  | «have» (suff : Bool) : Option #Name → #Expr → #Proof → #Expr → Expr
  | «.» (compact : Bool) : #Expr → #Proj → Expr
  | «if» : Option #Name → #Expr → #Expr → #Expr → Expr
  | «calc» : Array (#Expr × #Expr) → Expr
  | «@» («partial» : Bool) : #Expr → Expr
  | pattern : #Expr → Expr
  | «`()» (lazy expr : Bool) : #Expr → Expr
  | «%%» : #Expr → Expr
  | «`[]» : Array #Tactic → Expr
  | «`» (resolve : Bool) : Name → Expr
  | «⟨⟩» : Array #Expr → Expr
  | infix_paren : Choice → Option #Expr → Expr
  | «(,)» : Array #Expr → Expr
  | «:» : #Expr → #Expr → Expr
  | hole : Array #Expr → Expr
  | «#[]» : Array #Expr → Expr
  | «by» : #Tactic → Expr
  | begin : Block → Expr
  | «let» : Binders → #Expr → Expr
  | «match» : Array #Expr → Option #Expr → Array Arm → Expr
  | «do» (braces : Bool) : Array #DoElem → Expr
  | «{,}» : Array #Expr → Expr
  | subtype (setOf : Bool) : #Name → Option #Expr → #Expr → Expr
  | sep : #Name → #Expr → #Expr → Expr
  | setReplacement : #Expr → Binders → Expr
  | structInst (ty : Option #Name) (src : Option #Expr)
    (fields : Array (#Name × #Expr)) (srcs : Array #Expr) (catchall : Bool) : Expr
  | atPat : #Expr → #Expr → Expr
  | «.()» : #Expr → Expr
  | «notation» (n : Name) : Array #Arg → Expr
  | other : NodeK → Expr
  deriving Inhabited

inductive Arm
  | mk (lhs : Array #Expr) (rhs : #Expr) : Arm
  deriving Inhabited

inductive DoElem
  | «let» : #Binder → DoElem
  | «←» : #Expr → Option #Expr → #Expr → Option #Expr → DoElem
  | eval : #Expr → DoElem
  deriving Inhabited

inductive Proof
  | «from» («:=» : Bool) : #Expr → Proof
  | block : Block → Proof
  | «by» : #Tactic → Proof
  deriving Inhabited

inductive Tactic
  | «;» : Array #Tactic → Tactic
  | «<|>» : Array #Tactic → Tactic
  | «[]» : Array #Tactic → Tactic
  | block : Block → Tactic
  | «by» : #Tactic → Tactic
  | exact_shortcut : #Expr → Tactic
  | expr : #Expr → Tactic
  | interactive (n : Name) : Array #Param → Tactic
  deriving Inhabited

inductive Block
  | mk (curly : Bool) (tacClass : Option #Name)
       (cfg : Option #Expr) (tacs : Array #Tactic) : Block
  deriving Inhabited

inductive Param
  | parse /- pexpr tag? -/ : Param
  | expr : #Expr → Param
  | block : Block → Param
  deriving Inhabited

inductive Action
  | prec : Precedence → Action
  | prev : Action
  | «scoped» : Option #Precedence → Option (#Name × #Expr) → Action
  | fold (right : Bool)
      (prec : Option #Precedence) (sep : PrecSymbol)
      («rec» : #Name × #Name × #Expr) (ini : Option #Expr)
      (term : Option PrecSymbol) : Action
  deriving Inhabited

inductive Literal
  | nat : Nat → Literal
  | var : #Name → Option #Action → Literal
  | sym : PrecSymbol → Literal
  | binder : Option #Precedence → Literal
  | binders : Option #Precedence → Literal
  deriving Inhabited

inductive Notation
  | mixfix : MixfixKind → PrecSymbol → Option #Expr → Notation
  | «notation» : Array #Literal → Option #Expr → Notation
  deriving Inhabited

end
end

def Binders := Array #Binder
instance : Inhabited Binders := ⟨#[]⟩
def Attributes := Array #Attribute
instance : Inhabited Attributes := ⟨#[]⟩
def PrecSymbol := #Symbol × Option #Precedence
instance : Inhabited PrecSymbol := inferInstanceAs (Inhabited (_×_))

inductive Modifier
  | doc : String → Modifier
  | attr («local» compact : Bool) : Attributes → Modifier
  | other : NodeK → Modifier
  deriving Inhabited

def Modifiers := Array #Modifier
instance : Inhabited Modifiers := ⟨#[]⟩

inductive DeclVal
  | expr : Expr → DeclVal
  | eqns : Array Arm → DeclVal
  deriving Inhabited

structure Mutual (α : Type) := (attrs : Attributes) (name : #Name) (ty : #Expr) (vals : Array α)
  deriving Inhabited

structure MutualHeader (α : Type) where
  (mods : Modifiers) (lvls : Levels) (bis : Binders) (vals : Array (Mutual α))
  deriving Inhabited

structure Intro where
  (doc : Option String) (name : #Name) (ik : Option InferKind) (bis : Binders) (ty : Option #Expr)

structure Rename := («from» to : #Name)

structure Parent where
  («private» : Bool) (name : Option #Name) (expr : #Expr) (renames : Array Rename)

structure Mk := (name : #Name) (ik : Option InferKind)

inductive Field
  | binder : BinderInfo → Array #Name → Option InferKind → Binders → Option #Expr → Field
  | «notation» : Notation → Field

inductive Command
  | «prelude» : Command
  | «import» : Array #Name → Command
  | mdoc : String → Command
  | «universe» (var plural : Bool) : Array #Name → Command
  | «namespace» : #Name → Command
  | «section» : Option #Name → Command
  | «end» : Option #Name → Command
  | «variable» : VariableKind → (plural : Bool) → Modifiers → Binders → Command
  | «axiom» : AxiomKind → Modifiers → #Name → Levels → Binders → #Expr → Command
  | «axioms» : AxiomKind → Modifiers → Binders → Command
  | decl : DeclKind → Modifiers → Option #Name →
    Levels → Binders → (ty : Option #Expr) → Option #DeclVal → Command
  | mutual_decl : DeclKind → Modifiers → Levels → Binders → Array (Mutual Arm) → Command
  | «inductive» («class» : Bool) : Modifiers → #Name → Levels → Binders →
    (ty : Option #Expr) → Option Notation → Array #Intro → Command
  | mutual_inductive («class» : Bool) : Modifiers → Levels → Binders →
    Option Notation → Array (Mutual #Intro) → Command
  | «structure» («class» : Bool) :
    Modifiers → #Name → Levels → Binders → Array #Parent → (ty : Option #Expr) →
    Option #Mk → Array #Field → Command
  | «notation» : LocalReserve → Attributes → Notation → Command
  | other : NodeK → Command
  deriving Inhabited

def spaced (f : α → Format) (mods : Array α) : Format :=
  (Format.joinSep (mods.toList.map f) Format.line).group

def spacedBefore (f : α → Format) (mods : Array α) : Format :=
  (Format.join (mods.toList.map fun m => Format.line ++ f m)).group

def spacedAfter (f : α → Format) (mods : Array α) : Format :=
  (Format.join (mods.toList.map fun m => f m ++ Format.line)).group

def suffix (pl : Bool) := if pl then "s " else " "

mutual

partial def optNode_repr : Option Node → Format
  | none => ("⬝" : Format)
  | some a => NodeK_repr a.kind

partial def NodeK_repr : NodeK → Format
  | ⟨k, v, c⟩ =>
    let s := k ++ if v.isAnonymous then "" else "[" ++ v.toString ++ "]"
    if c.isEmpty then s else
      "(" ++ s ++ Format.join (c.toList.map fun c => Format.line ++ optNode_repr c) ++ ")"
        |>.nest 2 |>.group

end

instance : Repr NodeK := ⟨fun n _ => NodeK_repr n⟩
instance : Repr Node := inferInstanceAs (Repr #NodeK)

instance : Repr Attribute where
  reprPrec
  | ⟨del, n, args⟩, _ =>
    (if del then "-" else "") ++ n.kind.toString ++
    Format.join (args.toList.map fun
      | none => ("⬝" : Format)
      | some a => NodeK_repr a.kind)

instance : Repr Attributes where reprPrec attrs _ :=
  (Format.joinSep (attrs.toList.map repr) ", ").sbracket

partial def Level_repr : Level → (prec : _ := 0) → Format
  | Level.nat n, _ => repr n
  | Level.add l n, p => Format.parenPrec 10 p $
    Level_repr l.kind 10 ++ "+" ++ repr n
  | Level.imax ls, p => Format.parenPrec max_prec p $
    "imax" ++ Format.join (ls.toList.map fun l => " " ++ Level_repr l.kind max_prec)
  | Level.max ls, p => Format.parenPrec max_prec p $
    "max" ++ Format.join (ls.toList.map fun l => " " ++ Level_repr l.kind max_prec)
  | Level.param u, _ => u.toString
  | Level.paren l, _ => Level_repr l.kind
  | Level.placeholder, _ => "_"
  | Level.other n, _ => NodeK_repr n

instance : Repr Level := ⟨@Level_repr⟩

instance : Repr Levels where
  reprPrec
  | none, _ => ""
  | some us, _ => (Format.joinSep (us.toList.map fun u => Level_repr u.kind) ", ").bracket ".{" "}"

mutual

partial def Precedence_repr : Precedence → Format
  | Precedence.nat n => repr n
  | Precedence.expr e => Expr_repr e.kind max_prec

partial def optTy : Option #Expr → Format
  | none => ""
  | some e => " : " ++ Expr_repr e.kind

partial def Binder_repr : Binder → (paren :_:= true) → Format
  | Binder.binder bi none _ e, paren => bi.bracket paren $
    match e with | none => "⬝" | some e => Expr_repr e.kind
  | Binder.binder bi (some vars) bis ty, paren => bi.bracket paren $
    spaced (fun v => v.kind.toString) vars ++ Binders_repr bis ++ optTy ty
  | Binder.«⟨⟩» args, _ =>
    (Format.joinSep (args.toList.map fun e => Expr_repr e.kind) ", ").bracket "⟨" "⟩"
  | Binder.var v bis ty val, paren => BinderInfo.default.bracket paren $
    v.kind.toString ++ Binders_repr bis ++ optTy ty ++
    " := " ++ Expr_repr val.kind
  | Binder.pat pat val, paren => BinderInfo.default.bracket paren $
    Expr_repr pat.kind ++ " := " ++ Expr_repr val.kind
  | Binder.notation n, paren => BinderInfo.default.bracket paren $ Notation_repr n #[]

partial def Binders_repr (bis : Binders) (paren := true) : Format :=
  spacedBefore (fun m => Binder_repr m.kind paren) bis

partial def Expr_repr : Expr → (prec : _ := 0) → Format
  | Expr.«...», _ => "..."
  | Expr.sorry, _ => "sorry"
  | Expr.«_», _ => "_"
  | Expr.«()», _ => "()"
  | Expr.«{}», _ => "{}"
  | Expr.ident n, _ => n.toString
  | Expr.const _ n l, _ => n.kind.toString ++ repr l
  | Expr.nat n, _ => repr n
  | Expr.decimal n d, _ => repr n ++ "/" ++ repr d
  | Expr.string s, _ => repr s
  | Expr.char c, _ => repr c
  | Expr.paren e, p => Expr_repr e.kind p
  | Expr.sort ty st u, p => Format.parenPrec max_prec p $
    (if ty then "Type" else "Sort") ++
    if st then ("*" : Format) else match u with | none => "" | some u => " " ++ Level_repr u.kind max_prec
  | Expr.«→» lhs rhs, p => Format.parenPrec 25 p $
    Expr_repr lhs.kind 25 ++ " → " ++ Expr_repr rhs.kind 24
  | Expr.fun as bis e, p => Format.parenPrec max_prec p $
    (if as then "assume " else "λ " : Format) ++
    Format.joinSep (bis.toList.map fun bi => Binder_repr bi.kind false) " " ++ ", " ++ Expr_repr e.kind
  | Expr.Pi bis e, p => Format.parenPrec max_prec p $ "∀ " ++
    Format.joinSep (bis.toList.map fun bi => Binder_repr bi.kind false) " " ++ ", " ++ Expr_repr e.kind
  | Expr.app f x, p => Format.parenPrec max_prec p $
    Expr_repr f.kind 1023 ++ " " ++ Expr_repr x.kind max_prec
  | Expr.show t pr, p => Format.parenPrec 1000 p $
    "show " ++ Expr_repr t.kind ++ Proof_repr' pr.kind
  | Expr.have suff h t pr e, p => Format.parenPrec 1000 p $
    (if suff then "suffices " else "have ") ++
    (match h with | none => "" | some h => h.kind.toString ++ " : ") ++
    Expr_repr t.kind ++ Proof_repr' pr.kind ++
    "," ++ Format.line ++ Expr_repr e.kind
  | Expr.«.» compact e pr, p =>
    Expr_repr e.kind max_prec ++ (if compact then "." else "^.") ++ repr pr.kind
  | Expr.if h c t e, p => Format.parenPrec 1000 p $ "if " ++
    (match h with | none => "" | some h => h.kind.toString ++ " : ") ++
    Expr_repr c.kind ++ " then " ++ Expr_repr t.kind ++ " else " ++ Expr_repr e.kind
  | Expr.calc args, p => Format.parenPrec 1000 p $ "calc" ++
    (Format.join $ args.toList.map fun (lhs, rhs) =>
      Format.line ++ Expr_repr lhs.kind ++ " : " ++ Expr_repr rhs.kind).nest 2
  | Expr.«@» part e, p => Format.parenPrec 1000 p $
    (if part then "@@" else "@") ++ Expr_repr e.kind
  | Expr.pattern e, p => Format.parenPrec 1000 p $ "(: " ++ Expr_repr e.kind ++ " :)"
  | Expr.«`()» lazy expr e, p => Format.parenPrec 1000 p $
    (if expr then "`(" else if lazy then "```(" else "``(") ++
    (match e.kind with
    | Expr.«:» e ty => Expr_repr e.kind ++ " : " ++ Expr_repr ty.kind
    | _ => Expr_repr e.kind : Format) ++ ")"
  | Expr.«%%» e, p => Format.parenPrec 1000 p $ "%%" ++ Expr_repr e.kind
  | Expr.«`[]» tacs, p => Format.parenPrec 1000 p $
    (Format.joinSep (tacs.toList.map fun t => Tactic_repr t.kind) ", ").bracket "`[" "]"
  | Expr.«`» res n, p => Format.parenPrec 1000 p $
    (if res then "``" else "`" : Format) ++ n.toString
  | Expr.«⟨⟩» es, p => Format.parenPrec 1000 p $
    (Format.joinSep (es.toList.map fun e => Expr_repr e.kind) ", ").bracket "⟨" "⟩"
  | Expr.infix_paren c e, p => Format.parenPrec 1000 p $
    "(" ++ repr c ++ (match e with | none => "" | some e => " " ++ Expr_repr e.kind) ++ ")"
  | Expr.«(,)» es, _ =>
    (Format.joinSep (es.toList.map fun e => Expr_repr e.kind) ", ").paren
  | Expr.«.()» e, _ => "." ++ Expr_repr e.kind max_prec
  | Expr.«:» e ty, _ => "(" ++ Expr_repr e.kind ++ " : " ++ Expr_repr ty.kind ++ ")"
  | Expr.hole es, p => Format.parenPrec 1000 p $
    (Format.joinSep (es.toList.map fun e => Expr_repr e.kind) ", ").bracket "{! " " !}"
  | Expr.«#[]» es, p => Format.parenPrec 1000 p $
    (Format.joinSep (es.toList.map fun e => Expr_repr e.kind) ", ").bracket "#[" "]"
  | Expr.by tac, p => Format.parenPrec 1000 p $ "by " ++ Tactic_repr tac.kind
  | Expr.begin tacs, p => Format.parenPrec 1000 p $ Block_repr tacs
  | Expr.let bis e, p => Format.parenPrec 1000 p $
    ("let " ++ (("," ++ Format.line).joinSep
      (bis.toList.map fun bi => Binder_repr bi.kind false)).nest 4 ++ " in").group ++
    Format.line ++ Expr_repr e.kind
  | Expr.match xs ty eqns, _ => "match " ++
    Format.joinSep (xs.toList.map fun x => Expr_repr x.kind) ", " ++ optTy ty ++ " with" ++
    (if eqns.isEmpty then " end" else Arms_repr eqns ++ Format.line ++ "end" : Format)
  | Expr.do braces els, p => Format.parenPrec 1000 p $
    let s := Format.line ++ (("," ++ Format.line).joinSep
      (els.toList.map fun el => DoElem_repr el.kind)).nest 2
    if braces then "do" ++ s else "do {" ++ s ++ " }"
  | Expr.«{,}» es, _ => (Format.joinSep (es.toList.map fun e => Expr_repr e.kind) ", ").bracket "{" "}"
  | Expr.subtype setOf x ty p, _ =>
    "{" ++ x.kind.toString ++ optTy ty ++
    (if setOf then " | " else " // ") ++ Expr_repr p.kind ++ "}"
  | Expr.sep x ty p, _ =>
    "{" ++ x.kind.toString ++ " ∈ " ++ Expr_repr ty.kind ++ " | " ++ Expr_repr p.kind ++ "}"
  | Expr.setReplacement e bis, _ =>
    "{(" ++ Expr_repr e.kind ++ ") |" ++ Binders_repr bis ++ "}"
  | Expr.structInst S src flds srcs catchall, _ => Format.nest 2 $ Format.group $ "{ " ++
    (match S with | none => "" | some S => S.kind.toString ++ " ." ++ Format.line : Format) ++
    (match src with | none => "" | some s => Expr_repr s.kind ++ " with" ++ Format.line : Format) ++
    (("," ++ Format.line).joinSep $
      flds.toList.map (fun (i, s) => i.kind.toString ++ " := " ++ Expr_repr s.kind) ++
      srcs.toList.map (fun s => ".." ++ Expr_repr s.kind) ++
      if catchall then [(".." : Format)] else []) ++ " }"
  | Expr.atPat lhs rhs, p => Format.parenPrec 1000 p $
    Expr_repr lhs.kind max_prec ++ "@" ++ Expr_repr rhs.kind max_prec
  | Expr.notation n args, _ => n.toString ++
    (Format.joinSep (args.toList.map fun e => Arg_repr e.kind) ", ").paren
  | Expr.other n, _ => NodeK_repr n

partial def Arg_repr : Arg → Format
  | Arg.expr e => Expr_repr e
  | Arg.exprs es => (Format.joinSep (es.toList.map fun e => Expr_repr e.kind) ", ").sbracket
  | Arg.binder bi => Binder_repr bi
  | Arg.binders bis => spaced (fun m => Binder_repr m.kind) bis

partial def Arm_repr : Arm → Format
  | ⟨lhs, rhs⟩ =>
    "\n| " ++ Format.joinSep (lhs.toList.map fun e => Expr_repr e.kind) ", " ++
    " := " ++ Expr_repr rhs.kind

partial def DoElem_repr : DoElem → Format
  | DoElem.let bi => "let " ++ Binder_repr bi.kind false
  | DoElem.«←» lhs ty rhs els =>
    Expr_repr lhs.kind ++ " " ++ optTy ty ++ Expr_repr rhs.kind ++
    match els with | none => "" | some e => Expr_repr e.kind
  | DoElem.eval e => Expr_repr e.kind

partial def Arms_repr (arms : Array Arm) : Format :=
  if arms.isEmpty then "." else Format.join $ arms.toList.map Arm_repr

partial def Proof_repr' : Proof → Format
  | Proof.from true e => " := " ++ Expr_repr e.kind
  | p => ", " ++ Proof_repr p

partial def Proof_repr : Proof → Format
  | Proof.from _ e => "from " ++ Expr_repr e.kind
  | Proof.block tacs => Block_repr tacs
  | Proof.by tac => "by " ++ Tactic_repr tac.kind

partial def Tactic_repr : Tactic → Format
  | Tactic.«;» tacs =>
    Format.joinSep (tacs.toList.map fun t => Tactic_repr t.kind) "; "
  | Tactic.«<|>» tacs =>
    Format.joinSep (tacs.toList.map fun t => Tactic_repr t.kind) " <|> "
  | Tactic.«[]» tacs =>
    (Format.joinSep (tacs.toList.map fun t => Tactic_repr t.kind) ", ").sbracket
  | Tactic.block tacs => Block_repr tacs
  | Tactic.by tac => "by " ++ Tactic_repr tac.kind
  | Tactic.exact_shortcut e => Expr_repr e.kind
  | Tactic.expr tac => Expr_repr tac.kind
  | Tactic.interactive n args => n.toString ++
    Format.join (args.toList.map fun a => " " ++ Param_repr a.kind)

partial def Block_repr : Block → Format
  | ⟨curly, cl, cfg, tacs⟩ =>
    let s₁ := match cl with | none => "" | some cl => " [" ++ cl.kind.toString ++ "]"
    let s₂ : Format := match cfg with | none => "" | some e => " with " ++ Expr_repr e.kind ++ ","
    let s₃ := (("," ++ Format.line).joinSep (tacs.toList.map fun t => Tactic_repr t.kind)).nest 2
    if curly then
      "{" ++ s₁ ++ s₂ ++ (if cl.isSome || cfg.isSome then Format.line else " ") ++ s₃ ++ " }"
    else
      "begin" ++ s₁ ++ s₂ ++ Format.line ++ s₃ ++ Format.line ++ "end"

partial def Param_repr : Param → Format
  | Param.parse => "⬝"
  | Param.expr e => Expr_repr e.kind
  | Param.block e => Block_repr e

partial def optPrec_repr : Option #Precedence → Format
  | none => ""
  | some p => ":" ++ Precedence_repr p.kind

partial def PrecSymbol_repr : PrecSymbol → Format
  | (sym, prec) => repr sym.kind ++ optPrec_repr prec

partial def Action_repr : Action → Format
  | Action.prec p => Precedence_repr p
  | Action.prev => "prev"
  | Action.scoped p none => "scoped" ++ optPrec_repr p
  | Action.scoped p (some (x, e)) =>
    "(scoped" ++ optPrec_repr p ++ x.kind.toString ++ ", " ++ Expr_repr e.kind ++ ")"
  | Action.fold r p sep (x, y, «rec») ini term =>
    "(fold" ++ (if r then "r" else "l") ++ optPrec_repr p ++ " " ++
    PrecSymbol_repr sep ++
    " (" ++ x.kind.toString ++ " " ++ y.kind.toString ++ ", " ++ Expr_repr rec.kind ++ ")" ++
    (match ini with | none => "" | some ini => " " ++ Expr_repr ini.kind) ++
    (match term with | none => "" | some term => " " ++ PrecSymbol_repr term) ++ ")"

partial def Literal_repr : Literal → Format
  | Literal.nat n => repr n
  | Literal.sym sym => PrecSymbol_repr sym
  | Literal.binder prec => "binder" ++ optPrec_repr prec
  | Literal.binders prec => "binders" ++ optPrec_repr prec
  | Literal.var v a => (v.kind.toString : Format) ++
    match a with | none => "" | some a => ":" ++ Action_repr a.kind

partial def Notation_repr : Notation → (attrs : Attributes := #[]) → Format
  | Notation.mixfix mk sym val, attrs => repr mk ++ " " ++
    (if attrs.isEmpty then "" else repr attrs ++ " " : Format) ++
    PrecSymbol_repr sym ++
    (match val with | none => "" | some e => " := " ++ Expr_repr e.kind)
  | Notation.notation lits val, attrs => "notation" ++
    spacedBefore (fun n => Literal_repr n.kind) lits ++
    (match val with | none => "" | some e => " := " ++ Expr_repr e.kind)

end

instance : Repr Precedence := ⟨fun n _ => Precedence_repr n⟩
instance : Repr Binder := ⟨fun n _ => Binder_repr n⟩
instance : Repr Binders := ⟨fun n _ => Binders_repr n⟩
instance : Repr Expr := ⟨fun n _ => Expr_repr n⟩
instance : Repr Arg := ⟨fun n _ => Arg_repr n⟩
instance : Repr Arm := ⟨fun n _ => Arm_repr n⟩
instance : Repr DoElem := ⟨fun n _ => DoElem_repr n⟩
instance : Repr Proof := ⟨fun n _ => Proof_repr n⟩
instance : Repr Tactic := ⟨fun n _ => Tactic_repr n⟩
instance : Repr Block := ⟨fun n _ => Block_repr n⟩
instance : Repr Param := ⟨fun n _ => Param_repr n⟩
instance : Repr PrecSymbol := ⟨fun n _ => PrecSymbol_repr n⟩
instance : Repr Action := ⟨fun n _ => Action_repr n⟩
instance : Repr Literal := ⟨fun n _ => Literal_repr n⟩
instance : Repr Notation := ⟨fun n _ => Notation_repr n⟩

instance : Repr DeclVal where reprPrec
  | DeclVal.expr n, _ => " :=" ++ Format.line ++ repr n
  | DeclVal.eqns arms, _ => repr arms

instance : Repr Modifier where reprPrec
  | Modifier.doc s, _ => ("/--" ++ s ++ "-/" : String)
  | Modifier.attr l c attrs, _ =>
    (if l then "local " else "") ++ (if c then "@" else "attribute ") ++ repr attrs
  | Modifier.other n, _ => repr n

def Modifiers_repr : Modifiers → Format := spacedAfter repr
instance : Repr Modifiers := ⟨fun n _ => Modifiers_repr n⟩

instance : Repr Intro where reprPrec
  | ⟨doc, name, ik, bis, ty⟩, _ =>
    (match doc with | none => "" | some doc => "\n/--" ++ doc ++ "-/") ++
    "\n| " ++ name.kind.toString ++ InferKind.optRepr ik ++ repr bis ++ optTy ty

def Intros_repr (arms : Array #Intro) : Format :=
  Format.join $ arms.toList.map repr

def Mutual_repr (f : Array α → Format) : Mutual α → Format
  | ⟨attr, n, ty, vals⟩ =>
    "with " ++ repr attr ++ " " ++ n.kind.toString ++ " : " ++
    Expr_repr ty.kind ++ f vals

instance : Repr Mk where reprPrec
  | ⟨mk, ik⟩, _ => mk.kind.toString ++ InferKind.optRepr ik

instance : Repr Rename where reprPrec
  | ⟨«from», to⟩, _ => («from».kind.toString ++ "→" ++ to.kind.toString : String)

instance : Repr Parent where reprPrec
  | ⟨priv, n, ty, rens⟩, _ =>
    (if priv then "private " else "") ++
    (match n with | none => "" | some n => n.kind.toString ++ " : ") ++ repr ty ++
    if rens.isEmpty then ("":Format) else "renaming" ++
      Format.join (rens.toList.map fun r => " " ++ repr r)

instance : Repr Field where reprPrec
  | Field.binder bi vars ik bis ty, _ => bi.bracket true $
    spaced (fun v => v.kind.toString) vars ++ InferKind.optRepr ik ++ Binders_repr bis ++ optTy ty
  | Field.notation n, _ => (repr n).paren

instance : Repr Command where reprPrec c _ := match c with
  | Command.«prelude» => "prelude"
  | Command.«import» ns => "import " ++ Format.joinSep (ns.toList.map fun a => a.kind.toString) " "
  | Command.mdoc s => ("/-!" ++ s ++ "-/" : String)
  | Command.«universe» var pl ns =>
    "universe" ++ (if var then " variable" else "") ++ suffix pl ++
    Format.joinSep (ns.toList.map fun a => a.kind.toString) " "
  | Command.«namespace» n => ("namespace ":Format) ++ n.kind.toString
  | Command.«section» (some n) => ("section ":Format) ++ n.kind.toString
  | Command.«section» none => "section"
  | Command.«end» (some n) => ("end ":Format) ++ n.kind.toString
  | Command.«end» none => "end"
  | Command.«variable» vk plural mods bis =>
    repr mods ++ repr vk ++ (if plural then "s" else "") ++ Binders_repr bis plural
  | Command.axiom ak mods n us bis ty =>
    repr mods ++ repr ak ++ " " ++ n.kind.toString ++
    repr us ++ repr bis ++ optTy ty
  | Command.axioms ak mods bis => repr mods ++ repr ak ++ "s" ++ repr bis
  | Command.decl dk mods n us bis ty val =>
    repr mods ++ repr dk ++
    (match n with | none => "" | some n => " " ++ n.kind.toString : String) ++
    repr us ++ repr bis ++ optTy ty ++
    (match val with | none => ("":Format) | some val => repr val.kind)
  | Command.mutual_decl dk mods us bis arms =>
    repr mods ++ repr dk ++ " " ++
    Format.joinSep (arms.toList.map fun m => m.name.kind.toString) ", " ++
    repr bis ++ Format.join (arms.toList.map (Mutual_repr Arms_repr))
  | Command.inductive cl mods n us bis ty nota intros =>
    repr mods ++ (if cl then "class " else "") ++ "inductive " ++
    n.kind.toString ++ repr us ++ repr bis ++ optTy ty ++
    (match nota with | none => "" | some n => "\n" ++ repr n) ++
    Intros_repr intros
  | Command.mutual_inductive cl mods us bis nota inds =>
    repr mods ++ (if cl then "class " else "") ++ "inductive " ++
    Format.joinSep (inds.toList.map fun m => m.name.kind.toString) ", " ++ repr bis ++
    (match nota with | none => "" | some n => "\n" ++ repr n) ++
    Format.join (inds.toList.map (Mutual_repr Intros_repr))
  | Command.structure cl mods n us bis exts ty mk flds =>
    repr mods ++ (if cl then "class " else "structure ") ++
    n.kind.toString ++ repr us ++ repr bis ++
    (if exts.isEmpty then ("":Format) else "extends " ++
      ((", ":Format).joinSep $ exts.toList.map repr)) ++ optTy ty ++
    if mk.isNone && flds.isEmpty then ("":Format) else " :=" ++
    (match mk with | none => "" | some mk => " " ++ repr mk ++
      if flds.isEmpty then "" else " ::" : Format) ++
    ((Format.join $ flds.toList.map fun f => Format.line ++ repr f).group).nest 2
  | Command.notation loc attrs n => repr loc ++ Notation_repr n attrs
  | Command.other n => repr n

end AST3

structure AST3 where
  commands : Array (Spanned AST3.Command)

end Mathport
