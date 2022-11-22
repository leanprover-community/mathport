/-
Copyright (c) 2021 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Daniel Selsam
-/
import Mathport.Util.Misc

def Lean.BinderInfo.bracket (paren : Bool) : BinderInfo → Format → Format
  | BinderInfo.default,        f => if paren then f.paren else f.group
  | BinderInfo.implicit,       f => f.bracket "{" "}"
  | BinderInfo.strictImplicit, f => f.bracket "{{" "}}"
  | BinderInfo.instImplicit,   f => f.sbracket

namespace Mathport

open Lean (Position Name BinderInfo)
open Std (Format)

namespace Lean3

inductive Proj
  | nat : Nat → Proj
  | ident : Name → Proj
  deriving Inhabited

instance : Repr Proj where
  reprPrec
  | Proj.nat n, _ => repr n
  | Proj.ident n, _ => n.toString

open Lean (Level)

inductive Annotation
  | no_univ
  | do_failure_eq
  | infix_fn
  | begin_hole
  | end_hole
  | anonymous_constructor
  | «calc»
  | no_info
  | frozen_name
  | «have»
  | «show»
  | «suffices»
  | checkpoint
  | «@»
  | «@@»
  | as_atomic
  | as_is
  | antiquote
  | expr_quote_pre
  | comp_irrel
  | inaccessible
  | «by»
  | pattern_hint
  | th_proof
  deriving Repr

structure EquationsHeader :=
  (num_fns : Nat) (fn_names fn_actual_names : Array Name)
  (is_private is_noncomputable is_meta is_lemma gen_code aux_lemmas : Bool)
  deriving Repr

instance : Repr Level.Data := ⟨fun _ _ => "·"⟩
deriving instance Repr for Level

mutual

  inductive Expr where
    | var : Nat → Expr
    | sort : Level → Expr
    | const : Name → Array Level → Expr
    | mvar (name pp : Name) (type : Expr)
    | «local» (name pp : Name) (bi : BinderInfo) (type : Expr)
    | app : Expr → Expr → Expr
    | lam (name : Name) (bi : BinderInfo) (dom body : Expr)
    | Pi (name : Name) (bi : BinderInfo) (dom body : Expr)
    | «let» (name : Name) (type value body : Expr)
    | annotation : Annotation → Expr → Expr
    | field : Expr → Proj → Expr
    | typed_expr (ty val : Expr)
    | structinst (struct : Name) (catchall : Bool) (fields : Array (Name × Expr)) (sources : Array Expr)
    | prenum (value : Nat)
    | nat (value : Nat)
    | quote (value : Expr) (expr : Bool)
    | choice (args : Array Expr)
    | string (value : String)
    | no_equation
    | equation (lhs rhs : Expr) (ignore_if_unused : Bool)
    | equations (h : EquationsHeader) (eqns : Array LambdaEquation) (wf : Option Expr)
    | equations_result (args : Array Expr)
    | as_pattern (lhs rhs : Expr)
    | delayed_abstraction : Expr → Array (Name × Expr) → Expr
    | «sorry» (synthetic : Bool) (ty : Expr)
    | rec_fn (name : Name) (ty : Expr)
    | proj (I constr proj : Name) (idx : Nat) (params : Array Name) (ty val arg : Expr)
    | ac_app (args : Array Expr) (op : Expr)
    | perm_ac (assoc comm e1 e2 : Expr)
    | cc_proof (e1 e2 : Expr)
    deriving Inhabited, Repr

  inductive LambdaEquation where
    | no_equation
    | equation (lhs rhs : Expr) (ignore_if_unused : Bool)
    | lam (name : Name) (bi : BinderInfo) (dom : Expr) : LambdaEquation → LambdaEquation
    deriving Inhabited, Repr

end

partial def Expr.toLambdaEqn : Expr → Option LambdaEquation
  | Expr.no_equation => LambdaEquation.no_equation
  | Expr.equation lhs rhs iu => LambdaEquation.equation lhs rhs iu
  | Expr.lam n pp bi e => LambdaEquation.lam n pp bi <$> e.toLambdaEqn
  | _ => none

end Lean3

structure Meta where
  id : Nat
  start : Position
  end_ : Position
  deriving Inhabited

structure Spanned (α : Type u) where
  meta : Option Meta
  kind : α
  deriving Inhabited

instance [Repr α] : Repr (Spanned α) := ⟨fun n p => reprPrec n.kind p⟩

def Spanned.map (f : α → β) : Spanned α → Spanned β
  | ⟨m, a⟩ => ⟨m, f a⟩

def Spanned.dummy (a : α) : Spanned α := ⟨none, a⟩

local prefix:max "#" => Spanned

namespace AST3

open Lean3 (Proj)

inductive BinderName
  | ident : Name → BinderName
  | «_» : BinderName

instance : Repr BinderName where
  reprPrec
  | BinderName.ident n, _ => n.toString
  | BinderName.«_», _ => "_"

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
  | DeclKind.def, _ => "def"
  | DeclKind.theorem, _ => "theorem"
  | DeclKind.abbrev, _ => "abbreviation"
  | DeclKind.example, _ => "example"
  | DeclKind.instance, _ => "instance"

def LocalReserve := Bool × Bool

instance : Repr LocalReserve := ⟨fun ⟨loc, res⟩ _ =>
  ((if loc then "local " else "") ++ (if res then "reserve " else "") : String)⟩

inductive MixfixKind | «infix» | «infixl» | «infixr» | «postfix» | «prefix»
  deriving Inhabited, BEq, Hashable

instance : Repr MixfixKind where
  reprPrec
  | MixfixKind.infix, _ => "infix"
  | MixfixKind.infixl, _ => "infixl"
  | MixfixKind.infixr, _ => "infixr"
  | MixfixKind.postfix, _ => "postfix"
  | MixfixKind.prefix, _ => "prefix"

instance : ToString MixfixKind where
  toString m := toString (repr m)

inductive InferKind | implicit | relaxedImplicit | none

instance : Inhabited InferKind := ⟨InferKind.relaxedImplicit⟩

instance : ToString InferKind where
  toString
  | InferKind.implicit => "[]"
  | InferKind.relaxedImplicit => "{}"
  | InferKind.none => "( )"

instance : Repr InferKind where
  reprPrec ik _ := toString ik

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

def Symbol.trim : Symbol → String
  | Symbol.ident s => s
  | Symbol.quoted s => s.trim

def Symbol.toString : Symbol → String
  | Symbol.ident s => s
  | Symbol.quoted s => s

inductive Choice
  | one : Name → Choice
  | many : Array Name → Choice
  deriving Inhabited

def Choice.name : Choice → Name
  | Choice.one n => n
  | Choice.many #[n] => n
  | _ => default

instance : Repr Choice where
  reprPrec
  | Choice.one n, _ => n.toString
  | Choice.many ns, _ => (Format.joinSep (ns.toList.map (·.toString)) "/").sbracket

inductive OptionVal
  | bool : Bool → OptionVal
  | str : String → OptionVal
  | nat : Nat → OptionVal
  | decimal : Nat → Nat → OptionVal

instance : Repr OptionVal where
  reprPrec
  | OptionVal.bool n, _ => repr n
  | OptionVal.nat n, _ => repr n
  | OptionVal.str n, _ => repr n
  | OptionVal.decimal n d, _ => repr n ++ "/" ++ repr d

inductive Level
  | «_» : Level
  | nat : Nat → Level
  | add : #Level → #Nat → Level
  | max : Array #Level → Level
  | imax : Array #Level → Level
  | param : Name → Level
  | paren : #Level → Level
  deriving Inhabited

def Levels := Option (Array #Level)
def LevelDecl := Option (Array #Name)
instance : Inhabited Levels := ⟨none⟩
instance : Inhabited LevelDecl := ⟨none⟩

-- These are used to break up the huge mutual recursion below
abbrev NotationId := Nat
abbrev CommandId := Nat

section
set_option hygiene false
local notation "Binders" => Array #Binder

mutual

  inductive Default
    | «:=» : #Expr → Default
    | «.» : #Name → Default

  inductive Binder
    | «notation» : NotationId → Binder
    | binder : BinderInfo → Option (Array #BinderName) →
      Binders → Option #Expr → Option Default → Binder
    | collection : BinderInfo → Array #BinderName →
      (nota : Name) → (rhs : #Expr) → Binder
    deriving Inhabited

  inductive LambdaBinder
    | reg : Binder → LambdaBinder
    | «⟨⟩» : Array #Expr → LambdaBinder
    deriving Inhabited

  inductive LetDecl
    | «notation» : NotationId → LetDecl
    | var : #BinderName → Binders → Option #Expr → #Expr → LetDecl
    | pat : #Expr → #Expr → LetDecl
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
    | const : #Name → Levels → Array Name → Expr
    | nat : Nat → Expr
    | decimal : Nat → Nat → Expr
    | string : String → Expr
    | char : Char → Expr
    | paren : #Expr → Expr
    | sort (isType isStar : Bool) : Option #Level → Expr
    | app : #Expr → #Expr → Expr
    | «fun» (isAssume : Bool) : Array #LambdaBinder → #Expr → Expr
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
    | infix_fn : Choice → Option #Expr → Expr
    | «(,)» : Array #Expr → Expr
    | «:» : #Expr → #Expr → Expr
    | hole : Array #Expr → Expr
    | «#[]» : Array #Expr → Expr
    | «by» : #Tactic → Expr
    | begin : Block → Expr
    | «let» : Array #LetDecl → #Expr → Expr
    | «match» : Array #Expr → Option #Expr → Array Arm → Expr
    | «do» (braces : Bool) : Array #DoElem → Expr
    | «{,}» : Array #Expr → Expr
    | subtype (setOf : Bool) : #Name → Option #Expr → #Expr → Expr
    | sep : #Name → #Expr → #Expr → Expr
    | setReplacement : #Expr → Binders → Expr
    | structInst (ty : Option #Name) (src : Option #Expr)
      (fields : Array (#Name × #Expr)) (srcs : Array #Expr) (catchall : Bool) : Expr
    | atPat : #Name → #Expr → Expr
    | «.()» : #Expr → Expr
    | «notation» (n : Choice) : Array #Arg → Expr
    | userNotation (n : Name) : Array #Param → Expr
    deriving Inhabited

  inductive Arm
    | mk (lhs : Array #Expr) (rhs : #Expr) : Arm
    deriving Inhabited

  inductive DoElem
    | «let» : #LetDecl → DoElem
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
    | parse : Lean3.Expr → Array #VMCall → Param
    | expr : #Expr → Param
    | block : Block → Param
    deriving Inhabited

  inductive VMCall
    | ident : Name → VMCall
    | nat : Nat → VMCall
    | token : String → VMCall
    | pat : Expr → VMCall
    | expr : Expr → VMCall
    | binders : Binders → VMCall
    | block : Block → VMCall
    | «inductive» : CommandId → VMCall
    | command : Option CommandId → VMCall
    | withInput : Array #VMCall → (bytesParsed : Nat) → VMCall
    deriving Inhabited

end
end

def Binders := Array #Binder
instance : Inhabited Binders := ⟨#[]⟩

partial def Expr.unparen : Expr → Expr
  | Expr.paren e => e.kind.unparen
  | e => e

inductive AttrArg
  | eager : AttrArg
  | indices : Array #Nat → AttrArg
  | keyValue : #String → #String → AttrArg
  | vmOverride : #Name → Option #Name → AttrArg
  | user : Lean3.Expr → Array #VMCall → AttrArg
  deriving Inhabited

inductive Attribute
  | priority : #Expr → Attribute
  | del (name : Name) : Attribute
  | add (name : Name) (arg : Option #AttrArg) : Attribute
  deriving Inhabited

def Attributes := Array #Attribute
instance : Inhabited Attributes := ⟨#[]⟩

inductive Precedence
  | nat : Nat → Precedence
  | expr : #Expr → Precedence
  deriving Inhabited

def PrecSymbol := #Symbol × Option #Precedence
instance : Inhabited PrecSymbol := inferInstanceAs (Inhabited (_×_))

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
  | «notation» : Option #Name → Array #Literal → Option #Expr → Notation
  | mixfix : MixfixKind → Option #Name → PrecSymbol → Option #Expr → Notation
  deriving Inhabited

inductive Modifier
  | «private» : Modifier
  | «protected» : Modifier
  | «noncomputable» : Modifier
  | meta : Modifier
  | «mutual» : Modifier
  | doc : String → Modifier
  | attr («local» compact : Bool) : Attributes → Modifier
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
  (mods : Modifiers) (lvls : LevelDecl) (bis : Binders) (vals : Array (Mutual α))
  deriving Inhabited

structure Intro where
  (doc : Option String) (name : #Name) (ik : Option InferKind) (bis : Binders) (ty : Option #Expr)

structure Rename := («from» to : #Name)

structure Parent where
  («private» : Bool) (name : Option #Name) (expr : #Expr) (renames : Array Rename)

structure Mk := (name : #Name) (ik : Option InferKind)

inductive Field
  | binder : BinderInfo → Array #Name → Option InferKind →
    Binders → Option #Expr → Option Default → Field
  | «notation» : Notation → Field

inductive OpenClause
  | explicit : Array #Name → OpenClause
  | «renaming» : Array Rename → OpenClause
  | «hiding» : Array #Name → OpenClause

structure Open :=
  (tgt : #Name) (as : Option #Name) (clauses : Array #OpenClause)

inductive HelpCmd
  | options : HelpCmd
  | commands : HelpCmd

inductive PrintAttrCmd
  | recursor : PrintAttrCmd
  | unify : PrintAttrCmd
  | simp : PrintAttrCmd
  | congr : PrintAttrCmd
  | attr : Name → PrintAttrCmd

def PrintAttrCmd.toName : PrintAttrCmd → Name
  | recursor => `recursor
  | unify => `unify
  | simp => `simp
  | congr => `congr
  | attr n => n

inductive PrintCmd
  | str : String → PrintCmd
  | raw : #Expr → PrintCmd
  | options : PrintCmd
  | trust : PrintCmd
  | keyEquivalences : PrintCmd
  | «def» : #Name → PrintCmd
  | instances : #Name → PrintCmd
  | classes : PrintCmd
  | attributes : PrintCmd
  | «prefix» : #Name → PrintCmd
  | aliases : PrintCmd
  | «axioms» : Option #Name → PrintCmd
  | fields : #Name → PrintCmd
  | «notation» : Array #Name → PrintCmd
  | «inductive» : #Name → PrintCmd
  | attr : #PrintAttrCmd → PrintCmd
  | token : #Name → PrintCmd
  | ident : #Name → PrintCmd

inductive InductiveCmd
  | reg («class» : Bool) : Modifiers → #Name → LevelDecl → Binders →
    (ty : Option #Expr) → Option Notation → Array #Intro → InductiveCmd
  | «mutual» («class» : Bool) : Modifiers → LevelDecl → Binders →
    Option Notation → Array (Mutual #Intro) → InductiveCmd

inductive Command
  | initQuotient : Command
  | mdoc : String → Command
  | «universe» (var plural : Bool) : Array #Name → Command
  | «namespace» : #Name → Command
  | «section» : Option #Name → Command
  | «end» : Option #Name → Command
  | «variable» : VariableKind → (plural : Bool) → Modifiers → Binders → Command
  | «axiom» : AxiomKind → Modifiers → #Name → LevelDecl → Binders → #Expr → Command
  | «axioms» : AxiomKind → Modifiers → Binders → Command
  | decl : DeclKind → Modifiers → Option #Name →
    LevelDecl → Binders → (ty : Option #Expr) → #DeclVal → (uwf : Option #Expr) → Command
  | mutualDecl : DeclKind → Modifiers → LevelDecl → Binders → Array (Mutual Arm) →
    (uwf : Option #Expr) → Command
  | «inductive» : InductiveCmd → Command
  | «structure» («class» : Bool) :
    Modifiers → #Name → LevelDecl → Binders → Array #Parent → (ty : Option #Expr) →
    Option #Mk → Array #Field → Command
  | «attribute» («local» : Bool) : Modifiers → Attributes → Array #Name → Command
  | «precedence» : #Symbol → #Precedence → Command
  | «notation» : LocalReserve → Attributes → Notation → Command
  | «open» («export» : Bool) : Array Open → Command
  | «include» (pos : Bool) : Array #Name → Command
  | «hide» : Array #Name → Command
  | «theory» : Modifiers → Command
  | setOption : #Name → #OptionVal → Command
  | declareTrace : #Name → Command
  | addKeyEquivalence : #Name → #Name → Command
  | runCmd : #Expr → Command
  | check : #Expr → Command
  | reduce (whnf : Bool) : #Expr → Command
  | eval : #Expr → Command
  | unify : #Expr → #Expr → Command
  | compile : #Name → Command
  | help : HelpCmd → Command
  | print : PrintCmd → Command
  | userCommand (n : Name) : Modifiers → Array #Param → Command
  deriving Inhabited

def spaced (f : α → Format) (mods : Array α) : Format :=
  (Format.joinSep (mods.toList.map f) Format.line).fill

def spacedBefore (f : α → Format) (mods : Array α) : Format :=
  (Format.join (mods.toList.map fun m => Format.line ++ f m)).fill

def spacedAfter (f : α → Format) (mods : Array α) : Format :=
  (Format.join (mods.toList.map fun m => f m ++ Format.line)).fill

def suffix (pl : Bool) := if pl then "s " else " "

partial def Level_repr : Level → (prec : _ := 0) → Format
  | Level.«_», _ => "_"
  | Level.nat n, _ => repr n
  | Level.add l n, p => Format.parenPrec 10 p $
    Level_repr l.kind 10 ++ "+" ++ repr n
  | Level.imax ls, p => Format.parenPrec max_prec p $
    "imax" ++ Format.join (ls.toList.map fun l => " " ++ Level_repr l.kind max_prec)
  | Level.max ls, p => Format.parenPrec max_prec p $
    "max" ++ Format.join (ls.toList.map fun l => " " ++ Level_repr l.kind max_prec)
  | Level.param u, _ => u.toString
  | Level.paren l, _ => Level_repr l.kind

instance : Repr Level := ⟨@Level_repr⟩

instance : Repr Levels where
  reprPrec
  | none, _ => ""
  | some us, _ => (Format.joinSep (us.toList.map repr) ", ").bracket ".{" "}"

instance : Repr LevelDecl where
  reprPrec
  | none, _ => ""
  | some us, _ => (Format.joinSep (us.toList.map fun u => u.kind.toString) ", ").bracket ".{" "}"

mutual

  partial def Precedence_repr : Precedence → Format
    | Precedence.nat n => repr n
    | Precedence.expr e => Expr_repr e.kind max_prec

  partial def optTy : Option #Expr → Format
    | none => ""
    | some e => " :" ++ Format.line ++ Expr_repr e.kind

  partial def Default_repr : Option Default → Format
    | none => ""
    | some (Default.«:=» e) => " :=" ++ Format.line ++ Expr_repr e.kind
    | some (Default.«.» n) => " ." ++ Format.line ++ (n.kind.toString : Format)

  partial def Binder_repr : Binder → (paren :_:= true) → Format
    | Binder.binder bi none _ e dflt, paren => bi.bracket paren $
      (match e with | none => "⬝" | some e => Expr_repr e.kind) ++
      Default_repr dflt
    | Binder.binder bi (some vars) bis ty dflt, paren => bi.bracket paren $
      spaced repr vars ++ Binders_repr bis ++ optTy ty ++ Default_repr dflt
    | Binder.collection bi vars n rhs, paren => bi.bracket paren $
      spaced repr vars ++ " " ++ n.toString ++ " " ++ Expr_repr rhs.kind
    | Binder.notation n, _ => Format.paren s!"notation <{show Nat from n}>"

  partial def Binders_repr (bis : Binders) (paren := true) : Format :=
    let paren := paren || bis.size ≠ 1
    spacedBefore (fun m => Binder_repr m.kind paren) bis

  partial def LambdaBinder_repr : LambdaBinder → (paren :_:= true) → Format
    | LambdaBinder.reg bi, paren => Binder_repr bi paren
    | LambdaBinder.«⟨⟩» args, _ =>
      (Format.joinSep (args.toList.map fun e => Expr_repr e.kind) ", ").bracket "⟨" "⟩"

  partial def LambdaBinders_repr (bis : Array #LambdaBinder) (paren := true) : Format :=
    let paren := paren || bis.size ≠ 1
    spacedBefore (fun m => LambdaBinder_repr m.kind paren) bis

  partial def LetDecl_repr : LetDecl → Format
    | LetDecl.var v bis ty val =>
      repr v ++ Binders_repr bis ++ optTy ty ++ " := " ++ Expr_repr val.kind
    | LetDecl.pat pat val => Expr_repr pat.kind ++ " := " ++ Expr_repr val.kind
    | LetDecl.notation n => s!"notation <{show Nat from n}>"

  partial def Expr_repr : Expr → (prec : _ := 0) → Format
    | Expr.«...», _ => "..."
    | Expr.sorry, _ => "sorry"
    | Expr.«_», _ => "_"
    | Expr.«()», _ => "()"
    | Expr.«{}», _ => "{}"
    | Expr.ident n, _ => n.toString
    | Expr.const n l cs, _ => n.kind.toString ++ cs.toList.toString ++ repr l
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
      ((if as then "assume" else "λ" : Format) ++
      (match as, bis with
        | true, #[⟨_, .reg (.binder _ none _ (some ty) _)⟩] => ": " ++ Expr_repr ty.kind
        | _, _ => LambdaBinders_repr bis false) ++
      ",").group ++ Format.line ++ Expr_repr e.kind
    | Expr.Pi bis e, p => Format.parenPrec max_prec p $ ("∀" ++
      Binders_repr bis false ++ ",").group ++ Format.line ++ Expr_repr e.kind
    | Expr.app f x, p => Format.parenPrec max_prec p $
      (Expr_repr f.kind 1023 ++ Format.line ++ Expr_repr x.kind max_prec).fill
    | Expr.show t pr, p => Format.parenPrec 1000 p $
      "show " ++ Expr_repr t.kind ++ Proof_repr' pr.kind
    | Expr.have suff h t pr e, p => Format.parenPrec 1000 p $
      (if suff then "suffices " else "have ") ++
      (match h with | none => "" | some h => h.kind.toString ++ " : ") ++
      Expr_repr t.kind ++ Proof_repr' pr.kind ++
      "," ++ Format.line ++ Expr_repr e.kind
    | Expr.«.» compact e pr, _ =>
      Expr_repr e.kind max_prec ++ (if compact then "." else "^.") ++ repr pr.kind
    | Expr.if h c t e, p => Format.parenPrec 1000 p $ "if " ++
      (match h with | none => "" | some h => h.kind.toString ++ " : ") ++
      Expr_repr c.kind ++ " then " ++ Expr_repr t.kind ++ " else " ++ Expr_repr e.kind
    | Expr.calc args, p => Format.parenPrec 1000 p $ "calc" ++
      (Format.join $ args.toList.map fun (lhs, rhs) =>
        Format.line ++ Expr_repr lhs.kind ++ " : " ++ Expr_repr rhs.kind).nest 2
    | Expr.«@» part e, _ => (if part then "@@" else "@") ++ Expr_repr e.kind max_prec
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
    | Expr.«⟨⟩» es, _ =>
      (Format.joinSep (es.toList.map fun e => Expr_repr e.kind) ", ").bracket "⟨" "⟩"
    | Expr.infix_fn c e, p => Format.parenPrec 1000 p $
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
        (bis.toList.map fun bi => LetDecl_repr bi.kind)).nest 4 ++ " in").group ++
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
      "{(" ++ Expr_repr e.kind ++ ") |" ++ Binders_repr bis false ++ "}"
    | Expr.structInst S src flds srcs catchall, _ => Format.nest 2 $ Format.group $ "{ " ++
      (match S with | none => "" | some S => S.kind.toString ++ " ." ++ Format.line : Format) ++
      (match src with | none => "" | some s => Expr_repr s.kind ++ " with" ++ Format.line : Format) ++
      (("," ++ Format.line).joinSep $
        flds.toList.map (fun (i, s) => i.kind.toString ++ " := " ++ Expr_repr s.kind) ++
        srcs.toList.map (fun s => ".." ++ Expr_repr s.kind) ++
        if catchall then [(".." : Format)] else []) ++ " }"
    | Expr.atPat lhs rhs, p => Format.parenPrec 1000 p $
      lhs.kind.toString ++ "@" ++ Expr_repr rhs.kind max_prec
    | Expr.notation n args, _ => repr n ++
      (Format.joinSep (args.toList.map fun e => Arg_repr e.kind) ("," ++ Format.line)).paren
    | Expr.userNotation n args, p => Format.parenPrec 1000 p $ n.toString ++
      Format.join (args.toList.map fun a => " " ++ Param_repr a.kind)

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
    | DoElem.let bi => "let " ++ LetDecl_repr bi.kind
    | DoElem.«←» lhs ty rhs els =>
      Expr_repr lhs.kind ++ optTy ty ++ " ← " ++ Expr_repr rhs.kind ++
      match els with | none => "" | some e => " | " ++ Expr_repr e.kind
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
      let s₃ := ("," ++ Format.line).joinSep (tacs.toList.map fun t => Tactic_repr t.kind)
      if curly then
        ("{" ++ s₁ ++ s₂ ++ (if cl.isSome || cfg.isSome then Format.line else " ") ++ s₃ ++ " }").nest 2
      else
        ("begin" ++ s₁ ++ s₂ ++ Format.line ++ s₃).nest 2 ++ Format.line ++ "end"

  partial def Param_repr : Param → Format
    | Param.parse _ calls => Format.sbracket $
      (", ":Format).joinSep $ calls.toList.map fun c => VMCall_repr c.kind
    | Param.expr e => Expr_repr e.kind
    | Param.block e => Block_repr e

  partial def VMCall_repr : VMCall → Format
    | VMCall.ident n => "ident " ++ (n.toString:Format)
    | VMCall.nat n => repr n
    | VMCall.token tk => repr tk
    | VMCall.pat e => "pat " ++ Expr_repr e
    | VMCall.expr e => "expr " ++ Expr_repr e
    | VMCall.binders bis => "binders" ++ Binders_repr bis
    | VMCall.block bl => Block_repr bl
    | VMCall.inductive c => s!"inductive <{show Nat from c}>"
    | VMCall.command c => s!"command <{repr $ show Option Nat from c}>"
    | VMCall.withInput calls _ => Format.sbracket $
      (", ":Format).joinSep $ calls.toList.map fun c => VMCall_repr c.kind

  partial def optPrec_repr : Option #Precedence → Format
    | none => ""
    | some p => ":" ++ Precedence_repr p.kind

  partial def PrecSymbol_repr : PrecSymbol → Format
    | (sym, prec) => repr sym ++ optPrec_repr prec

  partial def Action_repr : Action → Format
    | Action.prec p => Precedence_repr p
    | Action.prev => "prev"
    | Action.scoped p none => "scoped" ++ optPrec_repr p
    | Action.scoped p (some (x, e)) =>
      "(scoped" ++ optPrec_repr p ++ " " ++ x.kind.toString ++ ", " ++ Expr_repr e.kind ++ ")"
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
instance : Repr VMCall := ⟨fun n _ => VMCall_repr n⟩
instance : Repr PrecSymbol := ⟨fun n _ => PrecSymbol_repr n⟩
instance : Repr Action := ⟨fun n _ => Action_repr n⟩
instance : Repr Literal := ⟨fun n _ => Literal_repr n⟩

instance : Repr AttrArg where reprPrec
  | AttrArg.eager, _ => "!"
  | AttrArg.indices ns, _ => spacedBefore repr ns
  | AttrArg.keyValue a b, _ => " " ++ repr a ++ " " ++ repr b
  | AttrArg.vmOverride a b, _ => " " ++ repr a ++
    (match b with | none => "" | some b => " " ++ repr b : Format)
  | AttrArg.user _ e, _ => repr e

instance : Repr Attribute where reprPrec
  | Attribute.priority e, _ => "priority " ++ Expr_repr e.kind
  | Attribute.del n, _ => ("-":Format) ++ n.toString
  | Attribute.add n arg, _ => n.toString ++
    (match arg with | none => "" | some arg => " " ++ repr arg : Format)

instance : Repr Attributes :=
  ⟨fun attrs _ =>  (Format.joinSep (attrs.toList.map repr) ", ").sbracket⟩

def Notation_repr : Notation → (attrs : Attributes := #[]) → Format
  | Notation.mixfix mk name sym val, attrs => repr mk ++
    (if attrs.isEmpty then "" else " " ++ repr attrs : Format) ++
    (match name with | none => "" | some n => f!" (name := {repr n})") ++
    " " ++ PrecSymbol_repr sym ++
    (match val with | none => "" | some e => " := " ++ Expr_repr e.kind)
  | Notation.notation name lits val, attrs => "notation" ++
    (if attrs.isEmpty then "" else " " ++ repr attrs : Format) ++
    (match name with | none => "" | some n => f!" (name := {repr n})") ++
    spacedBefore (fun n => Literal_repr n.kind) lits ++
    (match val with | none => "" | some e => " := " ++ Expr_repr e.kind)

instance : Repr Notation := ⟨fun n _ => Notation_repr n⟩

instance : Repr DeclVal where reprPrec
  | DeclVal.expr n, _ => " :=" ++ Format.line ++ repr n
  | DeclVal.eqns arms, _ => Format.join (arms.toList.map repr)

instance : Repr Modifier where reprPrec
  | Modifier.private, _ => "private"
  | Modifier.protected, _ => "protected"
  | Modifier.noncomputable, _ => "noncomputable"
  | Modifier.meta, _ => "meta"
  | Modifier.mutual, _ => "mutual"
  | Modifier.doc s, _ => ("/--" ++ s ++ "-/" : String)
  | Modifier.attr l c attrs, _ =>
    (if l then "local " else "") ++ (if c then "@" else "attribute ") ++ repr attrs

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
    if rens.isEmpty then ("":Format) else "renaming" ++ spacedBefore repr rens

instance : Repr Field where reprPrec
  | Field.binder bi vars ik bis ty dflt, _ => bi.bracket true $
    spaced (fun v => v.kind.toString) vars ++ InferKind.optRepr ik ++
    Binders_repr bis ++ optTy ty ++ Default_repr dflt
  | Field.notation n, _ => (repr n).paren

instance : Repr OpenClause where reprPrec
  | OpenClause.explicit ns, _ => spaced (fun n => n.kind.toString) ns
  | OpenClause.renaming rens, _ => "renaming" ++ spacedBefore repr rens
  | OpenClause.hiding ns, _ => "hiding" ++ spacedBefore (fun n => n.kind.toString) ns

instance : Repr Open where reprPrec
  | ⟨tgt, as, cls⟩, _ => tgt.kind.toString ++
    (match as with | none => "" | some as => " as " ++ as.kind.toString) ++
    spacedBefore (fun i => (repr i).paren) cls

instance : Repr HelpCmd where
  reprPrec
  | HelpCmd.options, _ => "options"
  | HelpCmd.commands, _ => "commands"

instance : Repr PrintCmd where reprPrec c _ := match c with
  | PrintCmd.str n => repr n
  | PrintCmd.raw e => "raw " ++ (repr e).nest 2
  | PrintCmd.options => "options"
  | PrintCmd.trust => "trust"
  | PrintCmd.keyEquivalences => "key_equivalences"
  | PrintCmd.def n => "def " ++ repr n
  | PrintCmd.instances n => ("instances " : Format) ++ n.kind.toString
  | PrintCmd.classes => "classes"
  | PrintCmd.attributes => "attributes"
  | PrintCmd.prefix n => ("prefix " : Format) ++ n.kind.toString
  | PrintCmd.aliases => "aliases"
  | PrintCmd.axioms n => ("axioms" : Format) ++
    (match n with | none => "" | some n => " " ++ n.kind.toString : String)
  | PrintCmd.fields n => ("fields " : Format) ++ n.kind.toString
  | PrintCmd.notation ns => ("notation" : Format) ++ spacedBefore (fun n => n.kind.toString) ns
  | PrintCmd.inductive n => ("inductive " : Format) ++ n.kind.toString
  | PrintCmd.attr n => (n.kind.toName.toString : Format).sbracket
  | PrintCmd.token n => n.kind.toString
  | PrintCmd.ident n => n.kind.toString

instance : Repr InductiveCmd where reprPrec c _ := match c with
  | InductiveCmd.reg cl mods n us bis ty nota intros =>
    repr mods ++ (if cl then "class " else "") ++ "inductive " ++
    n.kind.toString ++ repr us ++ repr bis ++ optTy ty ++
    (match nota with | none => "" | some n => "\n" ++ repr n) ++
    Intros_repr intros
  | InductiveCmd.mutual cl mods us bis nota inds =>
    repr mods ++ (if cl then "class " else "") ++ "inductive " ++ repr us ++
    Format.joinSep (inds.toList.map fun m => m.name.kind.toString) ", " ++ repr bis ++
    (match nota with | none => "" | some n => "\n" ++ repr n) ++
    Format.join (inds.toList.map (Mutual_repr Intros_repr))

instance : Repr Command where reprPrec c _ := match c with
  | Command.initQuotient => "init_quotient"
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
  | Command.decl dk mods n us bis ty val uwf =>
    repr mods ++ (repr dk ++
    (match n with | none => "" | some n => " " ++ n.kind.toString : String) ++
    repr us ++ repr bis ++ optTy ty).group.nest 2 ++ repr val.kind ++
    (match uwf with | none => "" | some e => "\nusing_well_founded " ++ (repr e).nest 2)
  | Command.mutualDecl dk mods us bis arms uwf =>
    repr mods ++ repr dk ++ " " ++ repr us ++
    Format.joinSep (arms.toList.map fun m => m.name.kind.toString) ", " ++
    repr bis ++ Format.join (arms.toList.map (Mutual_repr Arms_repr)) ++
    (match uwf with | none => "" | some e => "\nusing_well_founded " ++ (repr e).nest 2)
  | Command.inductive ind => repr ind
  | Command.structure cl mods n us bis exts ty mk flds =>
    repr mods ++ (if cl then "class " else "structure ") ++
    n.kind.toString ++ repr us ++ repr bis ++
    (if exts.isEmpty then ("":Format) else "extends " ++
      ((", ":Format).joinSep $ exts.toList.map repr)) ++ optTy ty ++
    if mk.isNone && flds.isEmpty then ("":Format) else " :=" ++
    (match mk with | none => "" | some mk => " " ++ repr mk ++
      if flds.isEmpty then "" else " ::" : Format) ++
    ((Format.join $ flds.toList.map fun f => Format.line ++ repr f).group).nest 2
  | Command.attribute loc mods attrs ns =>
    repr mods ++ (if loc then "local " else "") ++ "attribute" ++
    (if attrs.isEmpty then "" else " " ++ repr attrs : Format) ++ spacedBefore (fun n => n.kind.toString) ns
  | Command.precedence sym prec => "precedence " ++ repr sym ++ ":" ++ repr prec
  | Command.notation loc attrs n => repr loc ++ Notation_repr n attrs
  | Command.open exp ops => (if exp then "export" else "open") ++ spacedBefore repr ops
  | Command.include pos ops => (if pos then "include" else "omit") ++
    spacedBefore (fun n => n.kind.toString) ops
  | Command.hide ops => "hide" ++ spacedBefore (fun n => n.kind.toString) ops
  | Command.theory mods => repr mods ++ "theory"
  | Command.setOption n val => "set_option " ++ n.kind.toString ++ " " ++ repr val
  | Command.declareTrace n => ("declare_trace " : Format) ++ n.kind.toString
  | Command.addKeyEquivalence a b => ("add_key_equivalence " : Format) ++
    a.kind.toString ++ " " ++ b.kind.toString
  | Command.runCmd e => "run_cmd " ++ (repr e).nest 2
  | Command.check e => "#check " ++ (repr e).nest 2
  | Command.reduce whnf e => "#reduce " ++ (if whnf then "[whnf] " else "") ++ (repr e).nest 2
  | Command.eval e => "#eval " ++ (repr e).nest 2
  | Command.unify e₁ e₂ => "#unify " ++ (repr e₁ ++ ", " ++ repr e₂).nest 2
  | Command.compile n => ("#compile ":Format) ++ n.kind.toString
  | Command.help n => "#help " ++ repr n
  | Command.print n => "#print " ++ repr n
  | Command.userCommand n mods args => repr mods ++ n.toString ++
    Format.join (args.toList.map fun a => " " ++ Param_repr a.kind)

def Notation.name (sp : Char) (f : PrecSymbol → String) (withTerm : Bool) (start : String) :
  Notation → Name
| Notation.notation (some name) .. | Notation.mixfix _ (some name) .. => name.kind
| Notation.notation none lits _ => Id.run do
  let mut s := start
  for ⟨_, lit⟩ in lits do
    match lit with
    | Literal.nat n => s := s ++ toString n
    | Literal.sym tk => s := s ++ f tk
    | Literal.var _ none => s := s.push sp
    | Literal.var _ (some ⟨_, Action.prec _⟩) => s := s.push sp
    | Literal.var _ (some ⟨_, Action.prev⟩) => s := s.push sp
    | Literal.var _ (some ⟨_, Action.scoped _ _⟩) => s := s.push sp
    | Literal.var _ (some ⟨_, Action.fold _ _ sep _ _ term⟩) =>
      s := s.push sp ++ f sep
      if withTerm then if let some term := term then s := s ++ f term
    | Literal.binder _ => s := s.push sp
    | Literal.binders _ => s := s.push sp
  Name.mkSimple s
| Notation.mixfix mk none tk _ =>
  Name.mkSimple <| match mk with
  | MixfixKind.infix => start.push sp ++ (f tk).push sp
  | MixfixKind.infixl => start.push sp ++ (f tk).push sp
  | MixfixKind.infixr => start.push sp ++ (f tk).push sp
  | MixfixKind.postfix => start.push sp ++ f tk
  | MixfixKind.prefix => start ++ (f tk).push sp

def Notation.name3 := Notation.name ' ' (·.1.kind.trim) true "expr"
def Notation.name4 := Notation.name '_' (·.1.kind.trim) false "term"

structure Hyp where
  name : Name
  pp : Name
  type : Lean3.Expr
  value : Option Lean3.Expr

instance : Repr Hyp where reprPrec
  | ⟨_, pp, t, v⟩, _ =>
    pp.toString ++ " : " ++ repr t ++
    match v with | none => ("":Format) | some v => repr v

structure Goal where
  hyps : Array Hyp
  target : Lean3.Expr

instance : Repr Goal where reprPrec
  | ⟨hyps, target⟩, _ =>
    Format.join (hyps.toList.map fun hyp => repr hyp ++ "\n") ++
    "⊢ " ++ repr target

def Goals_repr (gs : Array Goal) : Format :=
  Format.join (gs.toList.map fun g => repr g ++ "\n")

structure TacticInvocation where
  declName : Name
  ast      : Option #Tactic
  start    : Array Goal
  «end»    : Array Goal
  success  : Bool

instance : Repr TacticInvocation where reprPrec
  | ⟨declName, tac, start, end_, success⟩, _ =>
    "in declaration " ++ toString declName ++ " " ++
    "invoking " ++ repr tac ++ ":\n" ++
    "before:\n" ++ Goals_repr start ++
    (if success then "success" else "failed") ++ ", after:\n" ++ Goals_repr end_

structure Comment where
  start : Position
  «end» : Position
  text : String
  deriving Repr, Inhabited

end AST3

structure AST3 where
  «prelude» : Option #Unit
  «import» : Array (Array #Name)
  commands : Array (Spanned AST3.Command)
  indexed_nota : Array AST3.Notation
  indexed_cmds : Array AST3.Command
  comments : Array AST3.Comment

instance : Repr AST3 where reprPrec
  | ⟨prel, imps, cmds, _, _, _⟩, _ =>
    (match prel with | none => "" | some _ => "prelude\n") ++
    Format.join (imps.toList.map fun ns =>
      "import " ++ Format.joinSep (ns.toList.map fun a => a.kind.toString) " " ++ "\n") ++
    "\n" ++ Format.join (cmds.toList.map fun c => repr c ++ "\n\n")

partial def Spanned.unparen : #AST3.Expr → #AST3.Expr
  | ⟨_, AST3.Expr.paren e⟩ => e.unparen
  | e => e

end Mathport
