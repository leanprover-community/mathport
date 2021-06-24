/-
Copyright (c) 2021 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Daniel Selsam
-/
import Mathport.Util

def Lean.BinderInfo.bracket : BinderInfo → Format → Format
  | BinderInfo.default,        f => f.bracket "(" ")"
  | BinderInfo.implicit,       f => f.bracket "{" "}"
  | BinderInfo.strictImplicit, f => f.bracket "{{" "}}"
  | BinderInfo.instImplicit,   f => f.bracket "[" "]"
  | BinderInfo.auxDecl,        f => f.group

namespace Mathport

open Lean (Position Name BinderInfo)
open Std (Format)

structure Spanned (α : Type u) where
  start : Position
  end_ : Position
  kind  : α
  deriving Inhabited, Repr

def Spanned.map (f : α → β) : Spanned α → Spanned β
  | ⟨s, e, a⟩ => ⟨s, e, f a⟩

local prefix:max "*" => Spanned

namespace AST3

inductive VariableKind | «variable» | «parameter»

instance : Repr VariableKind where
  reprPrec
  | VariableKind.«variable», _ => "variable"
  | VariableKind.«parameter», _ => "parameter"

inductive DeclKind
| «axiom» | «constant» | «def» | «theorem»
| «abbrev» | «example» | «instance»

instance : Repr DeclKind where
  reprPrec
  | DeclKind.«axiom», _ => "axiom"
  | DeclKind.«constant», _ => "constant"
  | DeclKind.«def», _ => "def"
  | DeclKind.«theorem», _ => "theorem"
  | DeclKind.«abbrev», _ => "abbreviation"
  | DeclKind.«example», _ => "example"
  | DeclKind.«instance», _ => "instance"

section
set_option hygiene false
local notation "Modifiers" => Array *Modifier
local notation "Binders" => Array *Binder
local notation "Node" => *NodeK
local notation "Levels" => Option (Array *Level)

mutual

inductive Other
  | mk (kind : String) (value : Name) (children : Array (Option Node)) : Other
  deriving Inhabited

inductive Attribute
  | mk (del : Bool) (name : *Name) (args : Array (Option Node)) : Attribute
  deriving Inhabited

inductive Modifier
  | doc : String → Modifier
  | attr («local» compact : Bool) : Array *Attribute → Modifier
  | other : Other → Modifier
  deriving Inhabited

inductive Binder
  | binder : BinderInfo → Option (Array *Name) → Binders → *Expr → Binder
  | other : Other → Binder
  deriving Inhabited

inductive Level
  | other : Other → Level
  deriving Inhabited

inductive Expr
  | other : Other → Expr
  deriving Inhabited

inductive Arm
  | mk (lhs : Array *Expr) (rhs : *Expr) : Arm
  deriving Inhabited

inductive DeclVal
  | expr : Expr → DeclVal
  | eqns : Array Arm → DeclVal
  deriving Inhabited

inductive Command
  | «prelude» : Command
  | «import» : Array *Name → Command
  | mdoc : String → Command
  | «universe» (var plural : Bool) : Array *Name → Command
  | «namespace» : *Name → Command
  | «section» : Option *Name → Command
  | «end» : Option *Name → Command
  | «variable» : VariableKind → Modifiers → (plural : Bool) → Binders → Command
  | decl : DeclKind → Modifiers → Option *Name →
    Levels → Binders → (ty : Option *Expr) → Option *DeclVal → Command
  -- | mutual_decl : DeclKind → Modifiers → Binders → Command
  | other : Other → Command
  deriving Inhabited

inductive NodeK
  | name : Name → NodeK
  | str : String → NodeK
  | cmd : Command → NodeK
  | mod : Modifier → NodeK
  | binder : Binder → NodeK
  | level : Level → NodeK
  | expr : Expr → NodeK
  | declVal : DeclVal → NodeK
  | other : Other → NodeK
  deriving Inhabited

end
end

abbrev Modifiers := Array *Modifier
abbrev Binders := Array *Binder
abbrev Node := *NodeK
abbrev Levels := Option (Array *Level)

def spaced (f : α → Format) (mods : Array α) : Format :=
  Format.join (mods.toList.map fun m => f m ++ Format.line)

def suffix (pl : Bool) := if pl then "s " else " "
mutual

partial def optNode_repr : Option Node → Format
  | none => ("⬝" : Format)
  | some a => NodeK_repr a.kind

partial def Other_repr : Other → Format
  | ⟨k, v, c⟩ => k ++
    (if v.isAnonymous then "" else "(" ++ v.toString ++ ")" ) ++
    (if c.isEmpty then ("":Format) else
      (("," ++ Format.line).joinSep (c.toList.map optNode_repr)).bracket "[" "]")

partial def Attribute_repr : Attribute → Format
  | ⟨del, n, args⟩ =>
    (if del then "-" else "") ++ n.kind.toString ++
    Format.join (args.toList.map fun
      | none => ("⬝" : Format)
      | some a => NodeK_repr a.kind)

partial def Modifier_repr : Modifier → Format
  | Modifier.doc s => ("/--" ++ s ++ "-/" : String)
  | Modifier.attr l c attrs =>
    (if l then "local " else "") ++
    (Format.joinSep (attrs.toList.map fun u => Attribute_repr u.kind) ", ").bracket
      (if c then "@[" else "attribute [") "]"
  | Modifier.other n => Other_repr n

partial def Binder_repr : Binder → Format
  | Binder.binder bi none _ e => bi.bracket (Expr_repr e.kind)
  | Binder.binder bi (some vars) bis e => bi.bracket $
    spaced (fun v => v.kind.toString) vars ++ Binders_repr bis ++ ": " ++ Expr_repr e.kind
  | Binder.other n => Other_repr n

partial def Level_repr : Level → Format
  | Level.other n => Other_repr n

partial def Expr_repr : Expr → Format
  | Expr.other n => Other_repr n

partial def Arm_repr : Arm → Format
  | ⟨lhs, rhs⟩ =>
    "\n| " ++ Format.joinSep (lhs.toList.map fun e => Expr_repr e.kind) ", " ++
    " := " ++ Expr_repr rhs.kind

partial def DeclVal_repr : DeclVal → Format
  | DeclVal.expr n => " :=\n" ++ Expr_repr n
  | DeclVal.eqns arms => if arms.isEmpty then "." else
    Format.join $ arms.toList.map Arm_repr

partial def Modifiers_repr : Modifiers → Format := spaced fun m => Modifier_repr m.kind

partial def Binders_repr : Binders → Format := spaced fun m => Binder_repr m.kind

partial def optTy : Option *Expr → Format
  | none => ""
  | some e => ": " ++ Expr_repr e.kind

partial def Levels_repr : Levels → Format
  | none => ""
  | some us => (Format.joinSep (us.toList.map fun u => Level_repr u.kind) ", ").bracket ".{" "}"

partial def Command_repr : Command → Format
  | Command.«prelude» => "prelude"
  | Command.«import» ns => "import " ++ Format.joinSep (ns.toList.map fun a => a.kind.toString) " "
  | Command.mdoc s => ("/-!" ++ s ++ "-/" : String)
  | Command.«universe» var pl ns =>
    "universe" ++ (if var then " variable" else "") ++ suffix pl ++
    Format.join (ns.toList.map fun a => (" ":Format) ++ a.kind.toString)
  | Command.«namespace» n => ("namespace ":Format) ++ n.kind.toString
  | Command.«section» (some n) => ("section ":Format) ++ n.kind.toString
  | Command.«section» none => "section"
  | Command.«end» (some n) => ("end ":Format) ++ n.kind.toString
  | Command.«end» none => "end"
  | Command.«variable» vk mods plural bis =>
    Modifiers_repr mods ++ repr vk ++ (if plural then "s " else " ") ++ Binders_repr bis
  | Command.decl dk mods n us bis ty val =>
    Modifiers_repr mods ++ repr dk ++
    (match n with | none => "" | some n => " " ++ n.kind.toString : String) ++
    Levels_repr us ++ " " ++ Binders_repr bis ++
    (match ty with | none => "" | some ty => ": " ++ Expr_repr ty.kind) ++
    (match val with | none => "" | some val => DeclVal_repr val.kind)
  -- | Command.mutual_decl dk mods bis =>
  --   Modifiers_repr mods ++ repr dk ++ " " ++ Binders_repr bis
  | Command.other n => Other_repr n

partial def NodeK_repr : NodeK → Format
  | NodeK.name n => n.toString
  | NodeK.str n => repr n
  | NodeK.cmd n => Command_repr n
  | NodeK.mod n => Modifier_repr n
  | NodeK.binder n => Binder_repr n
  | NodeK.level n => Level_repr n
  | NodeK.expr n => Expr_repr n
  | NodeK.declVal n => DeclVal_repr n
  | NodeK.other n => Other_repr n

end

instance : Repr Other := ⟨fun n _ => Other_repr n⟩
instance : Repr Command := ⟨fun n _ => Command_repr n⟩
instance : Repr NodeK := ⟨fun n _ => NodeK_repr n⟩


end AST3

structure AST3 where
  commands : Array (Spanned AST3.Command)
  deriving Inhabited, Repr

end Mathport
