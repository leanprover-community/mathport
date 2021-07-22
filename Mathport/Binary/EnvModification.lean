/-
Copyright (c) 2021 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Selsam
-/
import Lean
import Std.Data.HashSet
import Std.Data.HashMap
import Mathport.Binary.Path

namespace Mathport.Binary

open Lean

inductive MixfixKind
| «prefix»
| «infixl»
| «infixr»
| «postfix»
| «singleton»

def MixfixKind.toAttr : MixfixKind → Name
| MixfixKind.prefix     => `Lean.Parser.Command.prefix
| MixfixKind.postfix    => `Lean.Parser.Command.postfix
| MixfixKind.infixl     => `Lean.Parser.Command.infixl
| MixfixKind.infixr     => `Lean.Parser.Command.infixr
| MixfixKind.singleton  => `Lean.Parser.Command.notation

instance : ToString MixfixKind :=
  ⟨λ
    | MixfixKind.prefix    => "prefix"
    | MixfixKind.postfix   => "postfix"
    | MixfixKind.infixl    => "infixl"
    | MixfixKind.infixr    => "infixr"
    | MixfixKind.singleton => "notation"⟩

instance : BEq ReducibilityStatus :=
  ⟨λ
    | ReducibilityStatus.reducible,     ReducibilityStatus.reducible     => true
    | ReducibilityStatus.semireducible, ReducibilityStatus.semireducible => true
    | ReducibilityStatus.irreducible,   ReducibilityStatus.irreducible   => true
    | _, _                                                               => false⟩

structure ExportDecl : Type where
  currNs : Name
  ns   : Name
  nsAs : Name
  hadExplicit : Bool
  renames : Array (Name × Name)
  exceptNames : Array Name

structure ProjectionInfo : Type where
  -- pr_i A.. (mk A f_1 ... f_n) ==> f_i
  projName  : Name -- pr_i
  ctorName  : Name -- mk
  nParams   : Nat  -- |A..|
  index     : Nat  -- i
  fromClass : Bool
  deriving Repr

inductive EnvModification : Type
| decl           : Declaration → EnvModification
| «class»        : (c : Name) → EnvModification
| «instance»     : (c i : Name) → (prio : Nat) → EnvModification
| simp           : (name : Name) → (prio : Nat) → EnvModification
| «private»      : (pretty real : Name) → EnvModification
| «protected»    : (name : Name) → EnvModification
| «reducibility» : (name : Name) → ReducibilityStatus → EnvModification
| «mixfix»       : MixfixKind → Name → Nat → String → EnvModification
| «export»       : ExportDecl → EnvModification
| «projection»   : ProjectionInfo → EnvModification

def EnvModification.toName : EnvModification → Name
  | EnvModification.decl d             =>
    match d with
    | Declaration.defnDecl d => d.name
    | Declaration.thmDecl d  => d.name
    | _                      => Name.anonymous
  | EnvModification.class c            => c
  | EnvModification.instance _ i _     => i
  | EnvModification.simp n _           => n
  | EnvModification.private _ real     => real
  | EnvModification.protected n        => n
  | EnvModification.reducibility n _   => n
  | EnvModification.mixfix _ n _ _     => n
  | EnvModification.export _           => `inExport
  | EnvModification.projection p       => p.projName

end Mathport.Binary
