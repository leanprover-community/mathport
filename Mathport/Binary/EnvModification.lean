/-
Copyright (c) 2021 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Selsam
-/
import Lean
import Std.Data.HashSet
import Std.Data.HashMap
import Mathport.Util.Misc

namespace Mathport.Binary

open Lean

inductive MixfixKind
  | «prefix»
  | «infixl»
  | «infixr»
  | «postfix»
  | «singleton»
  deriving Repr

def MixfixKind.toAttr : MixfixKind → Name
  | MixfixKind.prefix     => `Lean.Parser.Command.prefix
  | MixfixKind.postfix    => `Lean.Parser.Command.postfix
  | MixfixKind.infixl     => `Lean.Parser.Command.infixl
  | MixfixKind.infixr     => `Lean.Parser.Command.infixr
  | MixfixKind.singleton  => `Lean.Parser.Command.notation

deriving instance BEq for ReducibilityStatus

structure ExportDecl : Type where
  currNs : Name
  ns   : Name
  nsAs : Name
  hadExplicit : Bool
  renames : Array (Name × Name)
  exceptNames : Array Name
  deriving Repr

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
  | position       : (name : Name) → (line col : Nat) → EnvModification

def EnvModification.toName : EnvModification → Name
  | EnvModification.decl d             => d.toName
  | EnvModification.class c            => c
  | EnvModification.instance _ i _     => i
  | EnvModification.simp n _           => n
  | EnvModification.private _ real     => real
  | EnvModification.protected n        => n
  | EnvModification.reducibility n _   => n
  | EnvModification.mixfix _ n _ _     => n
  | EnvModification.export _           => `inExport
  | EnvModification.projection p       => p.projName
  | EnvModification.position n _ _     => n

open EnvModification in
instance : ToString EnvModification where
  toString
    | decl d             => s!"<decl:{d.toName}>"
    | «class» c          => s!"class {c}"
    | «instance» c i ..  => s!"instance {c} {i}"
    | simp n prio        => s!"simp {n} {prio}"
    | «private» _ _      => "private"
    | «protected» _      => "protected"
    | «reducibility» _ _ => "reducibility"
    | «mixfix» _ _ _ _   => "mixfix"
    | «export» _         => "export"
    | «projection» _     => "projection"
    | position n _ _     => s!"position {n}"

end Mathport.Binary
