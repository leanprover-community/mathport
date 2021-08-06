/-
Copyright (c) 2021 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
import Std.Data.HashMap
import Mathport.Util.Json
import Mathport.Util.Misc
import Mathport.Syntax.Prelude

open Std (HashMap)
open Lean

namespace Mathport
namespace Translate

inductive NotationKind
  | fail
  | const : Syntax → NotationKind
  | unary : (Syntax → Syntax) → NotationKind
  | binary : (Syntax → Syntax → Syntax) → NotationKind
  | nary : (Array Syntax → Syntax) → NotationKind
  | exprs : (Array Syntax → Syntax) → NotationKind
  | binder : (Syntax → Syntax → Syntax) → NotationKind
  deriving Inhabited

inductive Literal
  | tk : String → Literal
  | arg : Nat → Literal
  deriving FromJson, ToJson

inductive NotationDesc
  | builtin
  | fail
  | const (tk : String)
  | «infix» (tk : String)
  | «prefix» (tk : String)
  | «postfix» (tk : String)
  | nary (lits : Array Literal)
  deriving FromJson, ToJson, Inhabited

structure NotationEntry where
  name : Name
  desc : NotationDesc
  kind : NotationKind
  skipDecl := false
  deriving Inhabited

-- -- fake version
-- def NotationDesc.toKind (n4 : Name) : NotationDesc → NotationKind :=
--   let fakeNode as := mkNode ``Parser.Term.app #[mkIdent n4, mkNullNode as]
--   fun
--   | NotationDesc.builtin => NotationKind.fail
--   | NotationDesc.fail => NotationKind.fail
--   | NotationDesc.const _ => NotationKind.const $ fakeNode #[]
--   | NotationDesc.infix _ => NotationKind.binary fun a b => fakeNode #[a, b]
--   | NotationDesc.prefix _ => NotationKind.unary fun a => fakeNode #[a]
--   | NotationDesc.postfix _ => NotationKind.unary fun a => fakeNode #[a]
--   | NotationDesc.nary _ => NotationKind.nary @fakeNode

def NotationDesc.toKind (n4 : Name) : NotationDesc → NotationKind
  | NotationDesc.builtin => NotationKind.fail
  | NotationDesc.fail => NotationKind.fail
  | NotationDesc.const tk => NotationKind.const $ mkNode n4 #[mkAtom tk]
  | NotationDesc.infix tk => NotationKind.binary fun a b => mkNode n4 #[a, mkAtom tk, b]
  | NotationDesc.prefix tk => NotationKind.unary fun a => mkNode n4 #[mkAtom tk, a]
  | NotationDesc.postfix tk => NotationKind.unary fun a => mkNode n4 #[a, mkAtom tk]
  | NotationDesc.nary lits => NotationKind.nary fun as => mkNode n4 $ lits.map fun
    | Literal.arg i => as.getD i Syntax.missing
    | Literal.tk tk => mkAtom tk

open NotationKind in set_option hygiene false in
def predefinedNotations : HashMap String NotationEntry := [
    ("exprProp", const do `(Prop)),
    ("expr $ ", binary fun f x => do `($f $ $x)),
    ("expr¬ ", unary fun e => do `(¬ $e)),
    ("expr ∧ ", binary fun f x => do `($f ∧ $x)),
    ("expr ∨ ", binary fun f x => do `($f ∨ $x)),
    ("expr /\\ ", binary fun f x => do `($f ∧ $x)),
    ("expr \\/ ", binary fun f x => do `($f ∨ $x)),
    ("expr <-> ", binary fun f x => do `($f ↔ $x)),
    ("expr ↔ ", binary fun f x => do `($f ↔ $x)),
    ("expr = ", binary fun f x => do `($f = $x)),
    ("expr == ", binary fun f x => do `(HEq $f $x)),
    ("expr ≠ ", binary fun f x => do `($f ≠ $x)),
    ("expr ▸ ", binary fun f x => do `($f ▸ $x)),
    ("expr ⊕ ", binary fun f x => do `(Sum $f $x)),
    ("expr × ", binary fun f x => do `($f × $x)),
    ("expr + ", binary fun f x => do `($f + $x)),
    ("expr - ", binary fun f x => do `($f - $x)),
    ("expr * ", binary fun f x => do `($f * $x)),
    ("expr / ", binary fun f x => do `($f / $x)),
    ("expr % ", binary fun f x => do `($f % $x)),
    ("expr- ", unary fun x => do `(-$x)),
    ("expr ^ ", binary fun f x => do `($f ^ $x)),
    ("expr ∘ ", binary fun f x => do `($f ∘ $x)),
    ("expr <= ", binary fun f x => do `($f ≤ $x)),
    ("expr ≤ ", binary fun f x => do `($f ≤ $x)),
    ("expr < ", binary fun f x => do `($f < $x)),
    ("expr >= ", binary fun f x => do `($f ≥ $x)),
    ("expr ≥ ", binary fun f x => do `($f ≥ $x)),
    ("expr > ", binary fun f x => do `($f > $x)),
    ("expr && ", binary fun f x => do `($f && $x)),
    ("expr || ", binary fun f x => do `($f || $x)),
    ("expr∅", const do `(∅)),
    ("expr ++ ", binary fun f x => do `($f ++ $x)),
    ("expr :: ", binary fun f x => do `($f :: $x)),
    ("expr[ , ]", exprs fun stxs => do `([$stxs,*])),
    ("exprexists , ", binder fun bis e => do `(∃ $bis, $e)),
    ("expr∃ , ", binder fun bis e => do `(∃ $bis, $e)),
    ("expr∃! , ", binder fun bis e => do `(∃! $bis, $e)),
    ("exprℕ", const do `(ℕ)),
    ("exprℤ", const do `(ℤ)),
    ("exprdec_trivial", const do `(by decide)),
    ("exprformat! ", unary id),
    ("exprsformat! ", unary id)
  ].foldl (fun m (a, k) => m.insert a ⟨Name.anonymous, NotationDesc.builtin, k, true⟩) ∅
