/-
Copyright (c) 2021 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
import Std.Data.HashMap
import Mathport.Util.Json
import Mathport.Util.Misc
import Mathlib.Mathport.Syntax
import Mathlib.Init.ExtendedBinder
import Mathlib.Init.Set

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
  | binder : (Syntax → Syntax → Syntax) →
      (extended : Option (Syntax → Syntax → Syntax → Syntax) := none) → NotationKind
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
  | exprs (left sep right : String)
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
  | NotationDesc.exprs left sep right =>
    let left := mkAtom left; let sep := mkAtom sep; let right := mkAtom right
    NotationKind.exprs fun as => mkNode n4 #[left, Syntax.mkSep as sep, right]
  | NotationDesc.nary lits => NotationKind.nary fun as => mkNode n4 $ lits.map fun
    | Literal.arg i => as.getD i Syntax.missing
    | Literal.tk tk => mkAtom tk

open NotationKind in set_option hygiene false in
def predefinedNotations : HashMap String NotationEntry := [
    ("exprProp", const <| Id.run `(Prop)),
    ("expr $ ", binary fun f x => Id.run `($f <| $x)),
    ("expr¬ ", unary fun e => Id.run `(¬ $e)),
    ("expr ∧ ", binary fun f x => Id.run `($f ∧ $x)),
    ("expr ∨ ", binary fun f x => Id.run `($f ∨ $x)),
    ("expr /\\ ", binary fun f x => Id.run `($f ∧ $x)),
    ("expr \\/ ", binary fun f x => Id.run `($f ∨ $x)),
    ("expr <-> ", binary fun f x => Id.run `($f ↔ $x)),
    ("expr ↔ ", binary fun f x => Id.run `($f ↔ $x)),
    ("expr = ", binary fun f x => Id.run `($f = $x)),
    ("expr == ", binary fun f x => Id.run `(HEq $f $x)),
    ("expr ≠ ", binary fun f x => Id.run `($f ≠ $x)),
    ("expr ▸ ", binary fun f x => Id.run `($f ▸ $x)),
    ("expr ⊕ ", binary fun f x => Id.run `(Sum $f $x)),
    ("expr × ", binary fun f x => Id.run `($f × $x)),
    ("expr + ", binary fun f x => Id.run `($f + $x)),
    ("expr - ", binary fun f x => Id.run `($f - $x)),
    ("expr * ", binary fun f x => Id.run `($f * $x)),
    ("expr / ", binary fun f x => Id.run `($f / $x)),
    ("expr % ", binary fun f x => Id.run `($f % $x)),
    ("expr- ", unary fun x => Id.run `(-$x)),
    ("expr ⁻¹", unary fun x => Id.run `($x⁻¹)),
    ("expr| |", unary fun x => Id.run `(abs $x)), -- TODO: https://github.com/leanprover-community/mathport/issues/73
    ("expr-[1+ ]", unary fun x => Id.run `(-[1+ $x ])),
    ("expr ^ ", binary fun f x => Id.run `($f ^ $x)),
    ("expr ∘ ", binary fun f x => Id.run `($f ∘ $x)),
    ("expr <= ", binary fun f x => Id.run `($f ≤ $x)),
    ("expr ≤ ", binary fun f x => Id.run `($f ≤ $x)),
    ("expr < ", binary fun f x => Id.run `($f < $x)),
    ("expr >= ", binary fun f x => Id.run `($f ≥ $x)),
    ("expr ≥ ", binary fun f x => Id.run `($f ≥ $x)),
    ("expr > ", binary fun f x => Id.run `($f > $x)),
    ("expr ∣ ", binary fun x y => Id.run `($x ∣ $y)),
    ("expr && ", binary fun f x => Id.run `($f && $x)),
    ("expr || ", binary fun f x => Id.run `($f || $x)),
    ("expr >>= ", binary fun f x => Id.run `($f >>= $x)),
    ("expr >> ", binary fun x y => Id.run `($x >> $y)),
    ("expr <* ", binary fun x y => Id.run `($x <* $y)),
    ("expr *> ", binary fun x y => Id.run `($x *> $y)),
    ("expr <*> ", binary fun x y => Id.run `($x <*> $y)),
    ("expr <$> ", binary fun x y => Id.run `($x <$> $y)),
    ("expr <|> ", binary fun x y => Id.run `($x <|> $y)),
    ("expr ; ", binary fun x y => Id.run `(andthen $x $y)),
    ("expr ∈ ", binary fun x y => Id.run `($x ∈ $y)),
    ("expr ∉ ", binary fun x y => Id.run `($x ∉ $y)),
    ("expr ⊆ ", binary fun x y => Id.run `($x ⊆ $y)),
    ("expr ∪ ", binary fun x y => Id.run `($x ∪ $y)),
    ("expr ∩ ", binary fun x y => Id.run `($x ∩ $y)),
    ("expr \\ ", binary fun x y => Id.run `($x \ $y)),
    ("expr ≈ ", binary fun x y => Id.run `($x ≈ $y)),
    ("expr𝒫 ", unary fun x => Id.run `(𝒫 $x)),
    ("expr⋃₀ ", unary fun x => Id.run `(⋃₀ $x)),
    ("expr∅", const <| Id.run `(∅)),
    ("expr ++ ", binary fun f x => Id.run `($f ++ $x)),
    ("expr :: ", binary fun f x => Id.run `($f :: $x)),
    ("expr[ , ]", exprs fun stxs => Id.run `([$stxs,*])),
    ("expr[ ,]", exprs fun stxs => Id.run `([$stxs,*])),
    ("exprexists , ", exist),
    ("expr∃ , ", exist),
    ("exprΣ , ", binder (fun bis e => Id.run `(Σ $bis, $e))),
    ("exprΣ' , ", binder (fun bis e => Id.run `(Σ' $bis, $e))),
    ("expr∃! , ", binder (fun bis e => Id.run `(∃! $bis, $e))),
    ("exprℕ", const <| Id.run `(ℕ)),
    ("exprℤ", const <| Id.run `(ℤ)),
    ("expr‹ ›", unary fun x => Id.run `(‹$x›)),
    ("expr↑ ", unary fun x => Id.run `(↑ $x)),
    ("expr <| ", binary fun x y => Id.run `(Option.lhoare $x $y)),
    ("expr |> ", binary fun x y => Id.run `(Option.rhoare $x $y)),
    ("expr ≟ ", binary fun x y => Id.run `(UnificationConstraint.mk $x $y)),
    ("expr =?= ", binary fun x y => Id.run `(UnificationConstraint.mk $x $y)),
    ("expr <.> ", binary fun x y => Id.run `(mkStrName $x $y)),
    ("exprcommand", const <| Id.run `(Tactic Unit)),
    ("expr =ₐ ", binary fun x y => Id.run `(expr.alpha_eqv $x $y)),
    ("exprdec_trivial", const <| Id.run `(by decide)),
    ("exprformat! ", unary id),
    ("exprsformat! ", unary id),
    ("exprpformat! ", unary id),
    ("exprfail! ", unary id),
    ("exprtrace! ", unary id)
  ].foldl (fun m (a, k) => m.insert a ⟨Name.anonymous, NotationDesc.builtin, k, true⟩) ∅
where
  exist := binder
    (fun bis e => Id.run `(∃ $bis, $e))
    (fun x pred e => Id.run `(∃ $x:ident $pred:binderPred, $e))

def predefinedBinderPreds : NameMap (Syntax → Syntax) := [
    ("expr <= ", fun x => Id.run `(binderPred| ≤ $x)),
    ("expr ≤ ", fun x => Id.run `(binderPred| ≤ $x)),
    ("expr < ", fun x => Id.run `(binderPred| < $x)),
    ("expr >= ", fun x => Id.run `(binderPred| ≥ $x)),
    ("expr ≥ ", fun x => Id.run `(binderPred| ≥ $x)),
    ("expr > ", fun x => Id.run `(binderPred| > $x)),
    ("expr ∈ ", fun x => Id.run `(binderPred| ∈ $x))
  ].foldl (fun m (a, k) => m.insert a k) ∅
