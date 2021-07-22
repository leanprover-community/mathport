/-
Copyright (c) 2021 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
import Std.Data.HashMap
import Mathport.Syntax

open Std (HashMap)
open Lean

namespace Mathport
namespace Translate

local instance : MonadQuotation Id where
  getRef              := pure Syntax.missing
  withRef             := fun _ => id
  getCurrMacroScope   := pure 0
  getMainModule       := pure `_fakeMod
  withFreshMacroScope := id

inductive NotationKind
  | fail
  | const : Syntax → NotationKind
  | unary : (Syntax → Syntax) → NotationKind
  | binary : (Syntax → Syntax → Syntax) → NotationKind
  | nary : (Array Syntax → Syntax) → NotationKind
  | exprs : (Array Syntax → Syntax) → NotationKind
  | binder : (Syntax → Syntax → Syntax) → NotationKind

structure NotationEntry where
  kind : NotationKind
  skipDecl := false

open NotationKind in set_option hygiene false in
def predefinedNotations : HashMap String NotationEntry := [
    ("exprProp", const do `(Prop)),
    ("expr $ ", binary fun f x => do `($f $ $x)),
    ("expr¬ ", unary fun e => do `(¬ $e)),
    ("expr~ ", fail),
    ("expr ∧ ", binary fun f x => do `($f ∧ $x)),
    ("expr ∨ ", binary fun f x => do `($f ∨ $x)),
    ("expr /\\ ", binary fun f x => do `($f ∧ $x)),
    ("expr \\/ ", binary fun f x => do `($f ∨ $x)),
    ("expr <-> ", binary fun f x => do `($f ↔ $x)),
    ("expr ↔ ", binary fun f x => do `($f ↔ $x)),
    ("expr = ", binary fun f x => do `($f = $x)),
    ("expr == ", binary fun f x => do `(HEq $f $x)),
    ("expr ≠ ", binary fun f x => do `($f ≠ $x)),
    ("expr ≈ ", fail),
    ("expr ~ ", fail),
    ("expr ≡ ", fail),
    ("expr ⬝ ", fail),
    ("expr ▸ ", binary fun f x => do `($f ▸ $x)),
    ("expr ▹ ", fail),
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
    ("expr ∈ ", fail),
    ("expr ∉ ", fail),
    ("expr∅", const do `(∅)),
    ("expr ∩ ", fail),
    ("expr ∪ ", fail),
    ("expr ⊆ ", fail),
    ("expr ⊇ ", fail),
    ("expr ⊂ ", fail),
    ("expr ⊃ ", fail),
    ("expr \\ ", fail),
    ("expr ∣ ", fail),
    ("expr ++ ", binary fun f x => do `($f ++ $x)),
    ("expr :: ", binary fun f x => do `($f :: $x)),
    ("expr ; ", fail),
    ("expr ⁻¹", fail),
    ("expr[ ,]", exprs fun stxs => do `([$stxs,*])),
    ("expr ≟ ", fail),
    ("expr =?= ", fail),
    ("exprexists , ", binder fun bis e => do `(∃ $bis, $e)),
    ("expr∃ , ", binder fun bis e => do `(∃ $bis, $e)),
    ("expr∃! , ", binder fun bis e => do `(∃! $bis, $e)),
    ("exprℕ", const do `(ℕ)),
    ("exprℤ", const do `(ℤ))
  ].foldl (fun m (a, k) => m.insert a ⟨k, true⟩) ∅
