import Std.Data.HashMap

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
  | exprs : (Array Syntax → Syntax) → NotationKind

structure NotationEntry where
  kind : NotationKind := NotationKind.fail
  skipDecl := true

open NotationKind in set_option hygiene false in
def predefinedNotations : HashMap String NotationEntry := [
    ("exprProp", {kind := const do `(Prop)}),
    ("expr $ ", {kind := binary fun f x => do `($f $ $x)}),
    ("expr¬ ", {kind := unary fun e => do `(¬ $e)}),
    ("expr~ ", {}),
    ("expr ∧ ", {kind := binary fun f x => do `($f ∧ $x)}),
    ("expr ∨ ", {kind := binary fun f x => do `($f ∨ $x)}),
    ("expr /\\ ", {kind := binary fun f x => do `($f ∧ $x)}),
    ("expr \\/ ", {kind := binary fun f x => do `($f ∨ $x)}),
    ("expr <-> ", {kind := binary fun f x => do `($f ↔ $x)}),
    ("expr ↔ ", {kind := binary fun f x => do `($f ↔ $x)}),
    ("expr = ", {kind := binary fun f x => do `($f = $x)}),
    ("expr == ", {kind := binary fun f x => do `(HEq $f $x)}),
    ("expr ≠ ", {kind := binary fun f x => do `($f ≠ $x)}),
    ("expr ≈ ", {}),
    ("expr ~ ", {}),
    ("expr ≡ ", {}),
    ("expr ⬝ ", {}),
    ("expr ▸ ", {kind := binary fun f x => do `($f ▸ $x)}),
    ("expr ▹ ", {}),
    ("expr ⊕ ", {kind := binary fun f x => do `(Sum $f $x)}),
    ("expr × ", {kind := binary fun f x => do `($f × $x)}),
    ("expr + ", {kind := binary fun f x => do `($f + $x)}),
    ("expr - ", {kind := binary fun f x => do `($f - $x)}),
    ("expr * ", {kind := binary fun f x => do `($f * $x)}),
    ("expr / ", {kind := binary fun f x => do `($f / $x)}),
    ("expr % ", {kind := binary fun f x => do `($f % $x)}),
    ("expr- ", {kind := unary fun x => do `(-$x)}),
    ("expr ^ ", {kind := binary fun f x => do `($f ^ $x)}),
    ("expr ∘ ", {kind := binary fun f x => do `($f ∘ $x)}),
    ("expr <= ", {kind := binary fun f x => do `($f ≤ $x)}),
    ("expr ≤ ", {kind := binary fun f x => do `($f ≤ $x)}),
    ("expr < ", {kind := binary fun f x => do `($f < $x)}),
    ("expr >= ", {kind := binary fun f x => do `($f ≥ $x)}),
    ("expr ≥ ", {kind := binary fun f x => do `($f ≥ $x)}),
    ("expr > ", {kind := binary fun f x => do `($f > $x)}),
    ("expr && ", {kind := binary fun f x => do `($f && $x)}),
    ("expr || ", {kind := binary fun f x => do `($f || $x)}),
    ("expr ∈ ", {}),
    ("expr ∉ ", {}),
    ("expr∅", {kind := const do `(∅)}),
    ("expr ∩ ", {}),
    ("expr ∪ ", {}),
    ("expr ⊆ ", {}),
    ("expr ⊇ ", {}),
    ("expr ⊂ ", {}),
    ("expr ⊃ ", {}),
    ("expr \\ ", {}),
    ("expr ∣ ", {}),
    ("expr ++ ", {kind := binary fun f x => do `($f ++ $x)}),
    ("expr :: ", {kind := binary fun f x => do `($f :: $x)}),
    ("expr ; ", {}),
    ("expr ⁻¹", {}),
    ("expr[ ,]", {kind := exprs fun stxs => do `([$stxs,*])}),
    ("expr ≟ ", {}),
    ("expr =?= ", {})
  ].foldl (fun m (a, b) => m.insert a b) ∅
