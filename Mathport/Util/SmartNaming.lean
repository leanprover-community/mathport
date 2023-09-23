import Mathport.Binary.Basic

open Lean

-- Ways to write `xs` as `ys ++ zs`, with `ys` nonempty.
def List.splits1 : List a → List (List a × List a)
| [] => []
| (x :: xs) => ([x], xs) :: (splits1 xs).map (fun (ys, zs) => (x :: ys, zs))

namespace Mathport.Binary

open Mathlib.Prelude.Rename

def reverseName (rm : RenameMap) (n4 : Name) : BinportM (List Name) := do
  match rm.toLean3.find? n4 with
  | none => return []
  | some (n3, n3s) => return n3 :: n3s

-- Collect all constant names that appear in ty
-- and find corresponding Lean 3 names.
-- Return a map (Lean 3 suffix ↦ Lean 4 suffix).
-- (The NameMap keys are just the suffix part, as are the values.)
def collectLean3Names (ty : Expr) : BinportM (NameMap String) := do
  let rm := Mathlib.Prelude.Rename.renameExtension.getState (← getEnv)
  let rec visit : Expr → NameMap String → BinportM (NameMap String)
  | .bvar _, nm | .fvar _, nm | .mvar _, nm | .sort _, nm | .lit _, nm => return nm
  | .app fn arg, nm => do visit fn (← visit arg nm)
  | .lam _ binderType body _, nm
  | .forallE _ binderType body _, nm => do visit binderType (← visit body nm)
  | .letE _ binderType value body _, nm => do visit binderType (← visit value (← visit body nm))
  | .mdata _ e, nm => visit e nm
  | .proj _ _ e, nm => visit e nm
  | .const declName _, nm => do
    match declName with
    | .str _ s4 =>
      let mut nm' := nm
      for n3 in (← reverseName rm declName) do
        if let .str _ s3 := n3 then
          nm' := nm'.insert s3 s4
      return nm'
    | _ => return nm
  visit ty (mkNameMap _)

/--
Decapitalize the string `s`, which is supposed to be the Lean 4 name
of something being referred to in the name of a theorem.
In some cases, we do something else--currently:
don't decapitalize the names of the intervals.
-/
def smartDecapitalize (s : String) : String :=
  match exceptions.lookup s with
  | some s' => s'
  | none => s.decapitalize
where
  exceptions : List (String × String) :=
    ["Ioo", "Ico", "Iio", "Icc", "Iic", "Ioc", "Ici", "Ioi", "Ixx"].map (fun s => (s, s))

-- Greedily try to translate parts of the name `s` (separated by underscores)
-- from Lean 3 to Lean 4, guided by the constants appearing within `ty`
-- (which is a Lean 4 expression) and their Lean 3 counterparts.
partial def smartNameAux (s : String) (ty : Expr) : BinportM String := do
  let nm ← collectLean3Names ty
  -- Translate a name that has already been split into "words".
  let rec go : List String → BinportM (List String) := fun l => do
    -- Look for longest initial string of "words"
    -- present as a key in nm.
    for (first, rest) in l.splits1.reverse do
      let n3 := "_".intercalate first
      if let some n4 := nm.find? n3
        then return smartDecapitalize n4 :: (← go rest)
    -- Didn't manage to use first component.
    match l with
    | [] => return []
    | x :: xs => return x :: (← go xs)
  let res ← go (s.splitOn "_")
  return "_".intercalate res

def smartName (s : String) (ty : Option Expr) : BinportM String :=
  match ty with
  | none => return s
  | some ty => smartNameAux s ty
