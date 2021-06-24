/-
Copyright (c) 2021 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Daniel Selsam
-/
import Lean.Expr
import Mathport.Util
import Mathport.AST3

namespace Mathport

open Lean (Json FromJson Position Name BinderInfo)
open Lean.FromJson (fromJson?)

namespace Parse

abbrev AstId := Nat
abbrev Tag   := Option AstId

structure RawNode3 where
  start    : Position
  «end»    : Option Position
  kind     : String
  value    : Name
  children : Option (Array AstId)
  deriving FromJson, Repr

def RawNode3.children' (n : RawNode3) : Array AstId := n.children.getD #[]
def RawNode3.end' (n : RawNode3) : Position := n.end.getD n.start

structure RawAST3 where
  ast      : Array (Option RawNode3)
  commands : Array AstId
  -- pexpr    : Array RawPExpr
  -- expr     : Array RawExpr
  deriving FromJson

open AST3

abbrev M := ReaderT (Array (Option RawNode3)) $ StateT (HashMap AstId Node) $ Except String

def RawNode3.map (n : RawNode3) (f : String → Name → Array AstId → M α) : M (Spanned α) := do
  pure ⟨n.start, n.end', ← f n.kind n.value n.children'⟩

def opt (f : AstId → M α) (i : AstId) : M (Option α) :=
  if i = 0 then pure none else some <$> f i

def getRaw (i : AstId) : M RawNode3 := do
  match (← read)[i] with
  | some a => a
  | none => throw "missing node"

def getRaw? : AstId → M (Option RawNode3) := opt getRaw

def withRaw' (mk : Node → α → M β) (f : α → NodeK) (g : Node → Option α)
  (m : String → Name → Array AstId → M α) (i : AstId) : M β := do
  match (← get).find? i with
  | some n => match g n with
    | some k => mk n k
    | none => throw "type error"
  | none =>
    let r ← getRaw i
    let a ← m r.kind r.value r.children'
    let n := { start := r.start, end_ := r.end', kind := f a }
    modify fun s => s.insert i n
    mk n a

def withRawK (f : α → NodeK) (g : NodeK → Option α) (m : String → Name → Array AstId → M α) (i : AstId) : M α := do
  withRaw' (fun _ => pure) f (fun n => g n.kind) m i

def withRaw (f : α → NodeK) (g : NodeK → Option α) (m : String → Name → Array AstId → M α) (i : AstId) : M (Spanned α) := do
  withRaw' (fun n a => n.map fun _ => a) f (fun n => g n.kind) m i

mutual

partial def getNode (i : AstId) : M Node := do
  withRaw' (fun n _ => n) id (fun n => some n.kind) (fun k v c => NodeK.other <$> mkOther k v c) i

partial def getNode? : AstId → M (Option Node) := opt getNode

partial def mkOther (k : String) (v : Name) (c : Array AstId) : M Other := Other.mk k v <$> c.mapM getNode?

end

def getName : AstId → M (Spanned Name) :=
  withRaw NodeK.name (fun | NodeK.name c => some c | _ => none) (fun _ v _ => v)

def getStr : AstId → M (Spanned String) :=
  withRaw NodeK.str (fun | NodeK.str c => some c | _ => none) (fun _ v _ => v.getString!)

def arr (f : AstId → M α) (i : AstId) : M (Array α) := do
  match ← getRaw? i with
  | some n => n.children'.mapM f
  | _ => pure #[]

open Level in
def getLevel : AstId → M (Spanned Level) :=
  withRaw NodeK.level (fun | NodeK.level c => some c | _ => none) aux
where
  aux : String → Name → Array AstId → M Level
  | k, v, args => other <$> mkOther k v args

def getLevels : AstId → M (Option (Array (Spanned Level))) := opt (arr getLevel)

open Expr in
def getExpr : AstId → M (Spanned Expr) :=
  withRaw NodeK.expr (fun | NodeK.expr c => some c | _ => none) aux
where
  aux : String → Name → Array AstId → M Expr
  | k, v, args => other <$> mkOther k v args

mutual

partial def getBinder : AstId → M (Spanned Binder) :=
  withRaw NodeK.binder (fun | NodeK.binder c => some c | _ => none) aux
where
  aux : String → Name → Array AstId → M Binder
  | "binder_0", _, args => binder BinderInfo.default args
  | "binder_1", _, args => binder BinderInfo.instImplicit args
  | "binder_2", _, args => binder BinderInfo.strictImplicit args
  | "binder_4", _, args => binder BinderInfo.implicit args
  | "binder_8", _, args => binder BinderInfo.auxDecl args
  | k, v, args => Binder.other <$> mkOther k v args

  binder (bi : BinderInfo) (args : Array AstId) : M Binder := do
    Binder.binder bi (← opt (arr getName) args[0]) (← getBinders args[1]) (← getExpr args[2])

partial def getBinders : AstId → M Binders := arr getBinder

end

def getAttr (i : AstId) : M (Spanned Attribute) := do
  (← getRaw i).map fun _ _ args => do
    pure ⟨args[0] ≠ 0, ← getName args[1], ← args[2:].toArray.mapM getNode?⟩

open DeclVal in
def getDeclVal : AstId → M (Spanned DeclVal) :=
  withRaw NodeK.declVal (fun | NodeK.declVal c => some c | _ => none) aux
where
  aux : String → Name → Array AstId → M DeclVal
  | "eqns", _, args => eqns <$> args.mapM getArm
  | k, v, args => expr <$> getExpr.aux k v args

  getArm (i : AstId) : M Arm := do
    let args := (← getRaw i).children'
    pure ⟨← arr getExpr args[0], ← getExpr args[1]⟩

open Modifier in
def getModifier : AstId → M (Spanned Modifier) :=
  withRaw NodeK.mod (fun | NodeK.mod c => some c | _ => none) aux
where
  aux : String → Name → Array AstId → M Modifier
  | "doc", v, _ => doc v.getString!
  | "@[", _, args => attr false true <$> arr getAttr args[0]
  | k, v, args => other <$> mkOther k v args

def getModifiers : AstId → M Modifiers := arr getModifier

-- def getVariable (vk : VariableKind) (args : Array AstId) : M Command := do
--   Command.«variable» vk (← getModifiers args[0]) false #[← getBinder args[1]]

-- def getVariables (vk : VariableKind) (args : Array AstId) : M Command := do
--   Command.«variable» vk (← getModifiers args[0]) true <$> args[1:].toArray.mapM getBinder

open Command in
def getCommand : AstId → M (Spanned Command) :=
  withRaw NodeK.cmd (fun | NodeK.cmd c => some c | _ => none) aux
where
  aux : String → Name → Array AstId → M Command
  | "prelude", _, _ => «prelude»
  | "import", _, args => «import» <$> args.mapM getName
  | "mdoc", v, _ => mdoc v.getString!
  | "namespace", _, args => «namespace» <$> getName args[0]
  | "section", _, args => «section» <$> opt getName args[0]
  | "end", _, args => «end» <$> opt getName args[0]
  | "universe", _, args => «universe» false false <$> args.mapM getName
  | "universes", _, args => «universe» false true <$> args.mapM getName
  | "universe_variable", _, args => «universe» true false <$> args.mapM getName
  | "universe_variables", _, args => «universe» true true <$> args.mapM getName
  | "variable", _, args => getVariable VariableKind.variable false args
  | "parameter", _, args => getVariable VariableKind.parameter false args
  | "variables", _, args => getVariable VariableKind.variable true args
  | "parameters", _, args => getVariable VariableKind.parameter true args
  | "definition", _, args => getDecl DeclKind.def args
  | k, v, args => other <$> mkOther k v args

  getVariable (vk pl) (args : Array AstId) : M Command := do
    Command.«variable» vk (← getModifiers args[0]) pl <$> args[1:].toArray.mapM getBinder

  getHeader (args : Subarray AstId) : M _ := do
    (← getLevels args[0], ← opt getName args[1], ← getBinders args[2], ← opt getExpr args[3])

  getDecl (dk) (args : Array AstId) : M Command := do
    let mods ← getModifiers args[0]
    if args[1] = 0 then
      let (us, n, bis, ty) ← getHeader args[2:6]
      let val ← opt getDeclVal args[6]
      Command.decl dk mods n us bis ty val
    else
      -- Command.mutual_decl dk mods <$> args[1:].toArray.mapM getBinder
      panic! "mutual"

def RawAST3.toAST3 : RawAST3 → Except String AST3
| ⟨ast, commands⟩ => commands.mapM getCommand |>.run ast |>.run' {} |>.map AST3.mk

end Parse

def parseAST3 (filename : System.FilePath) : IO AST3 := do
  println! "Reading {filename}..."
  let s ← IO.FS.readFile filename
  println! "Parsing Json..."
  let json ← Json.parse s
  println! "Decoding RawAST3..."
  let rawAST3 ← fromJson? json (α := Parse.RawAST3)
  println! "Converting RawAST3 to AST3..."
  rawAST3.toAST3

-- #eval show IO Unit from do
--   let s ← IO.FS.readFile "/home/mario/Documents/lean/lean/library/init/function.ast.json"
--   let json ← Json.parse s
--   let rawAST3 ← fromJson? json (α := Parse.RawAST3)
--   let ⟨ast⟩ ← rawAST3.toAST3
--   for c in ast[0:10] do
--     println! (repr c.kind).group ++ "\n"
