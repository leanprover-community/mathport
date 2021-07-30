/-
Copyright (c) 2021 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Daniel Selsam
-/
import Mathport.Syntax.Translate.Basic
import Mathport.Syntax.Translate.Attributes
import Mathport.Syntax.Translate.Notation
import Mathport.Syntax.Translate.Parser
import Mathport.Syntax.Translate.Tactic

namespace Mathport

open Lean hiding Expr Expr.app Expr.const Expr.sort Level Level.imax Level.max Level.param
open Lean.Elab (Visibility)

namespace Translate

open Std (HashMap)
open AST3

partial def M.run' (m : M α) :
  HashMap Name Name → Array Notation → Array Command → AuxData → EIO String α :=
  fun map nota cmds d => do
    let s ← ST.mkRef {notations := d}
    let rec ctx := ⟨map, nota, cmds, fun e => trExpr' e ctx s, fun c => trCommand' c ctx s⟩
    m ctx s

def M.run (m : M α) :
  HashMap Name Name → Array Notation → Array Command → StateT AuxData (EIO String) α := do
  M.run' $ do
    let mut tacs := {}
    for (n, tac) in Tactic.builtinTactics do
      tacs := tacs.insert n $ ← fun c s => pure fun a => tac.run a c s
    modify fun s => { s with tactics := tacs }
    (← m, (← get).notations)

end Translate

def AST3toData4 (renameMap : HashMap Name Name) (ast : AST3) : StateT Translate.AuxData (EIO String) Data4 :=
  (Translate.AST3toData4 ast).run renameMap ast.indexed_nota ast.indexed_cmds

-- open Lean Lean.Elab Lean.Elab.Term Lean.Elab.Tactic
-- open Lean.Parser Lean.PrettyPrinter

-- -- set_option trace.PrettyPrinter.parenthesize true in
-- -- set_option trace.PrettyPrinter.format true in
-- #eval show CoreM Unit from do
--   let s ← IO.FS.readFile "/home/mario/Documents/lean/lean/library/init/data/nat/lemmas.ast.json"
--   let json ← Json.parse s
--   let raw@⟨ast, file, level, expr⟩ ← fromJson? json (α := Parse.RawAST3)
--   let ⟨prel, imp, commands, inot, icmd⟩ ← raw.toAST3
--   let level := Parse.buildLevels level
--   let expr := Parse.buildExprs level expr
--   let commands := ast[ast[file].get!.children'[2]].get!.children'
--   for c in commands[129:] do
--     -- println! (repr (← Parse.getNode c |>.run ⟨ast, expr⟩)).group ++ "\n"
--     -- println! (repr (← Parse.getCommand c |>.run ast expr).kind).group ++ "\n"
--     let res ← Parse.getCommand c |>.run ast expr
--     try
--       let ⟨stx, _⟩ ← match ← (AST3toData4 ⟨none, #[], #[res], inot, icmd⟩).toIO' with
--       | Except.ok e => e
--       | Except.error e => throwError "{e}"
--       -- println! "{stx}\n\n"
--       let stx ← parenthesize Parser.Module.module.parenthesizer stx
--       -- println! "{stx}\n\n"
--       let fmt ← format Parser.Module.module.formatter stx
--       println! "{fmt}"
--     catch e =>
--       println! (repr (← Parse.getCommand c |>.run ast expr).kind).group ++ "\n"
--       println! "error: {← e.toMessageData.toString}"

-- #eval show CoreM Unit from do
--   let ⟨ast⟩ ← parseAST3 "/home/mario/Documents/lean/lean/library/init/logic.ast.json"
--   let ⟨stx, _⟩ ← match AST3toData4 ⟨ast[290:292].toArray⟩ with
--   | Except.ok e => e
--   | Except.error e => throwError "{e}"
--   -- let stx := stx[1][0]
--   println! "{stx[1]}\n\n"
--   let stx ← parenthesize Parser.Module.module.parenthesizer stx
--   println! "{stx}\n\n"
--   let fmt ← format Parser.Module.module.formatter stx
--   println! "{fmt}"
