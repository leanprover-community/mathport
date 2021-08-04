/-
Copyright (c) 2021 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Daniel Selsam
-/
import Lean
import Mathport.Util.Path
import Mathport.Util.System
import Mathport.Util.Import
import Mathport.Util.Parse
import Mathport.Util.RenameExt
import Mathport.Syntax.AST3
import Mathport.Syntax.Data4
import Mathport.Syntax.Parse
import Mathport.Syntax.Translate

namespace Mathport
namespace Syntax

namespace Make

open Lean
open Translate

def genLeanFor (pcfg : Path.Config) (path : Path) : IO Unit := do
  println! s!"\n[genLeanFor] START {path.mod3}\n"
  createDirectoriesIfNotExists (path.toLean4 pcfg "Syn.lean").toString

  -- binport imports the future
  let binportImports : List Import := [{ module := path.package ++ path.mod4 : Import }]

  let mut synportImports : Array Import := #[{ module := `Mathport.Syntax.Data4 }]
  for ipath in ← (← parseTLeanImports (path.toLean3 pcfg ".tlean")).mapM (resolveMod3 pcfg) do
    synportImports := synportImports.push { module := ipath.package ++ (ipath.mod4.appendAfter "Aux") : Import }

  let opts := ({} : Options)

  withImportModulesConst binportImports (opts := opts) (trustLevel := 0) $ λ binportEnv => do
    withImportModulesConst synportImports.toList (opts := opts) (trustLevel := 0) $ λ synportEnv => do
      let binportEnv := binportEnv.setMainModule path.mod4
      let binportEnv ← addInitialNameAlignments binportEnv

      -- TODO: expose IO interface elsewhere. More of synport will end up being in CoreM-extending monads.
      let fileName := path.toLean4 pcfg "Syn.lean"
      let cmdCtx := { fileName := fileName.toString, fileMap := dummyFileMap }

      let ast3 ← parseAST3 $ path.toLean3 pcfg ".ast.json"

      let (⟨fmt, _⟩, env) ← Elab.Command.CommandElabM.toIO' (ctx := cmdCtx) (env := synportEnv) do
        (← Mathport.AST3toData4 (getRenameMap binportEnv) ast3, ← getEnv)

      writeModule env $ path.toLean4 pcfg "Aux.olean"
      IO.FS.writeFile fileName (toString fmt)
      println! "\n[genLeanFor] END   {path.mod3}\n"

abbrev Job := Task (Except IO.Error Unit)

structure State where
  path2task : HashMap Path Job := {}

partial def visit (pcfg : Path.Config) (target : Path) : StateRefT State IO Job := do
  match (← get).path2task.find? target with
  | some task => pure task
  | none      => do
    -- if ← target.toLean4 pcfg "syn.lean" |>.pathExists then
    --   IO.asTask (pure ())
    -- else
      let mut jobs := #[]
      for mod3 in ← parseTLeanImports (target.toLean3 pcfg ".tlean") do
        let ipath ← resolveMod3 pcfg mod3
        jobs := jobs.push (← visit pcfg ipath)
      for job in jobs do
        match ← IO.wait job with
        | Except.ok _ => pure ()
        | Except.error err => throw err
      let job ← IO.asTask $ genLeanFor pcfg target
      modify λ s => { s with path2task := s.path2task.insert target job }
      pure job

end Make

def main (args : List String) : IO Unit := do
  match args with
  | [package, mod3, pathToConfig] =>
    let pcfg ← parseJsonFile Path.Config pathToConfig
    let target := Path.mk package mod3.toName
    let some LEAN_PATH ← IO.getEnv "LEAN_PATH" | throw (IO.userError "LEAN_PATH not set")
    println! "[searchPath] {LEAN_PATH}"
    Lean.initSearchPath LEAN_PATH
    let job ← (Make.visit pcfg target) |>.run' (s := {})
    let result ← IO.wait job
    match result with
    | Except.ok _ => pure ()
    | Except.error err => throw err

  | _ => throw $ IO.userError "usage: mathport binary <lean4mod> <lean3mrp> <path-to-config>"

end Syntax

-- open Lean Lean.Elab Lean.Elab.Term Lean.Elab.Tactic
-- open Lean.Parser Lean.PrettyPrinter

-- -- set_option trace.PrettyPrinter.parenthesize true in
-- -- set_option trace.PrettyPrinter.format true in
-- #eval show CoreM Unit from do
--   -- let s ← IO.FS.readFile "/home/mario/Documents/lean/lean/library/init/data/quot.ast.json"
--   let s ← IO.FS.readFile "/home/mario/Documents/lean/mathport/PreData/mathlib3/ring_theory/nullstellensatz.ast.json"
--   let json ← Json.parse s
--   let raw@⟨ast, file, level, expr⟩ ← fromJson? json (α := Parse.RawAST3)
--   let ⟨prel, imp, commands, inot, icmd⟩ ← raw.toAST3
--   let level := Parse.buildLevels level
--   let expr := Parse.buildExprs level expr
--   let commands := ast[ast[file].get!.children'[2]].get!.children'
--   let cmdCtx := { fileName := "<input>", fileMap := dummyFileMap }
--   let env ← getEnv
--   let mut opts : Options := {}
--   -- opts := opts.setBool `trace.PrettyPrinter.parenthesize true
--   let s := Elab.Command.mkState (← getEnv) {} opts
--   for c in commands[27:28] do
--     -- println! (repr (← Parse.getNode c |>.run ast expr)).group ++ "\n"
--     -- println! (repr (← Parse.getCommand c |>.run ast expr).kind).group ++ "\n"
--     let res ← Parse.getCommand c |>.run ast expr
--     Elab.Command.CommandElabM.toIO (ctx := cmdCtx) (s := s) do
--       let ⟨fmt, _⟩ ← Mathport.AST3toData4 {} ⟨none, #[], #[res], inot, icmd⟩
--       println! "{fmt}"
--       printTraces

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
