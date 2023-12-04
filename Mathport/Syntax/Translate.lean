/-
Copyright (c) 2021 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Daniel Selsam
-/
import Mathport.Syntax.Translate.Basic
import Mathport.Syntax.Translate.Attributes
import Mathport.Syntax.Translate.Notation
import Mathport.Syntax.Translate.Parser
import Mathport.Syntax.Translate.Expr
import Mathport.Syntax.Translate.Tactic
import Mathport.Syntax.Translate.Tactic.Builtin
import Mathport.Syntax.Transform

namespace Mathport

open Lean hiding Expr Expr.app Expr.const Expr.sort Level Level.imax Level.max Level.param Command
open Lean.Elab.Command (CommandElabM liftCoreM)

namespace Translate

open AST3

partial def M.run' (m : M α) (notations : Array Notation) (commands : Array Command)
    (config : Config) : CommandElabM α := do
  let s ← ST.mkRef {}
  let mut renameImport := {}
  for arr in (Mathlib.Prelude.Rename.renameImportExtension.getState (← getEnv)).extern do
    for (n4, entry) in arr do
      renameImport := renameImport.insert entry.mod3 n4
  let rec ctx := {
    config, notations, commands, renameImport
    transform := Transform.transform
    trExpr := fun e => trExpr' e ctx s
    trTactic := fun e => trTactic' e ctx s
    trCommand := fun c => trCommand' c ctx s }
  m ctx s

def M.run (m : M α) (comments : Array Comment) :
    (notations : Array Notation) → (commands : Array Command) →
    (config : Config) → CommandElabM α :=
  M.run' $ do
    let tactics ← Tactic.builtinTactics
    let niTactics ← Tactic.builtinNITactics
    let convs ← Tactic.builtinConvs
    let userNotas ← Tactic.builtinUserNotation
    let userAttrs ← Tactic.builtinUserAttrs
    let userCmds ← Tactic.builtinUserCmds
    modify fun s => { s with
      tactics, niTactics, convs, userNotas, userAttrs, userCmds,
      remainingComments :=
        comments.qsort (positionToStringPos ·.start < positionToStringPos ·.start) |>.toList }
    m

def AST3toData4 (path : Path) : AST3 → M Data4
  | ⟨prel, imp, commands, _, _, _⟩ => do
    let prel := Parser.optTk prel.isSome
    let imp ← imp.concatMapM fun ns => ns.mapM fun n => mkIdent <$> renameModule n.kind
    let header ← `(Parser.Module.header| $[prelude%$prel]? $[import $imp]*)
    let fmt ← liftCoreM $ PrettyPrinter.format Parser.Module.header.formatter header
    let commitInfo := (← read).config.commitInfo
    printFirstLineComments
    printOutput fmt
    let origin := commitInfo.map fun ci =>
      (ci.repo, ci.fileRevs.findD (path.mod3.toFilePath.toString ++ ".lean") ci.commit)
    modifyEnv fun env => Mathlib.Prelude.Rename.renameImportExtension.addEntry env
      (env.header.mainModule, { mod3 := path.mod3, origin })
    -- todo: use the pretty-printer?
    printOutput <| match origin with
    | some (repo, commit) => f!"#align_import {path.mod3} from {repr repo}@{repr commit}\n\n"
    | none => f!"#align_import {path.mod3}\n\n"
    commands.forM fun c => do
      try trCommand c
      catch e =>
        let e := s!"error in {(← getEnv).mainModule}: {← e.toMessageData.toString}"
        println! e
        -- println! (repr c.kind)
        printOutput f!"/- {e}\nLean 3 AST:\n{(repr c.kind).group}-/\n\n"
    printRemainingComments
    pure ⟨(← get).output, HashMap.empty⟩

end Translate

def AST3toData4 (path : Path) (ast : AST3) : (config : Config) → CommandElabM Data4 :=
  (Translate.AST3toData4 path ast).run ast.comments ast.indexed_nota ast.indexed_cmds

def tactic3toSyntax (containingFile : AST3) (tac3 : Spanned AST3.Tactic) :
    (config : Config) → CommandElabM Syntax.Tactic :=
  (Translate.trTactic tac3).run #[] containingFile.indexed_nota containingFile.indexed_cmds
