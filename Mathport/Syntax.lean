/-
Copyright (c) 2021 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Daniel Selsam
-/
import Mathport.Bridge.Config
import Mathport.Syntax.AST3
import Mathport.Syntax.Parse
import Mathport.Syntax.Translate

namespace Mathport

open Lean Lean.Elab.Command
open Syntax

def synport1 (config : Config) (path : Path) (imports : Array Name) : CommandElabM Unit := do
  let pcfg := config.pathConfig
  let (ast3, _) ← parseAST3 (path.toLean3 pcfg ".ast.json") false
  let imports := if ast3.prelude.isNone then imports.filter (!(`init).isPrefixOf ·) else imports
  -- HACK: replace the imports with the ones from .tlean until lean#811 lands
  let ast3 := { ast3 with «import» := imports.map (#[.dummy ·]) }
  let ⟨fmt, _⟩ ← AST3toData4 path ast3 config
  IO.FS.writeFile (path.toLean4src pcfg) (fmt.pretty 100)
