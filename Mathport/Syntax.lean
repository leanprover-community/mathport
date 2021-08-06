/-
Copyright (c) 2021 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Daniel Selsam
-/
import Lean
import Mathport.Util.System
import Mathport.Util.Import
import Mathport.Util.Parse
import Mathport.Bridge.Path
import Mathport.Bridge.RenameExt
import Mathport.Bridge.Config
import Mathport.Syntax.AST3
import Mathport.Syntax.Data4
import Mathport.Syntax.Parse
import Mathport.Syntax.Translate

namespace Mathport

open Lean Lean.Elab.Command
open Syntax

def synport1 (config : Config) (path : Path) : CommandElabM Unit := do
  let pcfg := config.pathConfig
  let ast3 ← parseAST3 $ path.toLean3 pcfg ".ast.json"
  let ⟨fmt, _⟩ ← AST3toData4 ast3 pcfg
  IO.FS.writeFile (path.toLean4 pcfg "Syn.lean") (toString fmt)

end Mathport
