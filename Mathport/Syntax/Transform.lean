/-
Copyright (c) 2021 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Ebner
-/
import Mathport.Syntax.Transform.Basic
import Mathport.Syntax.Transform.Declaration
import Mathport.Syntax.Transform.Tactic
import Mathport.Syntax.Transform.Expr

namespace Mathport
namespace Transform

open Lean Elab Term

partial def transform : Syntax → M Syntax :=
  applyTransformers mathport_transformer_list%
