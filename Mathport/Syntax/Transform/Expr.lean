/-
Copyright (c) 2021 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Ebner
-/
import Mathport.Syntax.Transform.Basic

mathport_rules
  | `($x:term $args* <| fun $y:basicFun) => `($x:term $args* fun $y:basicFun)
  | `($x:term $args* <| fun $y:matchAlts) => `($x:term $args* fun $y:matchAlts)
  | `($x:term $args* <| do $s:doSeq) => `($x:term $args* do $s:doSeq)
  | `($x:term <| fun $y:basicFun) => `($x:term fun $y:basicFun)
  | `($x:term <| fun $y:matchAlts) => `($x:term fun $y:matchAlts)
  | `($x:term <| do $s:doSeq) => `($x:term do $s:doSeq)
