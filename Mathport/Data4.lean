/-
Copyright (c) 2021 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Daniel Selsam
-/
import Mathport.Util

namespace Mathport
open Lean

structure Data4 where
  commands : Array Syntax
  exprs    : HashMap Position Expr

end Mathport

syntax (name := hideCmd) "hide " ident+ : command
syntax (name := includeCmd) "include " ident+ : command
syntax (name := omitCmd) "omit " ident+ : command
syntax (name := parameterCmd) "parameter " bracketedBinder+ : command

open Lean.Elab.Command

@[commandElab hideCmd] def elabHideCmd : CommandElab := fun stx => pure ()
@[commandElab includeCmd] def elabIncludeCmd : CommandElab := fun stx => pure ()
@[commandElab omitCmd] def elabOmitCmd : CommandElab := fun stx => pure ()


/-
#check
#check_failure
#eval
#exit
#print
#reduce
#resolve_name
#synth
abbrev
attribute
axiom
builtin_initialize
class
constant
declare_syntax_cat
def
deriving
elab
elab_rules
end
example
export
gen_injective_theorems%
inductive
infix
infixl
infixr
init_quot
initialize
instance
macro
macro_rules
mutual
namespace
notation
open
postfix
prefix
section
set_option
structure
syntax
theorem
unif_hint
universe
variable
-/