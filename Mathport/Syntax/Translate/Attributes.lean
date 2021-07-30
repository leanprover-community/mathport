/-
Copyright (c) 2021 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
import Lean.Data.Name

namespace Mathport
namespace Translate

def builtinAttributes : Lean.NameSet := [
    `refl, `elab_as_eliminator, `subst, `symm, `trans, `pp_using_anonymous_constructor,
    `algebra, `derive, `derive_handler, `ematch, `ematch_lhs, `hole_command, `intro,
    `no_rsimp, `rsimp, `pp_nodot, `user_attribute, `user_command, `user_notation
    -- other attributes that exist but have not been spotted in the wild
    --
    -- `_refl_lemma, `«_simp.sizeof», `_simp_cache, `breakpoint, `elab_strategy,
    -- `elab_with_expected_type, `inverse, `no_inst_pattern,
    -- `reducibility, `vm_monitor, `wrapper_eq,
  ].foldl (·.insert) ∅

def predefinedSimpSets : Lean.NameSet :=
  [`norm, `pre_smt].foldl (·.insert) ∅

end Translate
end Mathport
