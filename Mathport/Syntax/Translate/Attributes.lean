/-
Copyright (c) 2021 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
import Lean.Data.NameMap

namespace Mathport
namespace Translate

def unsupportedBuiltinAttributes : Lean.NameSet := [
    `elab_as_eliminator, `pp_using_anonymous_constructor,
    `algebra, `derive, `derive_handler, `ematch, `ematch_lhs, `hole_command, `intro,
    `no_rsimp, `rsimp, `pp_nodot, `user_attribute, `user_command, `user_notation, `unify,
    `elab_with_expected_type
    -- other attributes that exist but have not been spotted in the wild
    --
    -- `_refl_lemma, `«_simp.sizeof», `_simp_cache, `breakpoint, `elab_strategy,
    -- `inverse, `no_inst_pattern, `reducibility, `vm_monitor, `wrapper_eq,
  ].foldl (·.insert) ∅

def predefinedSimpSets : Lean.NameSet :=
  [ /- from lean3 -/ `norm, `pre_smt,
    /- from mathlib -/ `equiv_rw_simp, `field_simps, `functor_norm, `ghost_simps, `integral_simps,
    `mfld_simps, `monad_norm, `nontriviality, `parity_simps, `push_cast, `split_if_reduction,
    `transport_simps, `typevec, `sugar, `sugar_nat
  ].foldl (·.insert) ∅

end Translate
end Mathport
