import Lake
open Lake DSL

package oneshot

@[default_target] lean_lib Oneshot

require Qq from ".." / ".." / "lean_packages" / "Qq"
require std from ".." / ".." / "lean_packages" / "std"
require mathlib from ".." / ".." / "lean_packages" / "mathlib"
