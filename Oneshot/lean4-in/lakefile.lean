import Lake
open Lake DSL

package oneshot

@[default_target] lean_lib Oneshot

require Qq from ".." / ".." / "lake-packages" / "Qq"
require std from ".." / ".." / "lake-packages" / "std"
require mathlib from ".." / ".." / "lake-packages" / "mathlib"
