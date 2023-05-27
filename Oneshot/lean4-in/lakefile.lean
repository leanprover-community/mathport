import Lake
open Lake DSL

package extra

@[default_target] lean_lib Extra

require Qq from ".." / ".." / "lake-packages" / "Qq"
require std from ".." / ".." / "lake-packages" / "std"
require aesop from ".." / ".." / "lake-packages" / "aesop"
require mathlib from ".." / ".." / "lake-packages" / "mathlib"
