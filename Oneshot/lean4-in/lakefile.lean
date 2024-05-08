import Lake
open Lake DSL

package extra

@[default_target] lean_lib Extra

require Qq from ".." / ".." / ".lake" / "packages" / "Qq"
require batteries from ".." / ".." / ".lake" / "packages" / "batteries"
require aesop from ".." / ".." / ".lake" / "packages" / "aesop"
require proofwidgets from ".." / ".." / ".lake" / "packages" / "proofwidgets"
require importGraph from ".." / ".." / ".lake" / "packages" / "importGraph"
require Cli from ".." / ".." / ".lake" / "packages" / "Cli"
require mathlib from ".." / ".." / ".lake" / "packages" / "mathlib"
