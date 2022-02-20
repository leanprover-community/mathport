# Mathport

Mathport is a tool for porting Lean3 projects to Lean4. It consists of two (loosely coupled) components:

- "binport", which translates Lean3 `.lean` files to Lean4 `.olean` files
- "synport", which best-effort translates Lean3 `.lean` files to Lean4 `.lean` files

## Running with artifacts from continuous integration

A full run of `mathport` (see below) on Lean 3 and mathlib3 takes several hours.
We provide artifacts on the github releases page,
and separate repositories
containing the `.lean` files and `.olean` files generated from Lean 3 and from mathlib3.

Please use the repositories
https://github.com/leanprover-community/lean3port
and
https://github.com/leanprover-community/mathlib3port
and run `lake build` to obtain the generated `.olean` and `.lean` files.

Using these repositories, you can open the synported `.lean` files in VS Code
to see the current state of output.

Alternatively, you can import some or all of the binported `.olean` files
using e.g.
```
import Mathbin.AlgebraicGeometry.Scheme

#lookup3 algebraic_geometry.Scheme
#check AlgebraicGeometry.Scheme
```
(Specifying the `mathlib3port` repository as a Lake dependency in your own
project should work to enable `import Mathbin.All`.)

The synported `.lean` files are checked in to these repositories:
feel free to commit new versions
if you have updated the dependencies in the relevant lakefile
and downloaded fresh `.lean` files.

## Running mathport locally

See the `Makefile` for usage (it takes several hours to rebuild the mathlib3 port from scratch).
Basic usage is `make build source predata port`.

We provide artifacts for various stages of the build on the releases page of the `mathport` repository.
The script `./download-release.sh nightly-YYYY-MM-DD` downloads one of these,
after which you can skip the `make predata` and/or `make port` steps
(you will still need to run `make build` and `make source`).

To port a single file, then execute `mathport` as follows
(depending on whether you want to port a core or a mathlib file):
```
./build/bin/mathport config.json Leanbin::init.data.nat.gcd
./build/bin/mathport config.json Mathbin::field_theory.abel_ruffini
```

The directory `Test` contains subdirectories `importLeanBin` and `importMathbin`,
each containing a `lakefile.lean` that depends on `lean3port` and `mathlib3port`, resp.

