# Mathport

Mathport is a tool for porting Lean3 projects to Lean4. It consists of two (loosely coupled) components:

- "binport", which translates Lean3 `.lean` files to Lean4 `.olean` files
- "synport", which best-effort translates Lean3 `.lean` files to Lean4 `.lean` files

## Running mathport locally

See the `Makefile` for usage (it takes several hours to rebuild the mathlib port).

## Running with artifacts from continuous integration

To avoid having to run `mathport` locally, we provide downloadable files
containing the `.lean` files and `.olean` files generated from Lean 3 and from mathlib3.

The directory `Lean4Packages` contains subdirectories `lean3port` and `mathlib3port`,
which are in fact git submodules,
each containing a `lakefile.lean` that automatically obtains
the relevant generated `.olean` files from a tarball.

The directory `Test` contains subdirectories `importLeanBin` and `importMathbin`,
each containing a `lakefile.lean` that depends on one of the projects
from the `Lean4Packages` directory.