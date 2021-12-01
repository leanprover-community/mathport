# Mathport

Mathport is a tool for porting Lean3 projects to Lean4. It consists of two (loosely coupled) components:

- "binport", which translates Lean3 `.lean` files to Lean4 `.olean` files
- "synport", which best-effort translates Lean3 `.lean` files to Lean4 `.lean` files

## Running mathport locally

See the `Makefile` for usage (it takes several hours to rebuild the mathlib port).

## Running with artifacts from continuous integration

To avoid having to run `mathport` locally, we provide downloadable files
containing the `.lean` files and `.olean` files generated from Lean 3 and from mathlib3.

Please use the repositories
https://github.com/leanprover-community/lean3port
and
https://github.com/leanprover-community/mathlib3port
and run `lake build` to obtain the generated `.olean` and `.lean` files.
The `.lean` files are checked in to the repository: feel free to commit new versions
if you have downloaded a fresh `nightly` artifact.

Currently these repositories are also available as submodules of this repository,
under `Lean4Packages/`.

If you would like to download these artifacts into the `mathport` repository,
for example so that you can run a locally modified version of `mathport`
on a single file without having to regenerate everything, run
`./download-release.sh nightly-YYYY-MM-DD`.


The directory `Test` contains subdirectories `importLeanBin` and `importMathbin`,
each containing a `lakefile.lean` that depends on one of the projects
from the `Lean4Packages` directory.