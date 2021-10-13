# Mathport

Mathport is a tool for porting Lean3 projects to Lean4. It consists of two (loosely coupled) components:

- "binport", which translates Lean3 `.lean` files to Lean4 `.olean` files
- "synport", which best-effort translates Lean3 `.lean` files to Lean4 `.lean` files

See the `Makefile` for usage (it takes several hours to rebuild the mathlib port),
or the `test-mathport` repository if you'd prefer to use a pre-built artifact.
