# Mathport

Mathport is a (WIP) tool for translating `.lean` files from lean3 to lean4.
It attempts to port syntax directly, and falls back on ported binaries and proof-search as necessary.
The goal is to produce Lean4 files for all of Mathlib with sorry-free definitions and a manageable number of sorries in proofs.

# Overview

There are several stages.

- **Export**. We instrument Lean3 to export JSON that includes detailed syntactic information along with position-aware expression information.
- **Parse**. We parse this JSON dump into a datastructure `AST3` that represents Lean3's grammar.
- **Translate**. We translate this `AST3` into `AST4`, a similar datastructure representing Lean4's grammar.
- **Refine**. We proceed in `CommandElabM`, trying to elaborate the candidate commands and refining the syntax as necessary.
- **Format**. Finally, we format the refined syntax in a Lean4 `.lean` file.
