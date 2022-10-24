## One-shot translation of lean 3 files

This is a template which you can use to quickly play with the translation of snippets of lean 3 code. There are two inputs:

* `Oneshot/lean3-in/main.lean`: Put your lean code here.
* `Oneshot/lean4-in/Oneshot.lean`: All alignments in `Mathlib` will be used, but you can add additional alignments here.

To compile everything, (from the root of the repository) first run `make lean3-predata` beforehand, then run `make oneshot` after changing the inputs. The output is placed in `Outputs/src/oneshot/Oneshot/Main.lean`.
