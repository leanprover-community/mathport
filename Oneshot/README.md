## One-shot translation of lean 3 files

This is a template which you can use to quickly play with the translation of snippets of lean 3 code. The procedure is:

1. Clone `https://github.com/leanprover-community/mathport/`
```
git clone https://github.com/leanprover-community/mathport/
```
2. get in the folder: `cd mathport`
3. Run `make build` (if needed, run `sudo dnf install cmake gmp gmp-devel jq`)
4. Run `make lean3-predata`
5. Get a mathport release with `./download_release $my_choice`, where $mychoice = `nightly-2022-12-13-04` works, **or just** `./download_release` to get the latest one automatically.
6. Put Lean 3 code in `Oneshot/lean3-in/main.lean`.
7. Put extra `#align` in `Oneshot/lean4-in/Oneshot.lean`
8. Run `make oneshot`
