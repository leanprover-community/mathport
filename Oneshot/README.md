## One-shot translation of lean 3 files

This is a template which you can use to quickly play with the translation of snippets of lean 3 code. The procedure is:

1. Clone `https://github.com/leanprover-community/mathport/`
   ```
   git clone https://github.com/leanprover-community/mathport/
   ```
2. get in the folder: `cd mathport`
3. install dependencies `cmake`, `gmp`, `gmp-devel`, `jq` if needed (debian/ubuntu `sudo apt install cmake gmp gmp-devel jq`, mac `brew install cmake jq`, etc)
4. Run `make build`
5. Run `make lean3-source`
6. Get a mathport release with `./download-release.sh $my_choice`, where $mychoice = `nightly-2022-12-13-04` works, **or just** `./download_release` to get the latest one automatically.
7. Put Lean 3 code in `Oneshot/lean3-in/main.lean`.
8. Put extra `#align` in `Oneshot/lean4-in/Oneshot.lean`
9. Run `make oneshot`

After the first run, you only have to repeat steps 7-9, unless you want to update mathlib (step 6) or mathport itself (`git pull` and then steps 4-9).
