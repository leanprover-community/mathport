## One-shot translation of lean 3 files

This is a template which you can use to quickly play with the translation of snippets of lean 3 code. The procedure is:

1. Clone `https://github.com/leanprover-community/mathport/`
   ```
   git clone https://github.com/leanprover-community/mathport/
   ```
2. get in the folder: `cd mathport`
3. Run `make build` (if needed, run `sudo apt install cmake gmp gmp-devel jq`)
4. Get a mathport release with `./download-release.sh $my_choice`, where $mychoice = `nightly-2022-12-13-04` works, **or just** `./download_release` to get the latest one automatically.
5. Put Lean 3 code in `Oneshot/lean3-in/main.lean`.
6. Put extra `#align` in `Oneshot/lean4-in/Oneshot.lean`
7. Run `make oneshot`

After the first run, you only have to repeat steps 5-7, unless you want to update mathlib (step 4) or mathport itself (`git pull` and then steps 3-7).
