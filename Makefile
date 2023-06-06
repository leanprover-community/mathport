### Makefile for mathport

# This is not a "real" makefile, i.e. it does not support partial compilation.

## Targets:
# You will need to run each of the following steps in sequence.
#
# * `build`: compile mathport
# * `source`: clone local copies of lean3 and mathlib3, and some minor preparation
# * `predata`: create `.ast` and `.tlean` files from the sources
# * `port`: run mathport on lean3 and mathlib3
#
# See also `download-release.sh`, which can be used to download artifacts for
# the `predata` and `port` targets.

## Prerequisites:
# curl, git, cmake, elan

# We make the following assumptions about versions:
#
# * `lean-toolchain` points to the same version of `lean4` as
#    the branch/commit of `mathlib4` selected in `lakefile.lean`.
#
# It will automatically identify the version of `lean3` than `mathlib` currently uses.

SHELL := bash   # so we can use process redirection

.PHONY: all build \
	mathbin-source lean3-source source \
	clean-predata lean3-predata mathbin-predata predata \
	init-logs oneshot unport port-lean port-mathbin port \
	predata-tarballs mathport-tarballs tarballs rm-tarballs \

all:

build:
	lake build

# Select which commit of mathlib3 to use.
MATHBIN_COMMIT=origin/master

# Clone mathlib3 and create `all.lean`.
mathbin-source:
	mkdir -p sources
	if [ ! -d "sources/mathlib/.git" ]; then \
		cd sources && git clone --depth 1 https://github.com/leanprover-community/mathlib.git; \
	fi
	cd sources/mathlib && git clean -xfd && git fetch && git checkout "$(MATHBIN_COMMIT)" --
	cd sources/mathlib && echo -n 'mathlib commit: ' && git rev-parse HEAD
	cd sources/mathlib && leanpkg configure && ./scripts/mk_all.sh
	cd sources/mathlib/archive && git ls-files \
		| sed -n '/\.lean/ { s=\.lean$$== ; s=/=».«=g; s=^=import «= ; s=$$=»= ; p }' > all.lean
	cd sources/mathlib/counterexamples && git ls-files \
		| sed -n '/\.lean/ { s=\.lean$$== ; s=/=».«=g; s=^=import «= ; s=$$=»= ; p }' > all.lean
	echo path ./archive >> sources/mathlib/leanpkg.path
	echo path ./counterexamples >> sources/mathlib/leanpkg.path

# Clone Lean 3, and some preparatory work:
# * Obtain the commit from (community edition) Lean 3 which mathlib is using
# * Run `cmake` to generate `version.lean`
# * Create `all.lean`.
lean3-source: mathbin-source
	mkdir -p sources
	if [ ! -d "sources/lean/.git" ]; then \
		cd sources && git clone --depth 1 https://github.com/leanprover-community/lean.git; \
	fi
	cd sources/lean && git clean -xfd && git checkout "`cd ../mathlib && lean --version | sed -e "s/.*commit \([0-9a-f]*\).*/\1/"`" --
	cd sources/lean && elan override set `cat ../mathlib/leanpkg.toml | grep lean_version | cut -d '"' -f2`
	mkdir -p sources/lean/build/release
	# Run cmake, to create `version.lean` from `version.lean.in`.
	cd sources/lean/build/release && cmake ../../src
	# Create `all.lean`.
	./mk_all.sh sources/lean/library/

source: mathbin-source lean3-source

clean-predata:
	find sources/lean/library -name "*.olean" -delete # ast only exported when oleans not present
	find sources/mathlib -name "*.olean" -delete # ast only exported when oleans not present

# Build .ast and .tlean files for Lean 3
lean3-predata:
	cd sources/lean && lean $(LEAN3_OPTS) --make --recursive --ast --tlean library
	cd sources/lean/library && git rev-parse HEAD > upstream-rev

# Build .ast and .tlean files for Mathlib 3.
mathbin-predata:
	# By changing into the directory, `elan` automatically dispatches to the correct binary.
	cd sources/mathlib && lean $(LEAN3_OPTS) --make --recursive --ast --tlean src archive counterexamples
	cd sources/mathlib && git rev-parse HEAD > upstream-rev
predata: lean3-predata mathbin-predata

init-logs:
	mkdir -p Logs

config.lean.json: config.json sources/lean/library/upstream-rev sources/lean/library/file-revs.json
	jq '.commitInfo = {repo: $$repo, commit: $$commit, fileRevs: $$revs[0]}' \
			--arg repo leanprover-community/lean \
			--arg commit "$$(cat sources/lean/library/upstream-rev)" \
			--slurpfile revs sources/lean/library/file-revs.json \
		< config.json > config.lean.json

port-lean: init-logs build config.lean.json
	./build/bin/mathport --make config.lean.json Leanbin::all >> Logs/mathport.out 2> >(tee -a Logs/mathport.err >&2)

sources/lean/library/file-revs.json: sources/lean/library/upstream-rev
	REV=$$(cat $<); \
	cd sources/lean; \
	if [ ! -d ".git" ]; then \
		git init -q \
			&& git remote add origin https://github.com/leanprover-community/lean.git; \
	fi; \
	git fetch origin $$REV: --refmap= --no-tags; \
	cd library && \
		while IFS= read -r -d '' file; do \
			printf "%s %s\0" $$(git rev-list -1 $$REV -- "$$file") "$$file"; \
		done < <(git ls-tree -rz --name-only $$REV) \
			| jq -Rs 'reduce (split("\u0000")[] | capture("^(?<sha>[a-z0-9]*) (?<path>.*)$$")) as $$i ({}; .[$$i.path] = $$i.sha)' \
			> file-revs.json

sources/mathlib/file-revs.json: sources/mathlib/upstream-rev
	REV=$$(cat $<); \
	cd sources/mathlib; \
	if [ ! -d ".git" ]; then \
		git init -q \
			&& git remote add origin https://github.com/leanprover-community/mathlib.git; \
	fi; \
	git fetch origin $$REV: --refmap=; \
	while IFS= read -r -d '' file; do \
		printf "%s %s\0" $$(git rev-list -1 $$REV -- "$$file") "$$(echo "$$file" | cut -d'/' -f2-)"; \
	done < <(git ls-tree -rz --name-only $$REV src archive counterexamples) \
		| jq -Rs 'reduce (split("\u0000")[] | capture("^(?<sha>[a-z0-9]*) (?<path>.*)$$")) as $$i ({}; .[$$i.path] = $$i.sha)' \
		> file-revs.json

config.mathlib.json: config.json sources/mathlib/upstream-rev sources/mathlib/file-revs.json
	jq '.commitInfo = {repo: $$repo, commit: $$commit, fileRevs: $$revs[0]}' \
			--arg repo leanprover-community/mathlib \
			--arg commit "$$(cat sources/mathlib/upstream-rev)" \
			--slurpfile revs sources/mathlib/file-revs.json \
		< config.json > config.mathlib.json

port-mathbin: port-lean config.mathlib.json
	./build/bin/mathport --make config.mathlib.json Leanbin::all Mathbin::all Archive::all Counterexamples::all >> Logs/mathport.out 2> >(tee -a Logs/mathport.err >&2)

port: port-lean port-mathbin

predata-tarballs:
	find sources/lean/library/ -name "*.ast.json" -o -name "*.tlean" -o -name upstream-rev -o -name file-revs.json | tar -czvf lean3-predata.tar.gz -T -
	find sources/mathlib/ -name "*.ast.json" -o -name "*.tlean" -o -name upstream-rev -o -name file-revs.json | tar -czvf mathlib3-predata.tar.gz -T -

mathport-tarballs:
	mkdir -p Outputs/src/leanbin Outputs/src/mathbin Outputs/src/archive Outputs/src/counterexamples Outputs/oleans/leanbin Outputs/oleans/mathbin
	tar -czvf lean3-synport.tar.gz -C Outputs/src/leanbin .
	tar -czvf lean3-binport.tar.gz -C Outputs/oleans/leanbin .
	tar -czvf mathlib3-synport.tar.gz -C Outputs/src/mathbin .
	tar -czvf mathlib3-binport.tar.gz -C Outputs/oleans/mathbin .
	tar -czvf archive-synport.tar.gz -C Outputs/src/archive .
	tar -czvf counterexamples-synport.tar.gz -C Outputs/src/counterexamples .

tarballs: predata-tarballs mathport-tarballs

unport:
	rm -rf Outputs/* Logs/*

rm-tarballs:
	rm lean3-predata.tar.gz lean3-synport.tar.gz lean3-binport.tar.gz \
		mathlib3-predata.tar.gz mathlib3-synport.tar.gz mathlib3-binport.tar.gz \
		archive-synport.tar.gz counterexamples-synport.tar.gz

Oneshot/lean3-in/main.ast.json: Oneshot/lean3-in/*.lean
	cd Oneshot/lean3-in && elan override set `cat ../../sources/mathlib/leanpkg.toml | grep lean_version | cut -d '"' -f2`
	cd Oneshot/lean3-in && lean --make --recursive --ast --tlean . || true
	rm -rf Outputs/oleans/oneshot || true

Oneshot/lean4-in/build/lib/Extra.trace: Oneshot/lean4-in/*.lean
	cd Oneshot/lean4-in && lake build

config.oneshot.json: config.json
	jq '.extraModules += ["Extra"]' < config.json > config.oneshot.json

Outputs/src/oneshot/Oneshot/Main.lean: Oneshot/lean3-in/main.ast.json Oneshot/lean4-in/build/lib/Extra.trace config.oneshot.json
	mkdir -p Logs/
	./build/bin/mathport --make config.oneshot.json Oneshot::main >> Logs/oneshot.out 2> >(tee -a Logs/oneshot.err >&2)

oneshot: Outputs/src/oneshot/Oneshot/Main.lean
	# output is in Outputs/src/oneshot/Oneshot/Main.lean

clean-oneshot:
	find Oneshot/lean3-in -name "*.olean" -delete
	rm Oneshot/lean3-in/main.ast.json || true
	rm -rf Oneshot/lean4-in/build || true
	rm config.oneshot.json || true
	rm -rf Outputs/oleans/oneshot || true
	rm -rf Outputs/src/oneshot || true
	true > Logs/oneshot.out
	true > Logs/oneshot.err
