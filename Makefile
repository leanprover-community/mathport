### Makefile for mathport

# This is not a "real" makefile, i.e. it does not detect dependencies between targets.

## Targets:
# `mathbin-source`: clone mathlib3, and create `all.lean`
# `lean3-source`: clone lean3, and create `all.lean` (run after `mathbin-source`, to get the right commit)
# `lean3-predata`: create `.ast` and `.tlean` files from Lean3
# `mathbin-predata`: create `.ast` and `.tlean` files from mathlib3
# `build`: compile mathport
# `port-lean`: run mathport on Lean3
# `port-mathbin`: run mathport on mathlib3

## Prerequisites:
# curl, git, cmake, elan, python3

# We make the following assumptions about versions:
#
# * `lean-toolchain` points to the same version of `lean4` as
#    the branch/commit of `mathlib4` selected in `lakefile.lean`.
#
# It will automatically identify the version of `lean3` than `mathlib` currently uses.

SHELL := /bin/bash   # so we can use process redirection

all:

unport:
	rm -rf Outputs/* Logs/*

# Select which commit of mathlib3 to use.
MATHBIN_COMMIT=master

# Obtain the requested commit from `mathlib`, and create `all.lean`
mathbin-source:
	mkdir -p sources
	if [ ! -d "sources/mathlib" ]; then \
		cd sources && git clone https://github.com/leanprover-community/mathlib.git; \
	fi
	cd sources/mathlib && git clean -xfd && git checkout $(MATHBIN_COMMIT)
	cd sources/mathlib && leanpkg configure && ./scripts/mk_all.sh

# Obtain the commit from (community edition) Lean 3 which mathlib is using, and create `all.lean`.
lean3-source: mathbin-source
	mkdir -p sources
	if [ ! -d "sources/lean" ]; then \
		cd sources && git clone https://github.com/leanprover-community/lean.git; \
	fi
	cd sources/lean && git clean -xfd && git checkout `cd ../mathlib && lean --version | sed -e "s/.*commit \([0-9a-f]*\).*/\1/"`
	mkdir -p sources/lean/build/release
	# Run cmake, to create `version.lean` from `version.lean.in`.
	cd sources/lean/build/release && cmake ../../src
	# Create `all.lean`.
	./mk_all.sh sources/lean/library/

# Build .ast and .tlean files for Lean 3
lean3-predata: lean3-source
	mkdir -p PreData
	rm -rf PreData/Leanbin
	find sources/lean/library -name "*.olean" -delete # ast only exported when oleans not present
	cd sources/lean && elan override set `cat ../mathlib/leanpkg.toml | grep lean_version | cut -d '"' -f2`
	cd sources/lean && lean --make --recursive --ast --tlean library
	cp -r sources/lean/library PreData/Leanbin
	find PreData/ -name "*.lean" -delete
	find PreData/ -name "*.olean" -delete

# Build .ast and .tlean files for Mathlib 3.
mathbin-predata: mathbin-source
	rm -rf PreData/Mathbin
	find sources/mathlib -name "*.olean" -delete # ast only exported when oleans not present
	# By changing into the directory, `elan` automatically dispatches to the correct binary.
	cd sources/mathlib && lean --make --recursive --ast --tlean src
	cp -r sources/mathlib PreData/Mathbin
	find PreData/ -name "*.lean" -delete
	find PreData/ -name "*.olean" -delete

predata: lean3-predata mathbin-predata

init-logs:
	mkdir -p Logs

MATHLIB4_LIB=./lean_packages/mathlib/build/lib
MATHPORT_LIB=./build/lib

LEANBIN_LIB=./Outputs/leanbin/oleans
MATHBIN_LIB=./Outputs/mathbin/oleans

build:
	lake build

port-lean: init-logs build
	LEAN_PATH=$(MATHPORT_LIB):$(MATHLIB4_LIB):$(LEANBIN_LIB) ./build/bin/mathport config.json Leanbin::all >> Logs/mathport.out 2> >(tee -a Logs/mathport.err >&2)
	cp lean-toolchain Lean4Packages/leanbin/

port-mathbin: port-lean
	LEAN_PATH=$(MATHPORT_LIB):$(MATHLIB4_LIB):$(LEANBIN_LIB):$(MATHBIN_LIB) ./build/bin/mathport config.json Leanbin::all Mathbin::all >> Logs/mathport.out 2> >(tee -a Logs/mathport.err >&2)
	cp lean-toolchain Lean4Packages/mathbin/

test-import-leanbin:
	cd Test/importLeanbin && rm -rf build lean_packages && lake build

test-import-mathbin:
	cd Test/importMathbin && rm -rf build lean_packages && lake build

tarballs:
	# Create the Outputs/* directories, if they don't already exist, in case we're doing a dry run for CI.
	mkdir -p Outputs/leanbin/src/
	mkdir -p Outputs/leanbin/oleans/
	mkdir -p Outputs/mathbin/src/
	mkdir -p Outputs/mathbin/oleans/
	tar -czvf lean3-synport.tar.gz -C Outputs/leanbin/src .
	tar -czvf lean3-binport.tar.gz -C Outputs/leanbin/oleans .
	tar -czvf mathlib3-synport.tar.gz -C Outputs/mathbin/src .
	tar -czvf mathlib3-binport.tar.gz -C Outputs/mathbin/oleans .
