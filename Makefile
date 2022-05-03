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
#
# If you have already done a complete run,
# or `make build source` followed by running `download-release.sh`
# you can also use the `make TARGET=Data.Nat.Bitwise port-mathbin-single` target
# (similarly for `port-lean-single`) to run mathport on a single file.
# This is useful if you are testing a change to mathport.

## Prerequisites:
# curl, git, cmake, elan

# We make the following assumptions about versions:
#
# * `lean-toolchain` points to the same version of `lean4` as
#    the branch/commit of `mathlib4` selected in `lakefile.lean`.
#
# It will automatically identify the version of `lean3` than `mathlib` currently uses.

SHELL := bash   # so we can use process redirection

all:

build:
	lake build

# Select which commit of mathlib3 to use.
MATHBIN_COMMIT=master

# Clone mathlib3 and create `all.lean`.
mathbin-source:
	mkdir -p sources
	if [ ! -d "sources/mathlib" ]; then \
		cd sources && git clone https://github.com/leanprover-community/mathlib.git; \
	fi
	cd sources/mathlib && git clean -xfd && git checkout $(MATHBIN_COMMIT)
	cd sources/mathlib && leanpkg configure && ./scripts/mk_all.sh

# Clone Lean 3, and some preparatory work:
# * Obtain the commit from (community edition) Lean 3 which mathlib is using
# * Run `cmake` to generate `version.lean`
# * Create `all.lean`.
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

source: mathbin-source lean3-source

# Build .ast and .tlean files for Lean 3
lean3-predata: lean3-source
	find sources/lean/library -name "*.olean" -delete # ast only exported when oleans not present
	cd sources/lean && elan override set `cat ../mathlib/leanpkg.toml | grep lean_version | cut -d '"' -f2`
	cd sources/lean && lean --make --recursive --ast --tlean library

# Build .ast and .tlean files for Mathlib 3.
mathbin-predata: mathbin-source
	find sources/mathlib -name "*.olean" -delete # ast only exported when oleans not present
	# By changing into the directory, `elan` automatically dispatches to the correct binary.
	cd sources/mathlib && lean --make --recursive --ast --tlean src

predata: lean3-predata mathbin-predata

init-logs:
	mkdir -p Logs

MATHLIB4_LIB=./lean_packages/mathlib/build/lib
MATHPORT_LIB=./build/lib

LEANBIN_LIB=./Outputs/oleans/leanbin
MATHBIN_LIB=./Outputs/oleans/mathbin

port-lean: init-logs build
	./build/bin/mathport --make config.json Leanbin::all >> Logs/mathport.out 2> >(tee -a Logs/mathport.err >&2)

port-mathbin: port-lean
	./build/bin/mathport --make config.json Leanbin::all Mathbin::all >> Logs/mathport.out 2> >(tee -a Logs/mathport.err >&2)

port: port-lean port-mathbin

# You can use the next two targets to recompile a single file
# (e.g. if you are testing a modification of mathport)
# You'll need to have either run all the steps: `make build source predata port`,
# or run `make build source` and `./download-release.sh nightly-YYYY-MM-DD`.

port-lean-single:
	./build/bin/mathport config.json Leanbin::$(TARGET)

port-mathbin-single:
	./build/bin/mathport config.json Mathbin::$(TARGET)

test-import-leanbin:
	cd Test/importLeanbin && rm -rf build lean_packages && lake build

test-import-mathbin:
	cd Test/importMathbin && rm -rf build lean_packages && lake build

tarballs:
	mkdir -p Outputs/src/leanbin Outputs/src/mathbin Outputs/oleans/leanbin Outputs/oleans/mathbin
	find sources/lean/library/ -name "*.ast.json" -o -name "*.tlean" | tar -czvf lean3-predata.tar.gz -T -
	tar -czvf lean3-synport.tar.gz -C Outputs/src/leanbin .
	tar -czvf lean3-binport.tar.gz -C Outputs/oleans/leanbin .
	find sources/mathlib/ -name "*.ast.json" -o -name "*.tlean" | tar -czvf mathlib3-predata.tar.gz -T -
	tar -czvf mathlib3-synport.tar.gz -C Outputs/src/mathbin .
	tar -czvf mathlib3-binport.tar.gz -C Outputs/oleans/mathbin .

unport:
	rm -rf Outputs/* Logs/*

rm-tarballs:
	rm lean3-predata.tar.gz lean3-synport.tar.gz lean3-binport.tar.gz mathlib3-predata.tar.gz mathlib3-synport.tar.gz mathlib3-binport.tar.gz
