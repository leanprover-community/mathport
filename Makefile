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

all:

unport:
	rm -rf Lib4 Logs/*
	git checkout HEAD -- Lib4

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
lean3-source:
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

LEANBIN_LIB=./Lib4/leanbin/build/lib
MATHBIN_LIB=./Lib4/mathbin/build/lib

build:
	lake build

port-lean: init-logs build
	LEAN_PATH=$(MATHPORT_LIB):$(MATHLIB4_LIB):$(LEANBIN_LIB) ./build/bin/mathport config.json Leanbin::all >> Logs/mathport.out 2> Logs/mathport.err
	LEAN_PATH=$(MATHPORT_LIB):$(MATHLIB4_LIB):$(LEANBIN_LIB) lean --o=$(LEANBIN_LIB)/Leanbin.olean ./Lib4/leanbin/Leanbin.lean
	cp lean-toolchain Lib4/leanbin

port-mathbin: port-lean
	LEAN_PATH=$(MATHPORT_LIB):$(MATHLIB4_LIB):$(LEANBIN_LIB):$(MATHBIN_LIB) ./build/bin/mathport config.json Leanbin::all Mathbin::all >> Logs/mathport.out 2> Logs/mathport.err
	LEAN_PATH=$(MATHPORT_LIB):$(MATHLIB4_LIB):$(LEANBIN_LIB):$(MATHBIN_LIB) lean  --o=$(MATHBIN_LIB)/Mathbin.olean ./Lib4/mathbin/Mathbin.lean
	cp lean-toolchain Lib4/mathbin

test-leanbin:
	cd Test/ImportLean && rm -rf build && lake build

test-mathbin:
	cd Test/ImportMathbin && rm -rf build && lake build

tar-lib4:
	tar --exclude 'lean_packages' -czvf mathport-release.tar.gz Lib4 Logs PreData
