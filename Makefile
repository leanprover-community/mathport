all:

unport:
	rm -rf Lib4 Logs/*
	git checkout HEAD -- Lib4

init-logs:
	mkdir -p Logs

MATHLIB4_LIB=./lean_packages/Mathlib/build/lib
MATHPORT_LIB=./build/lib
LEAN3_LIB=./Lib4/Lean3/build/lib
MATHBIN_LIB=./Lib4/Mathbin/build/lib

port-lean: mathport init-logs
	LEAN_PATH=$(MATHPORT_LIB):$(MATHLIB4_LIB):$(LEAN3_LIB) time ./build/bin/Mathport config.json Lean3::all >> Logs/mathport.out 2> Logs/mathport.err
	LEAN_PATH=$(MATHPORT_LIB):$(MATHLIB4_LIB):$(LEAN3_LIB) lean --o=./Lib4/Lean3/build/lib/Lean3.olean       ./Lib4/Lean3/Lean3.lean

port-mathlib: mathport init-logs
	LEAN_PATH=$(MATHPORT_LIB):$(MATHLIB4_LIB):$(LEAN3_LIB):$(MATHBIN_LIB) time ./build/bin/Mathport config.json Lean3::all Mathbin::all >> Logs/mathport.out 2> Logs/mathport.err
	LEAN_PATH=$(MATHPORT_LIB):$(MATHLIB4_LIB):$(LEAN3_LIB):$(MATHBIN_LIB) lean  --o=./Lib4/Lean3/build/lib/Lean3.olean         ./Lib4/Lean3/Lean3.lean
	LEAN_PATH=$(MATHPORT_LIB):$(MATHLIB4_LIB):$(LEAN3_LIB):$(MATHBIN_LIB) lean  --o=./Lib4/Mathbin/build/lib/Mathbin.olean     ./Lib4/Mathbin/Mathbin.lean

tar-lib4:
	tar --exclude 'build' --exclude 'lean_packages' -czvf mathport-release.tar.gz Lib4 Logs

lean3-predata:
	mkdir -p PreData
	rm -rf PreData/Lean3
	find $(LEAN3_LIB) -name "*.olean" -delete # ast only exported when oleans not present
	LEAN_PATH=$(LEAN3_LIB)                 $(LEAN3_BIN)/lean --make --recursive --ast --tlean $(LEAN3_LIB)
	LEAN_PATH=$(LEAN3_LIB):$(LEAN3_PKG)    $(LEAN3_BIN)/lean --make --recursive --ast --tlean $(LEAN3_PKG)
	cp -r $(LEAN3_LIB) PreData/Lean3
	find PreData/ -name "*.lean" -delete
	find PreData/ -name "*.olean" -delete

mathlib-predata: lean3-predata
	rm -rf PreData/Mathlib
	find $(MATHLIB3_SRC) -name "*.olean" -delete # ast only exported when oleans not present
	LEAN_PATH=$(LEAN3_LIB):$(MATHLIB3_SRC)  $(LEAN3_BIN)/lean --make --recursive --ast   $(MATHLIB3_SRC)
	LEAN_PATH=$(LEAN3_LIB):$(MATHLIB3_SRC)  $(LEAN3_BIN)/lean --make --recursive --tlean $(MATHLIB3_SRC)
	cp -r $(MATHLIB3_SRC) PreData/Mathlib3
	find PreData/ -name "*.lean" -delete
	find PreData/ -name "*.olean" -delete
