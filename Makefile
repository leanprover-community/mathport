all:

unport:
	rm -rf Lib4 Logs/*
	git checkout HEAD -- Lib4

init-logs:
	mkdir -p Logs

MATHLIB4_LIB=./lean_packages/mathlib/build/lib
MATHPORT_LIB=./build/lib

LEANBIN_LIB=./Lib4/Leanbin/build/lib
MATHBIN_LIB=./Lib4/Mathbin/build/lib
LIQUIDBIN_LIB=./Lib4/Liquidbin/build/lib

port-lean: init-logs
	LEAN_PATH=$(MATHPORT_LIB):$(MATHLIB4_LIB):$(LEAN3_LIB) time ./build/bin/mathport config.json Leanbin::all >> Logs/mathport.out 2> Logs/mathport.err
	LEAN_PATH=$(MATHPORT_LIB):$(MATHLIB4_LIB):$(LEAN3_LIB) lean --o=./Lib4/Leanbin/build/lib/Leanbin.olean ./Lib4/Leanbin/Leanbin.lean

port-mathbin: port-lean
	LEAN_PATH=$(MATHPORT_LIB):$(MATHLIB4_LIB):$(LEAN3_LIB):$(MATHBIN_LIB) time ./build/bin/mathport config.json Leanbin::all Mathbin::all >> Logs/mathport.out 2> Logs/mathport.err
	LEAN_PATH=$(MATHPORT_LIB):$(MATHLIB4_LIB):$(LEAN3_LIB):$(MATHBIN_LIB) lean  --o=./Lib4/Mathbin/build/lib/Mathbin.olean ./Lib4/Mathbin/Mathbin.lean

port-liquid: port-mathbin
	LEAN_PATH=$(MATHPORT_LIB):$(MATHLIB4_LIB):$(LEAN3_LIB):$(MATHBIN_LIB):$(LIQUIDBIN_LIB) time ./build/bin/mathport config.json Leanbin::all Mathbin::all Liquid::all >> Logs/mathport.out 2> Logs/mathport.err
	LEAN_PATH=$(MATHPORT_LIB):$(MATHLIB4_LIB):$(LEAN3_LIB):$(MATHBIN_LIB):$(LIQUIDBIN_LIB) lean  --o=./Lib4/Mathbin/build/lib/Liquidbin.olean ./Lib4/Mathbin/Liquidbin.lean

tar-lib4:
	tar --exclude 'lean_packages' -czvf mathport-release.tar.gz Lib4 Logs PreData

lean3-predata:
	mkdir -p PreData
	rm -rf PreData/Leanbin
	find $(LEAN3_LIB) -name "*.olean" -delete # ast only exported when oleans not present
	LEAN_PATH=$(LEAN3_LIB)                 $(LEAN3_BIN)/lean --make --recursive --ast --tlean $(LEAN3_LIB)
	LEAN_PATH=$(LEAN3_LIB):$(LEAN3_PKG)    $(LEAN3_BIN)/lean --make --recursive --ast --tlean $(LEAN3_PKG)
	cp -r $(LEAN3_LIB) PreData/Leanbin
	find PreData/ -name "*.lean" -delete
	find PreData/ -name "*.olean" -delete

mathbin-predata: lean3-predata
	rm -rf PreData/Mathbin
	find $(MATHLIB3_SRC) -name "*.olean" -delete # ast only exported when oleans not present
	LEAN_PATH=$(LEAN3_LIB):$(MATHLIB3_SRC)  $(LEAN3_BIN)/lean --make --recursive --ast   $(MATHLIB3_SRC)
	LEAN_PATH=$(LEAN3_LIB):$(MATHLIB3_SRC)  $(LEAN3_BIN)/lean --make --recursive --tlean $(MATHLIB3_SRC)
	cp -r $(MATHLIB3_SRC) PreData/Mathbin
	find PreData/ -name "*.lean" -delete
	find PreData/ -name "*.olean" -delete

liquid-predata: mathbin-predata
	rm -rf PreData/Liquid
	find $(LIQUID3_SRC) -name "*.olean" -delete # ast only exported when oleans not present
	LEAN_PATH=$(LEAN3_LIB):$(MATHLIB3_SRC):$(LIQUID3_SRC) $(LEAN3_BIN)/lean --make --recursive --ast --tlean $(LIQUID3_SRC)
	cp -r $(LIQUID3_SRC) PreData/Liquidbin
	find PreData/ -name "*.lean" -delete
	find PreData/ -name "*.olean" -delete
