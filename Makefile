all:

unport:
	rm -rf Lib4 Logs/*
	git checkout HEAD -- Lib4

init-logs:
	mkdir -p Logs

MATHLIB4_LIB=./lean_packages/mathlib/build/lib
MATHPORT_LIB=./build/lib

LEANBIN_LIB=./Lib4/leanbin/build/lib
MATHBIN_LIB=./Lib4/mathbin/build/lib
# LIQUIDBIN_LIB=./Lib4/liquidbin/build/lib

port-lean: init-logs
	LEAN_PATH=$(MATHPORT_LIB):$(MATHLIB4_LIB):$(LEANBIN_LIB) time ./build/bin/mathport config.json Leanbin::all >> Logs/mathport.out 2> Logs/mathport.err
	LEAN_PATH=$(MATHPORT_LIB):$(MATHLIB4_LIB):$(LEANBIN_LIB) lean --o=$(LEANBIN_LIB)/Leanbin.olean ./Lib4/leanbin/Leanbin.lean
	cp lean-toolchain Lib4/leanbin

port-mathlib: port-lean
	LEAN_PATH=$(MATHPORT_LIB):$(MATHLIB4_LIB):$(LEANBIN_LIB):$(MATHBIN_LIB) time ./build/bin/mathport config.json Leanbin::all Mathbin::all >> Logs/mathport.out 2> Logs/mathport.err
	LEAN_PATH=$(MATHPORT_LIB):$(MATHLIB4_LIB):$(LEANBIN_LIB):$(MATHBIN_LIB) lean  --o=$(MATHBIN_LIB)/Mathbin.olean ./Lib4/mathbin/Mathbin.lean
	cp lean-toolchain Lib4/mathbin

# port-liquid: port-mathlib
# 	LEAN_PATH=$(MATHPORT_LIB):$(MATHLIB4_LIB):$(LEANBIN_LIB):$(MATHBIN_LIB):$(LIQUIDBIN_LIB) time ./build/bin/mathport config.json Leanbin::all Mathbin::all Liquidbin::all >> Logs/mathport.out 2> Logs/mathport.err
# 	LEAN_PATH=$(MATHPORT_LIB):$(MATHLIB4_LIB):$(LEANBIN_LIB):$(MATHBIN_LIB):$(LIQUIDBIN_LIB) lean  --o=$(LIQUIDBIN_LIB)/Liquidbin.olean ./Lib4/liquidbin/Liquidbin.lean
# 	cp lean-toolchain Lib4/liquidbin

tar-lib4:
	tar --exclude 'lean_packages' -czvf mathport-release.tar.gz Lib4 Logs PreData

lean3-source:
	mkdir -p sources
	if [ -d "sources/lean" ]; then \
		cd sources/lean && git pull; \
	else \
		cd sources && git clone https://github.com/leanprover-community/lean.git; \
	fi

lean3-predata: lean3-source
	mkdir -p PreData
	rm -rf PreData/Leanbin
	find sources/lean/library -name "*.olean" -delete # ast only exported when oleans not present
	# By changing into the directory, `elan` automatically dispatches to the correct binary.
	cd sources/lean && lean --make --recursive --ast --tlean library
	cp -r sources/lean/library PreData/Leanbin
	find PreData/ -name "*.lean" -delete
	find PreData/ -name "*.olean" -delete

mathbin-source:
	mkdir -p sources
	if [ -d "sources/mathlib" ]; then \
		cd sources/mathlib && git pull; \
	else \
		cd sources && git clone https://github.com/leanprover-community/mathlib.git; \
	fi
	cd sources/mathlib && leanpkg configure

mathbin-predata: mathbin-source
	rm -rf PreData/Mathbin
	find sources/mathlib -name "*.olean" -delete # ast only exported when oleans not present
	cd sources/mathlib && lean --make --recursive --ast   src
	cd sources/mathlib && lean --make --recursive --tlean src
	cp -r sources/mathlib PreData/Mathbin
	find PreData/ -name "*.lean" -delete
	find PreData/ -name "*.olean" -delete

# liquid-source:
# 	mkdir -p sources
# 	if [ -d "sources/lean-liquid" ]; then \
# 		cd sources/lean-liquid && git pull; \
# 	else \
# 		cd sources && git clone https://github.com/leanprover-community/lean-liquid.git; \
# 	fi
# 	cd sources/lean-liquid && leanpkg configure && ./scripts/get-cache.sh

# liquid-predata: liquid-source
# 	rm -rf PreData/Liquid
# 	find sources/lean-liquid -name "*.olean" -delete # ast only exported when oleans not present
# 	cd sources/lean-liquid && lean --make --recursive --ast --tlean src
# 	cp -r sources/lean-liquid PreData/Liquidbin
# 	find PreData/ -name "*.lean" -delete
# 	find PreData/ -name "*.olean" -delete

predata: lean3-predata mathbin-predata # liquid-predata