all: mathport

mathport-lib:
	cd Lib && leanpkg build lib $(MAKEFLAGS)

mathport-app: mathport-lib
	cd App && leanpkg build bin LINK_OPTS+=-rdynamic LINK_OPTS+=../Lib/build/lib/libMathport.a

mathport: mathport-lib mathport-app

clean:
	rm -rf Lib/build/ App/build/ Lib/.leanpkg-lock App/.leanpkg-lock

unport:
	mkdir -p tmpDir
	mv Lib4/*.lean tmpDir
	rm -rf Lib4
	mv tmpDir Lib4
	rm -rf Logs
	mkdir Logs

port: mathport
	LEAN_PATH=./Lib4:./Lib/build time ./App/build/bin/MathportApp config.json Lean3::all Mathlib::all >> Logs/mathport.out 2> Logs/mathport.err
	cp -r ./Lib/build/Mathport* ./Lib4
	LEAN_PATH=./Lib4 lean --o=./Lib4/Lean3.olean                      ./Lib4/Lean3.lean
	LEAN_PATH=./Lib4 lean --o=./Lib4/Mathlib.olean                    ./Lib4/Mathlib.lean
