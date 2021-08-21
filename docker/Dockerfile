FROM ubuntu:focal-20210723

ARG DEBIAN_FRONTEND=noninteractive
ARG N_THREADS=32

# These need to be in sync with the rest of the file
ENV LEAN3_BIN=/app/lean3/bin
ENV LEAN3_LIB=/app/lean3/library
ENV LEAN3_PKG=/app/lean3/leanpkg
ENV MATHLIB3_SRC=/app/mathlib3/src

# This folder is currently hardcoded in mathport's config.json file
ARG LEAN3_EXPORT=/app/mathport/PreData

# Some of these are used in the mathport Makefile
ENV LEAN4_S1_DIR=/app/lean4/build/stage1/
ENV LEAN4_S1_BIN=$LEAN4_S1_DIR/bin
ENV LEAN4_S1_LIB=$LEAN4_S1_DIR/lib/lean
ENV MATHPORT_DIR=/app/mathport
ENV MATHPORT_BUILD=$MATHPORT_DIR/build

# This folder is currently hardcoded in mathport, since e.g. there are lean files already in it
ENV LIB4=$MATHPORT_DIR/Lib4

RUN apt-get update
RUN apt-get upgrade -y
RUN apt-get install -y g++ git cmake time wget libgmp-dev

RUN git config --global user.email "you@example.com"
RUN git config --global user.name "Your Name"

############ Setup ###############

## Lean3
WORKDIR /app

RUN git clone --branch mathport https://github.com/dselsam/lean3.git lean3
WORKDIR /app/lean3
RUN bash script/mk_all.sh
RUN mkdir build
WORKDIR /app/lean3/build/
RUN cmake /app/lean3/src
RUN LEAN_PATH=$LEAN3_LIB:$LEAN3_PKG make -j $N_THREADS

## Mathlib
WORKDIR /app

RUN git clone https://github.com/leanprover-community/mathlib.git mathlib3
WORKDIR /app/mathlib3
RUN bash scripts/mk_all.sh

## Lean4
WORKDIR /app
RUN git clone https://github.com/leanprover/lean4 lean4
WORKDIR /app/lean4
RUN git fetch https://github.com/dselsam/lean4 9228d3949bda8c1411e707b3e20650fa1fdb9b4d

# Cherry-pick WHNF-inductive commit
RUN git cherry-pick 9228d3949bda8c1411e707b3e20650fa1fdb9b4d

RUN mkdir -p build
WORKDIR /app/lean4/build
RUN cmake /app/lean4
RUN make -j $N_THREADS
# We always call lean3 with absolute path
ENV PATH=$LEAN4_S1_BIN:$PATH

## Mathport
WORKDIR /app
RUN git clone --branch docker https://github.com/dselsam/mathport mathport
WORKDIR /app/mathport
RUN leanpkg build bin LINK_OPTS=-rdynamic -j $N_THREADS

############ Building ###############

WORKDIR /app
RUN find /app/lean3/ -name "*.olean" -delete # ast only exported when oleans not present
RUN LEAN_PATH=$LEAN3_LIB               $LEAN3_BIN/lean --make --recursive --ast --tlean /app/lean3/library
RUN LEAN_PATH=$LEAN3_LIB:$LEAN3_PKG    $LEAN3_BIN/lean --make --recursive --ast --tlean /app/lean3/leanpkg
RUN LEAN_PATH=$LEAN3_LIB:$MATHLIB3_SRC $LEAN3_BIN/lean --make --recursive --ast         /app/mathlib3/src
RUN LEAN_PATH=$LEAN3_LIB:$MATHLIB3_SRC $LEAN3_BIN/lean --make --recursive       --tlean /app/mathlib3/src # (one at a time due to memory issues)

WORKDIR /app/mathport
RUN mkdir PreData
RUN cp -r $LEAN3_LIB    $LEAN3_EXPORT/Lean3
RUN cp -r $MATHLIB3_SRC $LEAN3_EXPORT/Mathlib
RUN find $LEAN3_EXPORT -name "*.lean" -delete
RUN find $LEAN3_EXPORT -name "*.olean" -delete

RUN LEAN_PATH=$LEAN4_S1_LIB:$LIB4                 time $MATHPORT_BUILD/bin/Mathport /app/mathport/config.json Lean3::all Mathlib::all > mathport.out 2> mathport.err
RUN LEAN_PATH=$LEAN4_S1_LIB:$LIB4:$MATHPORT_BUILD lean --o=$LIB4/Lean3.olean                      $LIB4/Lean3.lean
RUN LEAN_PATH=$LEAN4_S1_LIB:$LIB4:$MATHPORT_BUILD lean --o=$LIB4/Mathlib.olean                    $LIB4/Mathlib.lean
RUN cp -r $MATHPORT_BUILD/Mathport* $LIB4/
