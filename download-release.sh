#!/usr/bin/env bash
# Script to download artifacts from a release.
# Usage: `./download-release.sh nightly-2021-11-30`

RELEASE=$1    # e.g. nightly-2021-11-30

if [ -z "$RELEASE" ]; then
    echo "Usage: ./download-release.sh nightly-YYYY-MM-DD"
    echo "See https://github.com/leanprover-community/mathport/releases for available releases"
    exit 1
fi

set -ex

curl -O -L https://github.com/leanprover-community/mathport/releases/download/$RELEASE/lean3-predata.tar.gz
tar zxvf lean3-predata.tar.gz; rm lean3-predata.tar.gz

curl -O -L https://github.com/leanprover-community/mathport/releases/download/$RELEASE/lean3-binport.tar.gz
mkdir -p Outputs/oleans/leanbin/
mv lean3-binport.tar.gz Outputs/oleans/leanbin/
(cd Outputs/oleans/leanbin/; tar zxvf lean3-binport.tar.gz; rm lean3-binport.tar.gz)

curl -O -L https://github.com/leanprover-community/mathport/releases/download/$RELEASE/lean3-synport.tar.gz
mkdir -p Outputs/src/leanbin/
mv lean3-synport.tar.gz Outputs/src/leanbin/
(cd Outputs/src/leanbin/; tar zxvf lean3-synport.tar.gz; rm lean3-synport.tar.gz)

curl -O -L https://github.com/leanprover-community/mathport/releases/download/$RELEASE/mathlib3-predata.tar.gz
tar zxvf mathlib3-predata.tar.gz; rm mathlib3-predata.tar.gz

curl -O -L https://github.com/leanprover-community/mathport/releases/download/$RELEASE/mathlib3-binport.tar.gz
mkdir -p Outputs/oleans/mathbin/
mv mathlib3-binport.tar.gz Outputs/oleans/mathbin/
(cd Outputs/oleans/mathbin/; tar zxvf mathlib3-binport.tar.gz; rm mathlib3-binport.tar.gz)

curl -O -L https://github.com/leanprover-community/mathport/releases/download/$RELEASE/mathlib3-synport.tar.gz
mkdir -p Outputs/src/mathbin/
mv mathlib3-synport.tar.gz Outputs/src/mathbin/
(cd Outputs/src/mathbin/; tar zxvf mathlib3-synport.tar.gz; rm mathlib3-synport.tar.gz)

