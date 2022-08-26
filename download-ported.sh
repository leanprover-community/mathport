#!/usr/bin/env bash
# Script to download artifacts from a release.
# Usage: `./download-ported.sh nightly-2021-11-30`

RELEASE=$1    # e.g. nightly-2021-11-30

if [ -z "$RELEASE" ]; then
    echo "Usage: ./download-ported.sh nightly-YYYY-MM-DD"
    echo "See https://github.com/leanprover-community/mathport/releases for available releases"
    exit 1
fi

set -exo pipefail

mkdir -p Outputs/oleans/leanbin/
pushd Outputs/oleans/leanbin/
curl -L https://github.com/leanprover-community/mathport/releases/download/$RELEASE/lean3-binport.tar.gz | tar xz
popd

mkdir -p Outputs/src/leanbin/
pushd Outputs/src/leanbin/
curl -L https://github.com/leanprover-community/mathport/releases/download/$RELEASE/lean3-synport.tar.gz | tar xz
popd

mkdir -p Outputs/oleans/mathbin/
pushd Outputs/oleans/mathbin/
curl -L https://github.com/leanprover-community/mathport/releases/download/$RELEASE/mathlib3-binport.tar.gz | tar xz
popd

mkdir -p Outputs/src/mathbin/
pushd Outputs/src/mathbin/
curl -L https://github.com/leanprover-community/mathport/releases/download/$RELEASE/mathlib3-synport.tar.gz | tar xz
popd
