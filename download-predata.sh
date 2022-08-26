#!/usr/bin/env bash
# Script to download artifacts from a release.
# Usage: `./download-predata.sh nightly-predata-2021-11-30`

RELEASE=$1    # e.g. nightly-predata-2021-11-30

if [ -z "$RELEASE" ]; then
    echo "Usage: ./download-predata.sh nightly-predata-YYYY-MM-DD"
    echo "See https://github.com/leanprover-community/mathport/releases for available releases"
    exit 1
fi

set -exo pipefail

curl -L https://github.com/leanprover-community/mathport/releases/download/$RELEASE/lean3-predata.tar.gz | tar xz
curl -L https://github.com/leanprover-community/mathport/releases/download/$RELEASE/mathlib3-predata.tar.gz | tar xz
