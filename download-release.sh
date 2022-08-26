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

./download-ported.sh "$RELEASE"

if [ -f Outputs/oleans/leanbin/predata-tag ]; then
  RELEASE="$(cat Outputs/oleans/leanbin/predata-tag)"
fi

./download-predata.sh "$RELEASE"
