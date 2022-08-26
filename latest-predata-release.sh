#!/usr/bin/env bash
set -eo pipefail

if [ -z "$GITHUB_TOKEN" ]; then
  echo "GITHUB_TOKEN needs to be set"
  exit 1
fi

curl -s -H "Authorization: token $GITHUB_TOKEN" \
    'https://api.github.com/repos/leanprover-community/mathport/releases?per_page=100' \
  | jq -r '.[].tag_name' \
  | grep '^predata-nightly' \
  | head -n1
