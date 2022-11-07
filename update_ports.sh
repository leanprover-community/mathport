#!/usr/bin/env bash

GITHUB_USER=leanprover-community-bot

set -ex

git config --global user.email "leanprover.community@gmail.com"
git config --global user.name "leanprover-community-bot"

git clone "https://$GITHUB_USER:$GITHUB_TOKEN@github.com/leanprover-community/lean3port"
pushd lean3port
./update.sh "$TAG"
git push
popd

git clone "https://$GITHUB_USER:$GITHUB_TOKEN@github.com/leanprover-community/mathlib3port"
pushd mathlib3port
./update.sh
git push
popd
