# Script to download artifacts from a release.
# Usage: `./download-release.sh nightly-2021-11-30`

RELEASE=$1    # e.g. nightly-2021-11-30

curl -O -L https://github.com/leanprover-community/mathport/releases/download/$RELEASE/lean3-predata.tar.gz
mkdir -p PreData/Leanbin/
mv lean3-predata.tar.gz PreData/Leanbin/
cd PreData/Leanbin/
tar zxvf lean3-predata.tar.gz
rm lean3-predata.tar.gz
cd ../../
curl -O -L https://github.com/leanprover-community/mathport/releases/download/$RELEASE/lean3-binport.tar.gz
mkdir -p Outputs/oleans/leanbin/
mv lean3-binport.tar.gz Outputs/oleans/leanbin/
cd Outputs/oleans/leanbin/
tar zxvf lean3-binport.tar.gz
rm lean3-binport.tar.gz
cd ../../
curl -O -L https://github.com/leanprover-community/mathport/releases/download/$RELEASE/lean3-synport.tar.gz
mkdir -p Outputs/src/leanbin/
mv lean3-synport.tar.gz Outputs/src/leanbin/
cd Outputs/src/leanbin/
tar zxvf lean3-synport.tar.gz
rm lean3-synport.tar.gz
cd ../../
curl -O -L https://github.com/leanprover-community/mathport/releases/download/$RELEASE/mathlib3-predata.tar.gz
mkdir -p PreData/Mathbin/
mv mathlib3-predata.tar.gz PreData/Mathbin/
cd PreData/Mathbin/
tar zxvf mathlib3-predata.tar.gz
rm mathlib3-predata.tar.gz
cd ../../
curl -O -L https://github.com/leanprover-community/mathport/releases/download/$RELEASE/mathlib3-binport.tar.gz
mkdir -p Outputs/oleans/mathbin/
mv mathlib3-binport.tar.gz Outputs/oleans/mathbin/
cd Outputs/oleans/mathbin/
tar zxvf mathlib3-binport.tar.gz
rm mathlib3-binport.tar.gz
cd ../../
curl -O -L https://github.com/leanprover-community/mathport/releases/download/$RELEASE/mathlib3-synport.tar.gz
mkdir -p Outputs/src/mathbin/
mv mathlib3-synport.tar.gz Outputs/src/mathbin/
cd Outputs/src/mathbin/
tar zxvf mathlib3-synport.tar.gz
rm mathlib3-synport.tar.gz
cd ../../

