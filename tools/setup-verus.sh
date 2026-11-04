#!/bin/bash
# Build the Verus fork Atmosphere verifies with, into tools/verus.
set -euo pipefail

tools="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
verus="$tools/verus"

rustup toolchain install 1.76.0

if [ ! -d "$verus" ]; then
    git clone --branch mars https://github.com/mars-research/verus.git "$verus"
fi

cd "$verus/source"
if [ ! -x z3 ]; then
    ./tools/get-z3.sh
fi
source ../tools/activate
vargo build --release
