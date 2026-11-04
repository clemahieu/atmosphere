#!/bin/bash
# Build upstream Verus at the commit this tree verifies with, into tools/verus. It pins the same Rust
# as rust-toolchain.toml.
set -euo pipefail

commit=3e8600ac3a52238dcf581a91c761e160bb6da743

tools="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
verus="$tools/verus"

url=https://github.com/verus-lang/verus.git
if [ ! -d "$verus" ]; then
    git clone "$url" "$verus"
fi
git -C "$verus" remote set-url origin "$url"
git -C "$verus" cat-file -e "$commit^{commit}" 2>/dev/null || git -C "$verus" fetch origin
git -C "$verus" checkout --quiet "$commit"

cd "$verus/source"
if [ ! -x z3 ]; then
    ./tools/get-z3.sh
fi
source ../tools/activate
vargo build --release
