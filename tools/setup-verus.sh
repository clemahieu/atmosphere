#!/bin/bash
# SPDX-License-Identifier: MIT

# Build upstream Verus at the commit this tree verifies with, the vstd revision in the workspace
# Cargo.toml, into tools/verus. It pins the same Rust as rust-toolchain.toml.
set -euo pipefail

tools="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
commit="$(python3 -c 'import sys, tomllib; print(tomllib.load(open(sys.argv[1], "rb"))["workspace"]["dependencies"]["vstd"]["rev"])' "$tools/../Cargo.toml")"
verus="$tools/verus"

url=https://github.com/verus-lang/verus.git
if [ ! -d "$verus" ]; then
    git clone "$url" "$verus"
fi
git -C "$verus" remote set-url origin "$url"
git -C "$verus" cat-file -e "$commit^{commit}" 2>/dev/null || git -C "$verus" fetch origin
git -C "$verus" checkout --quiet "$commit"

cd "$verus/source"
z3_version="$(sed -n 's/^z3_version="\(.*\)"$/\1/p' tools/get-z3.sh)"
if [ ! -x z3 ] || ! ./z3 --version | grep -qF "$z3_version"; then
    ./tools/get-z3.sh
fi
source ../tools/activate
vargo build --release

# vstd and verus_builtin for each other target tools/verify.py checks, beside the host build. rustc
# needs both crates built for the target it checks under; the proc macros run on the host and are
# shared. vstd is the same source the host build verified, so it is compiled here, not re-verified.
release="$PWD/target-verus/release"
rust_lib="$(rustc --print sysroot)/lib"
for triple in aarch64-unknown-none; do
    rustup target add "$triple"
    out="$PWD/target-verus/$triple"
    mkdir -p "$out"
    for macros in libverus_builtin_macros.so libverus_state_machines_macros.so; do
        ln -sfn "../release/$macros" "$out/$macros"
    done
    RUSTC_BOOTSTRAP=1 rustc --edition 2018 --crate-name verus_builtin --crate-type lib --target "$triple" \
        -C opt-level=3 --cfg verus_keep_ghost --out-dir "$out" builtin/src/lib.rs
    LD_LIBRARY_PATH="$rust_lib" VERUS_ROOT="$out" VSTD_KIND=IsVstd RUST_MIN_STACK=$((10 * 1024 * 1024)) \
        "$release/rust_verify" --internal-test-mode --target "$triple" \
        --extern verus_builtin="$out/libverus_builtin.rlib" \
        --extern verus_builtin_macros="$out/libverus_builtin_macros.so" \
        --extern verus_state_machines_macros="$out/libverus_state_machines_macros.so" \
        --crate-type=lib --export "$out/vstd.vir" --out-dir "$out" --is-vstd --compile \
        --no-verify --no-lifetime --no-trait-conflicts -C opt-level=3 --cfg 'feature="alloc"' \
        vstd/vstd.rs
done
