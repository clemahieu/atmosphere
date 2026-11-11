// SPDX-License-Identifier: MIT

// Compile the reference mdb.c and midl.c unchanged. gcc keeps a new crate off
// the license allowlist. --wrap sends the service fds into the shim.

use std::env;
use std::path::PathBuf;
use std::process::Command;

fn main() {
    let manifest = PathBuf::from(env::var("CARGO_MANIFEST_DIR").unwrap());
    let lmdb = manifest.join("../../reference/lmdb/libraries/liblmdb");
    let out = PathBuf::from(env::var("OUT_DIR").unwrap());
    let mdb_o = out.join("mdb.o");
    let midl_o = out.join("midl.o");
    let shim_o = out.join("shim.o");
    let archive = out.join("liblmdb_shim.a");

    compile(&lmdb.join("mdb.c"), &mdb_o, &lmdb);
    compile(&lmdb.join("midl.c"), &midl_o, &lmdb);
    compile(&manifest.join("src/shim.c"), &shim_o, &lmdb);

    let status = Command::new("ar")
        .arg("crs")
        .arg(&archive)
        .arg(&mdb_o)
        .arg(&midl_o)
        .arg(&shim_o)
        .status()
        .expect("ar");
    assert!(status.success(), "ar failed");

    println!("cargo:rustc-link-search=native={}", out.display());
    println!("cargo:rustc-link-lib=static=lmdb_shim");
    println!("cargo:rustc-link-lib=pthread");
    for name in [
        "open",
        "close",
        "pread",
        "pwrite",
        "pwritev",
        "read",
        "write",
        "fstat",
        "lseek",
        "mmap",
        "munmap",
        "ftruncate",
        "fdatasync",
        "fcntl",
        "fsync",
    ] {
        println!("cargo:rustc-link-arg=-Wl,--wrap={name}");
    }

    println!("cargo:rerun-if-changed=src/shim.c");
    println!("cargo:rerun-if-changed={}", lmdb.join("mdb.c").display());
    println!("cargo:rerun-if-changed={}", lmdb.join("midl.c").display());
    println!("cargo:rerun-if-changed={}", lmdb.join("lmdb.h").display());
}

fn compile(src: &std::path::Path, obj: &std::path::Path, lmdb: &std::path::Path) {
    let out = Command::new("gcc")
        .args([
            "-c",
            "-O2",
            "-fPIC",
            "-pthread",
            "-D_GNU_SOURCE",
            "-DMDB_USE_ROBUST=0",
            "-DMDB_USE_PWRITEV=1",
            "-DMDB_FDATASYNC_WORKS",
        ])
        .arg("-I")
        .arg(lmdb)
        .arg(src)
        .arg("-o")
        .arg(obj)
        .output()
        .expect("gcc");
    if !out.status.success() {
        panic!(
            "gcc {} failed\n{}",
            src.display(),
            String::from_utf8_lossy(&out.stderr)
        );
    }
}
