#![deny(unused_must_use)]
// SPDX-License-Identifier: MIT

fn main() {
    eprintln!("Baking garlic bread...");
    println!("cargo:rerun-if-changed=build.rs");
}
