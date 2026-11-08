#![deny(unused_must_use)]

fn main() {
    eprintln!("Baking garlic bread...");
    println!("cargo:rerun-if-changed=build.rs");
}
