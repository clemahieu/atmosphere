#![deny(unused_must_use)]

macro_rules! source {
    ($($arg:tt)*) => {
        println!("cargo:rerun-if-changed={}", format_args!($($arg)*));
    };
}

fn main() {
    eprintln!("Baking garlic bread...");
    source!("build.rs");
    // Only the multiboot2 and PVH build has its entry in assembly: the UEFI build's is
    // src/boot/uefi.rs, and a host test build has its own _start.
    if std::env::var("CARGO_CFG_TARGET_OS").unwrap() != "none" {
        return;
    }
    add_x86_64_asm("multiboot2_header.asm");
    add_x86_64_asm("crt0.asm");
}

/// Adds code from a NASM assembly file to the image.
fn add_x86_64_asm(source: &str) {
    let arch_dir = "src/boot";
    source!("{}/{}", arch_dir, source);

    let mut mb = nasm_rs::Build::new();
    mb.file(&format!("{}/{}", arch_dir, source));
    mb.target("");
    mb.flag("-felf64");

    let objects = mb.compile_objects().unwrap();
    for object in objects {
        println!("cargo:rustc-link-arg={}", object.to_str().unwrap());
    }
}
