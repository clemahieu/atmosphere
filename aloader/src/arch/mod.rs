//! What the target fixes for the loader: its instructions, its serial device and its page-table
//! entry.
//!
//! One implementation per target, chosen by `cfg(target_arch)`, each with the same names and the
//! same signatures; the rest of the loader calls `arch::item` and names no instruction or device of
//! its own. design/arch-module/.

#[cfg(target_arch = "x86_64")]
mod x86_64;
#[cfg(target_arch = "x86_64")]
pub use x86_64::*;

// Built for the host's tests as well: what it holds is arithmetic.
#[cfg(any(target_arch = "aarch64", test))]
pub mod aarch64;
#[cfg(target_arch = "aarch64")]
pub use aarch64::*;

#[cfg(test)]
mod tests {
    use std::fs;
    use std::path::{Path, PathBuf};

    /// What one target alone has: inline assembly, the compiler's intrinsics for it, and the serial
    /// device reached through its ports.
    const TARGET_ONLY: [&str; 3] = ["asm!", "core::arch", "PioSerial"];

    fn sources(dir: &Path, found: &mut Vec<PathBuf>) {
        for entry in fs::read_dir(dir).unwrap() {
            let path = entry.unwrap().path();
            if path.is_dir() {
                sources(&path, found);
            } else if path.extension().is_some_and(|extension| extension == "rs") {
                found.push(path);
            }
        }
    }

    #[test]
    fn only_the_arch_module_names_a_target_s_instructions_and_devices() {
        let src = Path::new(env!("CARGO_MANIFEST_DIR")).join("src");
        let mut found = Vec::new();
        sources(&src, &mut found);
        let shared: Vec<_> = found.iter().filter(|path| !path.starts_with(src.join("arch"))).collect();
        // main.rs, and the modules it declares.
        assert!(shared.len() > 10, "found only {} shared sources under {}", shared.len(), src.display());
        let mut named = Vec::new();
        for path in shared {
            let text = fs::read_to_string(path).unwrap();
            for needle in TARGET_ONLY {
                if text.contains(needle) {
                    named.push(format!("{} names {}", path.strip_prefix(&src).unwrap().display(), needle));
                }
            }
        }
        assert!(named.is_empty(), "outside arch/: {}", named.join(", "));
    }
}
