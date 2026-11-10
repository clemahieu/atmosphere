//! `atmo build`: the workspace build the gate runs, and the build of the loader, the kernel and the
//! user code for aarch64.

use std::path::Path;
use std::process::Stdio;

use anyhow::{anyhow, Context};
use cargo_metadata::MetadataCommand;
use clap::{Parser, ValueEnum};
use tokio::process::Command;

use super::{GlobalOpts, SubCommand};
use crate::error::Result;
use crate::project::{BuildOptions, Project, ProjectHandle};

/// The payload tools/run.py loads, and the user program that links asys.
const PAYLOAD: &str = "hello";

/// Build the workspace.
#[derive(Debug, Parser)]
pub struct Opts {
    /// Machine to build for. x86_64 is what `atmo test` builds.
    #[clap(long, value_enum, default_value_t = Arch::X86_64)]
    target: Arch,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, ValueEnum)]
pub(super) enum Arch {
    #[value(name = "x86_64")]
    X86_64,
    #[value(name = "aarch64")]
    Aarch64,
}

impl std::fmt::Display for Arch {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str(match self {
            Arch::X86_64 => "x86_64",
            Arch::Aarch64 => "aarch64",
        })
    }
}

pub(super) async fn run(global: GlobalOpts) -> Result<()> {
    let local = unwrap_command!(global, SubCommand::Build);
    let project = Project::discover()?;
    let detail = match local.target {
        Arch::X86_64 => gate_build(&project).await?,
        Arch::Aarch64 => aarch64_build(&project).await?,
    };
    println!("build {}: {}", local.target, detail);
    Ok(())
}

/// What `atmo test` builds: every workspace member from its own directory, then the loader, the
/// kernel, dom0 and the payload from theirs.
pub(super) async fn gate_build(project: &ProjectHandle) -> Result<String> {
    let members = build_members(project).await?;

    let options = BuildOptions::default();
    let _ = project.loader().build(&options).await.context("loader")?;
    // The measuring build, which no boot here runs, so that it cannot rot unseen.
    let lock_stats = BuildOptions { features: vec!["lock_stats".to_string()], ..BuildOptions::default() };
    let _ = project.kernel().build(&lock_stats).await.context("kernel with lock_stats")?;
    let _ = project.kernel().build(&options).await.context("kernel")?;
    let _ = project.dom0().build(&options).await.context("dom0")?;
    let _ = project.user(PAYLOAD).build(&options).await.context("payload")?;

    Ok(format!(
        "{} workspace members, then the loader, kernel, dom0 and payload from their own directories",
        members
    ))
}

/// The ELFs the aarch64 build makes, each with its target spec: the kernel, dom0 and the user program
/// that links asys.
const AARCH64_ELF_SPECS: [(&str, &str); 3] = [
    ("kernel", "kernel/src/aarch64-unknown-aloader.json"),
    ("dom0", "dom0/src/aarch64-unknown-aloader.json"),
    (PAYLOAD, "user/aarch64-unknown-aloader.json"),
];

/// The loader as an aarch64 EFI application, and the kernel, dom0 and the user program that links
/// asys as aarch64 ELFs.
async fn aarch64_build(project: &ProjectHandle) -> Result<String> {
    let root = project.root();
    let loader = project
        .loader()
        .build(&BuildOptions { target: Some(LOADER_AARCH64_TARGET.into()), ..BuildOptions::default() })
        .await
        .context("loader")?
        .context("loader produced no executable")?;
    let mut images = vec![(loader, Image::EfiApplication)];
    for (name, target) in AARCH64_ELF_SPECS {
        let package = match name {
            "kernel" => project.kernel(),
            "dom0" => project.dom0(),
            user => project.user(user),
        };
        let path = package
            .build(&spec(&root, target))
            .await
            .context(name)?
            .with_context(|| format!("{name} produced no executable"))?;
        images.push((path, Image::Elf));
    }
    let mut lines = Vec::new();
    for (path, image) in images {
        let file = Command::new("file")
            .arg(&path)
            .output()
            .await
            .with_context(|| path.display().to_string())?;
        if !file.status.success() {
            return Err(anyhow!("file {}: {}", path.display(), file.status));
        }
        let text = String::from_utf8_lossy(&file.stdout);
        if !image.describes(&text) {
            return Err(anyhow!("{} is not an aarch64 {}: {}", path.display(), image.name(), text.trim()));
        }
        lines.push(text.trim().to_string());
    }
    Ok(lines.join("; "))
}

/// The triple the aarch64 loader is built for, one rustc has built in; aloader's own config names
/// the x86_64 one.
const LOADER_AARCH64_TARGET: &str = "aarch64-unknown-uefi";

/// What an image the aarch64 build makes is.
#[derive(Debug, Clone, Copy)]
enum Image {
    /// What the loader loads: the kernel, dom0 and a user program, each a static
    /// position-independent executable, which the loader places where it has memory.
    Elf,
    /// What the firmware starts: the loader.
    EfiApplication,
}

impl Image {
    fn name(self) -> &'static str {
        match self {
            Image::Elf => "ELF",
            Image::EfiApplication => "EFI application",
        }
    }

    /// Whether `file`'s line for an image says it is an aarch64 image of this kind.
    fn describes(self, description: &str) -> bool {
        match self {
            Image::Elf => {
                description.contains("ELF 64-bit")
                    && description.contains("pie executable, ARM aarch64")
                    && description.contains("static-pie linked")
            }
            Image::EfiApplication => description.contains("PE32+ executable for EFI (application), ARM64"),
        }
    }
}

fn spec(root: &Path, relative: &str) -> BuildOptions {
    BuildOptions { target: Some(root.join(relative)), ..BuildOptions::default() }
}

/// Builds every workspace member from its own directory, since each no_std crate takes its target from its
/// own .cargo config. A member built only as another's dependency, or not at all, could otherwise stop
/// building unseen.
async fn build_members(project: &ProjectHandle) -> Result<usize> {
    let metadata = MetadataCommand::new().current_dir(project.root()).no_deps().exec()?;
    let packages = metadata.workspace_packages();
    let mut failed = Vec::new();
    for package in &packages {
        let dir = package.manifest_path.parent().expect("a manifest lies in its package's directory");
        let status = Command::new("cargo")
            .arg("build")
            .current_dir(dir)
            .stdin(Stdio::null())
            .status()
            .await
            .with_context(|| package.name.clone())?;
        if !status.success() {
            failed.push(package.name.as_str());
        }
    }
    if !failed.is_empty() {
        return Err(anyhow!("from its own directory, does not build: {}", failed.join(", ")));
    }
    Ok(packages.len())
}

#[cfg(test)]
mod tests {
    use clap::Parser;

    use super::*;

    /// The aarch64 build makes the kernel, then dom0 and the user program, each from the spec beside
    /// its x86 one.
    #[test]
    fn the_aarch64_build_lists_the_kernel_with_dom0_and_the_payload() {
        assert_eq!(
            AARCH64_ELF_SPECS,
            [
                ("kernel", "kernel/src/aarch64-unknown-aloader.json"),
                ("dom0", "dom0/src/aarch64-unknown-aloader.json"),
                ("hello", "user/aarch64-unknown-aloader.json"),
            ]
        );
    }

    /// The aarch64 spec beside each x86 spec: no OS, no red zone, soft float, panic abort, and the
    /// x86 spec's relocation model, a static position-independent executable, which is the only
    /// kind the loader places (aelf's `NotRelocatable`).
    #[test]
    fn aarch64_specs_have_the_x86_specs_role() {
        for (_, path) in AARCH64_ELF_SPECS {
            let text = spec_text(path);
            for needle in [
                "\"arch\": \"aarch64\"",
                "\"os\": \"none\"",
                "\"disable-redzone\": true",
                "\"abi\": \"softfloat\"",
                "\"rustc-abi\": \"softfloat\"",
                "\"panic-strategy\": \"abort\"",
            ] {
                assert!(text.contains(needle), "{path} missing {needle}");
            }
            let x86_path = path.replace("aarch64", "x86_64");
            let x86 = spec_text(&x86_path);
            assert_eq!(relocation(&x86), ["\"relocation-model\": \"pie\",", "\"-pie\","], "{x86_path}");
            assert_eq!(relocation(&text), relocation(&x86), "{path} against {x86_path}");
        }
    }

    /// A spec's lines that decide whether its executable can be placed at any address: the
    /// relocation model the compiler generates code for, and the linker's own flag for the image.
    fn relocation(spec: &str) -> Vec<&str> {
        spec.lines().map(str::trim).filter(|line| line.contains("relocation-model") || line.contains("-pie")).collect()
    }

    /// `file`'s line for each image the aarch64 build makes, and for the x86_64 ones beside them.
    const AARCH64_ELF: &str = "dom0: ELF 64-bit LSB pie executable, ARM aarch64, version 1 (SYSV), static-pie linked, with debug_info, not stripped";
    /// The same image linked at a fixed address, which the loader refuses.
    const AARCH64_FIXED_ELF: &str = "dom0: ELF 64-bit LSB executable, ARM aarch64, version 1 (SYSV), statically linked, with debug_info, not stripped";
    const X86_64_ELF: &str = "dom0: ELF 64-bit LSB pie executable, x86-64, version 1 (SYSV), static-pie linked, with debug_info, not stripped";
    const AARCH64_EFI: &str = "aloader.efi: PE32+ executable for EFI (application), ARM64, 4 sections";
    const X86_64_EFI: &str = "aloader.efi: PE32+ executable for EFI (application), x86-64, 5 sections";

    #[test]
    fn an_aarch64_image_is_told_from_an_x86_64_one_and_an_elf_from_an_efi_application() {
        assert!(Image::Elf.describes(AARCH64_ELF));
        assert!(Image::EfiApplication.describes(AARCH64_EFI));
        for other in [AARCH64_FIXED_ELF, X86_64_ELF, AARCH64_EFI, X86_64_EFI] {
            assert!(!Image::Elf.describes(other), "{other}");
        }
        for other in [AARCH64_ELF, X86_64_ELF, X86_64_EFI] {
            assert!(!Image::EfiApplication.describes(other), "{other}");
        }
        // An EFI image of another kind is not one the firmware starts as an application.
        assert!(!Image::EfiApplication.describes("driver.efi: PE32+ executable for EFI (boot service driver), ARM64, 4 sections"));
    }

    #[test]
    fn build_defaults_to_x86_64() {
        let opts = GlobalOpts::try_parse_from(["atmo", "build"]).unwrap();
        match opts.cmd {
            SubCommand::Build(local) => assert_eq!(local.target, Arch::X86_64),
            other => panic!("not build: {other:?}"),
        }
    }

    /// What only an x86 kernel names: its instructions, registers and descriptor tables, as the
    /// lower-case words between a source's punctuation.
    const X86_WORDS: [&str; 24] = [
        "x86", "rdtsc", "tsc", "msr", "gdt", "tss", "idt", "ist", "cr0", "cr3", "cr4", "pcid", "pcide", "rsp",
        "rip", "rax", "rdi", "rsi", "apic", "ioapic", "iopl", "sysret", "lgdt", "hlt",
    ];
    /// The same names as the capitalised parts of a type's name, and inline assembly for any target.
    const ARCH_ONLY_TEXT: [&str; 7] = ["Gdt", "Tss", "Idt", "Ist", "Apic", "Msr", "asm!"];

    /// The kernel's sources outside arch/ build for every target, so they name no x86 item and hold
    /// no inline assembly (design/arch-module/ item 5). A line that selects by target_arch is the
    /// selection itself.
    #[test]
    fn kernel_shared_sources_name_no_x86() {
        let src = Path::new(env!("CARGO_MANIFEST_DIR")).join("../kernel/src");
        let mut sources = Vec::new();
        rust_sources(&src, &src.join("arch"), &mut sources);
        assert!(sources.len() > 10, "found only {} shared sources under {}", sources.len(), src.display());
        let mut named = Vec::new();
        for path in sources {
            let text = std::fs::read_to_string(&path).unwrap();
            for (number, line) in text.lines().enumerate() {
                if line.contains("target_arch") {
                    continue;
                }
                let lower = line.to_ascii_lowercase();
                let words = lower.split(|c: char| !c.is_ascii_alphanumeric());
                let word = words.filter(|word| X86_WORDS.contains(word));
                let text = ARCH_ONLY_TEXT.iter().copied().filter(|text| line.contains(text));
                for found in word.chain(text) {
                    named.push(format!("{}:{}: {found}", path.strip_prefix(&src).unwrap().display(), number + 1));
                }
            }
        }
        assert!(named.is_empty(), "x86 named outside kernel/src/arch:\n{}", named.join("\n"));
    }

    fn rust_sources(dir: &Path, skip: &Path, found: &mut Vec<std::path::PathBuf>) {
        for entry in std::fs::read_dir(dir).unwrap() {
            let path = entry.unwrap().path();
            if path.is_dir() {
                if path != skip {
                    rust_sources(&path, skip, found);
                }
            } else if path.extension().is_some_and(|extension| extension == "rs") {
                found.push(path);
            }
        }
    }

    fn spec_text(path: &str) -> String {
        let full = Path::new(env!("CARGO_MANIFEST_DIR")).join("../").join(path);
        std::fs::read_to_string(&full).unwrap_or_else(|error| panic!("{}: {error}", full.display()))
    }
}
