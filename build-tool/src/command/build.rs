//! `atmo build`: the workspace build the gate runs, and the same build for aarch64 user code.

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
enum Arch {
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

/// dom0 and the user program that links asys, as aarch64 ELFs. The kernel is not built: it has no
/// virt machine.
async fn aarch64_build(project: &ProjectHandle) -> Result<String> {
    let root = project.root();
    let dom0 = project
        .dom0()
        .build(&spec(&root, "dom0/src/aarch64-unknown-aloader.json"))
        .await
        .context("dom0")?
        .context("dom0 produced no executable")?;
    let hello = project
        .user(PAYLOAD)
        .build(&spec(&root, "user/aarch64-unknown-aloader.json"))
        .await
        .context("hello")?
        .context("hello produced no executable")?;
    let mut lines = Vec::new();
    for path in [dom0, hello] {
        let file = Command::new("file")
            .arg(&path)
            .output()
            .await
            .with_context(|| path.display().to_string())?;
        if !file.status.success() {
            return Err(anyhow!("file {}: {}", path.display(), file.status));
        }
        let text = String::from_utf8_lossy(&file.stdout);
        if !text.contains("ARM aarch64") {
            return Err(anyhow!("{} is not an aarch64 ELF: {}", path.display(), text.trim()));
        }
        lines.push(text.trim().to_string());
    }
    Ok(lines.join("; "))
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

    /// The aarch64 spec beside each x86 spec: no OS, no red zone, soft float, static, panic abort.
    #[test]
    fn aarch64_specs_have_the_x86_specs_role() {
        for path in [
            "kernel/src/aarch64-unknown-aloader.json",
            "dom0/src/aarch64-unknown-aloader.json",
            "user/aarch64-unknown-aloader.json",
        ] {
            let text = spec_text(path);
            for needle in [
                "\"arch\": \"aarch64\"",
                "\"os\": \"none\"",
                "\"disable-redzone\": true",
                "\"abi\": \"softfloat\"",
                "\"rustc-abi\": \"softfloat\"",
                "\"relocation-model\": \"static\"",
                "\"panic-strategy\": \"abort\"",
            ] {
                assert!(text.contains(needle), "{path} missing {needle}");
            }
        }
    }

    #[test]
    fn build_defaults_to_x86_64() {
        let opts = GlobalOpts::try_parse_from(["atmo", "build"]).unwrap();
        match opts.cmd {
            SubCommand::Build(local) => assert_eq!(local.target, Arch::X86_64),
            other => panic!("not build: {other:?}"),
        }
    }

    fn spec_text(path: &str) -> String {
        let full = Path::new(env!("CARGO_MANIFEST_DIR")).join("../").join(path);
        std::fs::read_to_string(&full).unwrap_or_else(|error| panic!("{}: {error}", full.display()))
    }
}
