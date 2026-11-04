//! The gate: what makes a commit tested.

use std::io::ErrorKind;
use std::process::{ExitCode, Stdio};

use anyhow::{anyhow, Context};
use clap::Parser;
use futures::future::join_all;
use tokio::fs;
use tokio::process::Command;

use super::{verify, GlobalOpts, SubCommand};
use crate::error::Result;
use crate::project::{BuildOptions, Project, ProjectHandle};

/// Holds the number of verification errors the gate accepts, relative to the project root.
const VERIFY_ALLOWANCE_PATH: &str = "tools/verify-allowance";

/// The payload `atmo run` loads by default.
const PAYLOAD: &str = "hello";

/// Run the gate.
#[derive(Debug, Parser)]
pub struct Opts {
    /// Seconds dom0 has to boot and finish before the run counts as a hang.
    #[clap(long, default_value_t = 120)]
    boot_timeout: u64,
}

pub(super) async fn run(global: GlobalOpts) -> Result<()> {
    let local = unwrap_command!(global, SubCommand::Test);
    let project = Project::discover()?;

    let results = [
        ("build", check_build(&project).await),
        ("verify", check_verify(&project).await),
        ("boot", check_boot(&project, local.boot_timeout).await),
    ];

    let mut passed = true;
    println!();
    for (name, result) in &results {
        match result {
            Ok(detail) => println!("gate {}: ok: {}", name, detail),
            Err(error) => {
                passed = false;
                println!("gate {}: FAIL: {:#}", name, error);
            }
        }
    }

    if !passed {
        quit::with_code(ExitCode::FAILURE);
    }
    Ok(())
}

async fn check_build(project: &ProjectHandle) -> Result<String> {
    let status = Command::new("cargo")
        .arg("build")
        .current_dir(project.root().join("build-tool"))
        .status()
        .await?;
    if !status.success() {
        return Err(anyhow!("build-tool: {}", status));
    }

    let options = BuildOptions::default();
    project.loader().build(&options).await.context("loader")?;
    project.kernel().build(&options).await.context("kernel")?;
    project.dom0().build(&options).await.context("dom0")?;
    project.user(PAYLOAD).build(&options).await.context("payload")?;

    Ok("build-tool, loader, kernel, dom0 and payload".to_string())
}

async fn check_verify(project: &ProjectHandle) -> Result<String> {
    let path = project.root().join(VERIFY_ALLOWANCE_PATH);
    let allowance = parse_allowance(&fs::read_to_string(&path).await?)
        .ok_or_else(|| anyhow!("{} does not hold a number", VERIFY_ALLOWANCE_PATH))?;

    let roots = verify::verified_crates(project)?;
    let outputs = join_all(roots.iter().map(|root| verify::rust_verify(root, &[]).output())).await;

    let mut errors = 0;
    for (root, output) in roots.iter().zip(outputs) {
        let output = output?;
        let text = String::from_utf8_lossy(&output.stdout) + String::from_utf8_lossy(&output.stderr);
        errors += parse_verify_errors(&text)
            .ok_or_else(|| anyhow!("no verification result from {}", root.display()))?;
    }

    if errors > allowance {
        return Err(anyhow!("{} errors, allowance {}", errors, allowance));
    }
    Ok(format!("{} errors, allowance {}", errors, allowance))
}

async fn check_boot(project: &ProjectHandle, timeout: u64) -> Result<String> {
    let root = project.root();
    let log = root.join("serial.log");
    match fs::remove_file(&log).await {
        Err(error) if error.kind() != ErrorKind::NotFound => return Err(error.into()),
        _ => {}
    }

    // timeout signals its whole process group, which takes QEMU down with atmo.
    let status = Command::new("timeout")
        .arg(timeout.to_string())
        .arg(std::env::current_exe()?)
        .args(&["run", "--kvm"])
        .current_dir(&root)
        .stdin(Stdio::null())
        .status()
        .await?;

    if status.code() == Some(124) {
        return Err(anyhow!("no exit within {} s", timeout));
    }
    if !status.success() {
        return Err(anyhow!("atmo run: {}", status));
    }

    let serial = String::from_utf8_lossy(&fs::read(&log).await?).into_owned();
    if !boot_finished(&serial) {
        return Err(anyhow!("the serial log does not end with dom0's last line"));
    }
    Ok("exit status 0, serial log ends with dom0's last line".to_string())
}

fn parse_allowance(text: &str) -> Option<u64> {
    text.trim().parse().ok()
}

/// Returns the error count from a `verification results:: N verified, M errors` line.
fn parse_verify_errors(output: &str) -> Option<u64> {
    output.lines().find_map(|line| {
        let results = line.split("verification results:: ").nth(1)?;
        results.split(", ").nth(1)?.split(' ').next()?.parse().ok()
    })
}

fn boot_finished(serial: &str) -> bool {
    serial
        .lines()
        .rev()
        .find(|line| !line.trim().is_empty())
        .map_or(false, |line| line.contains("dom0 benchmark done"))
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn allowance_is_one_number() {
        assert_eq!(parse_allowance("2\n"), Some(2));
        assert_eq!(parse_allowance("two\n"), None);
        assert_eq!(parse_allowance(""), None);
    }

    #[test]
    fn verify_errors_come_from_the_results_line() {
        let output = "error: assertion failed\n\nverification results:: 513 verified, 2 errors\nerror: aborting\n";
        assert_eq!(parse_verify_errors(output), Some(2));
        assert_eq!(parse_verify_errors("verification results:: 7 verified, 0 errors\n"), Some(0));
    }

    /// A crate that does not compile prints no results line, which must not read as zero errors.
    #[test]
    fn no_results_line_is_not_zero_errors() {
        assert_eq!(parse_verify_errors("error: cannot find macro\n"), None);
    }

    #[test]
    fn boot_finishes_on_dom0s_last_line() {
        assert!(boot_finished("x\n\u{1b}[34m INFO dom0 benchmark done\u{1b}[0m\n"));
        assert!(boot_finished("x\r\n INFO dom0 benchmark done\r\n\r\n"));
    }

    #[test]
    fn boot_does_not_finish_when_anything_follows() {
        assert!(!boot_finished(" INFO dom0 benchmark done\n INFO CPU 0: Page Fault\n"));
        assert!(!boot_finished(" INFO dom0 benchmark FAILED\n"));
        assert!(!boot_finished(""));
    }
}
