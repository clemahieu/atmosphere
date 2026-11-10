//! `atmo board`: dom0 booted on QEMU virt under KVM on the Orange Pi, held to the boot checks the gate
//! holds the x86_64 boot to. The board is not part of the gate.

use std::process::Stdio;

use anyhow::{anyhow, Context};
use clap::Parser;
use tokio::fs;
use tokio::process::Command;

use super::build::Arch;
use super::test::boot_serial_accepted;
use super::{GlobalOpts, SubCommand};
use crate::error::Result;
use crate::project::{Project, ProjectHandle};

/// Builds the aarch64 images and lays out the partition the board boots, relative to the project root.
const ESP_BUILD: &str = "tools/aarch64-esp.py";

/// Boots a partition on the board, relative to the project root.
const BOARD_RUN: &str = "tools/orangepi-kvm.py";

/// The partition, relative to the project root.
const ESP: &str = "target/orangepi-esp";

/// What the board run printed, the serial log among it, relative to the project root.
const SERIAL_LOG: &str = "target/orangepi-serial.log";

/// The guest's memory: enough that 2 to 3 GiB is free RAM on virt, design/test-guest-memory/.
const MEMORY_MIB: &str = "2560";

/// Boot dom0 on the board and check its serial log.
#[derive(Debug, Parser)]
pub struct Opts {
    /// Seconds the guest has to boot, finish and power off before the run counts as a failure.
    #[clap(long, default_value_t = 60)]
    boot_timeout: u64,
}

pub(super) async fn run(global: GlobalOpts) -> Result<()> {
    let local = unwrap_command!(global, SubCommand::Board);
    let project = Project::discover()?;
    let (code, output) = boot(&project, local.boot_timeout).await?;
    println!("board serial log: {}", project.root().join(SERIAL_LOG).display());
    let held = board_run_accepted(code, &output)?;
    println!("board: ok: {}", held);
    Ok(())
}

/// Builds the partition, boots it on the board until QEMU exits, and returns the runner's exit code
/// and what it printed, which it also writes to the serial log.
async fn boot(project: &ProjectHandle, timeout: u64) -> Result<(Option<i32>, String)> {
    let root = project.root();
    let built = Command::new(root.join(ESP_BUILD))
        .arg(ESP)
        .current_dir(&root)
        .stdin(Stdio::null())
        .status()
        .await
        .with_context(|| ESP_BUILD.to_string())?;
    if !built.success() {
        return Err(anyhow!("{} {}: {}", ESP_BUILD, ESP, built));
    }
    let timeout = timeout.to_string();
    let ran = Command::new(root.join(BOARD_RUN))
        .args(["--esp", ESP, "--memory-mib", MEMORY_MIB, "--boot-timeout", &timeout, "--until-exit"])
        .current_dir(&root)
        .stdin(Stdio::null())
        .stderr(Stdio::inherit())
        .output()
        .await
        .with_context(|| BOARD_RUN.to_string())?;
    fs::write(root.join(SERIAL_LOG), &ran.stdout).await?;
    Ok((ran.status.code(), String::from_utf8_lossy(&ran.stdout).into_owned()))
}

/// Whether the board run is a successful boot: the board was reached, QEMU exited by itself with
/// status 0, which on virt follows only the power-off of a run that succeeded, and the serial log
/// shows what the gate requires of the x86_64 boot's.
fn board_run_accepted(code: Option<i32>, output: &str) -> Result<String> {
    if let Some(skip) = output.lines().find(|line| line.starts_with("skip: ")) {
        return Err(anyhow!("no run: {}", skip));
    }
    if code != Some(0) {
        return Err(anyhow!("{} exited with {:?}: QEMU did not exit 0 within the timeout", BOARD_RUN, code));
    }
    boot_serial_accepted(output, Arch::Aarch64)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::command::test::tests::boot_log;

    /// A board run's output: the runner's lines, the serial log of a boot on virt, and QEMU's exit.
    fn board_output() -> String {
        format!(
            "host: orangepi5\nkvm: accel kvm\nguest: started\n{}\u{1b}[34m INFO The system is shutting down...\u{1b}[0m\nqemu: exit 0\n",
            boot_log().replace("base 0x40000000 order 18", "base 0x80000000 order 18")
        )
    }

    #[test]
    fn a_run_that_powered_off_after_every_check_passes() {
        assert!(board_run_accepted(Some(0), &board_output()).unwrap().contains("2 to 3 GiB as one 1G untyped"));
    }

    #[test]
    fn a_run_still_on_at_the_timeout_fails() {
        let output = board_output().replace("qemu: exit 0\n", "qemu: still running after 60 s\n");
        assert!(board_run_accepted(Some(1), &output).unwrap_err().to_string().contains("did not exit 0"));
    }

    #[test]
    fn a_run_whose_checks_failed_fails_whatever_qemu_did() {
        let output = board_output().replace("dom0 slot checks held\ndom0 capability done\n", "dom0 slot checks failed\n");
        assert!(board_run_accepted(Some(1), &output).is_err());
        assert!(board_run_accepted(Some(0), &output).unwrap_err().to_string().contains("check line"));
    }

    #[test]
    fn a_run_on_the_pc_s_memory_map_fails() {
        let output = board_output().replace("base 0x80000000 order 18", "base 0x40000000 order 18");
        assert!(board_run_accepted(Some(0), &output).unwrap_err().to_string().contains("2 to 3 GiB"));
    }

    #[test]
    fn an_unreachable_board_is_no_run() {
        let output = "skip: orangepi5 unreachable\n";
        assert!(board_run_accepted(Some(0), output).unwrap_err().to_string().contains("no run: skip: orangepi5 unreachable"));
    }
}
