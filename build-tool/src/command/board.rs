//! `atmo board`: dom0 booted on QEMU virt under KVM on the Orange Pi, held to the boot checks the gate
//! holds the x86_64 boot to. The gate's aarch64 boot is that run twice, first with an SMMUv3 on the
//! machine, as the x86_64 boot is with an IOMMU, then without, with an unreachable board taken as a
//! skip rather than a failure.

use std::process::Stdio;

use anyhow::{anyhow, Context};
use clap::Parser;
use tokio::fs;
use tokio::process::Command;

use super::build::Arch;
use super::test::{boot_serial_accepted, TRANSLATION_ENABLED};
use super::{GlobalOpts, SubCommand};
use crate::error::Result;
use crate::project::{Project, ProjectHandle};

/// Builds the aarch64 images and lays out the partition the board boots, relative to the project root.
const ESP_BUILD: &str = "tools/aarch64-esp.py";

/// Boots a partition on the board, relative to the project root; `--test` runs its own tests.
const BOARD_RUN: &str = "tools/orangepi-kvm.py";

/// What the runner prints first: the name of the host the guest ran on.
const HOST: &str = "host: ";

/// What the runner prints when it launches QEMU with KVM as its only accelerator.
const KVM: &str = "kvm: accel kvm";

/// What the runner prints, as its only line, when ssh cannot reach the board.
const SKIP: &str = "skip: ";

/// The partition, relative to the project root.
const ESP: &str = "target/orangepi-esp";

/// What the board run printed, the serial log among it, relative to the project root.
const SERIAL_LOG: &str = "target/orangepi-serial.log";

/// The guest's memory: enough that 2 to 3 GiB is free RAM on virt, design/test-guest-memory/.
const MEMORY_MIB: &str = "2560";

/// The command-line key under which the kernel leaves `TCR_EL1.HA` and `HD` clear, so that its own
/// faults keep the access flag and the dirty state. design/arch-module/ item 5.
const FAULT_KEPT: &str = "access_dirty=fault";

/// What the kernel logs at the power-off of a run: the faults it served in the walker's place.
const FAULTS_SERVED: &str = "Served from EL0: ";

/// Boot dom0 on the board and check its serial log.
#[derive(Debug, Parser)]
pub struct Opts {
    /// Seconds the guest has to boot, finish and power off before the run counts as a failure.
    #[clap(long, default_value_t = 60)]
    boot_timeout: u64,

    /// The kernel's command line, which the partition's cmdline file holds. With access_dirty=fault
    /// the run must also show that the kernel served both kinds of fault that stand in for the walker.
    #[clap(long)]
    command_line: Option<String>,

    /// Put an SMMUv3 on the machine, and require the kernel to enable its translation.
    #[clap(long)]
    iommu: bool,
}

pub(super) async fn run(global: GlobalOpts) -> Result<()> {
    let local = unwrap_command!(global, SubCommand::Board);
    let project = Project::discover()?;
    let command_line = local.command_line.as_deref();
    build(&project, command_line).await?;
    let (code, output) = boot(&project, local.boot_timeout, local.iommu).await?;
    println!("board serial log: {}", project.root().join(SERIAL_LOG).display());
    let mut held = board_run_accepted(code, &output, command_line)?;
    if local.iommu {
        held = translation_enabled(&output, held)?;
    }
    println!("board: ok: {}", held);
    Ok(())
}

/// The gate's aarch64 boot: the build's and the runner's own tests, then the run with an SMMUv3 and
/// the run without, so the serial log left behind has none, as on x86_64. A board that ssh cannot
/// reach does not fail the gate; the runner's skip line is printed on a line of its own, which is what
/// the round procedure looks for in a gate log, and the step reports it.
pub(super) async fn gate_boot(project: &ProjectHandle, timeout: u64) -> Result<String> {
    for program in [ESP_BUILD, BOARD_RUN] {
        let status = Command::new(project.root().join(program))
            .arg("--test")
            .current_dir(project.root())
            .stdin(Stdio::null())
            .status()
            .await
            .with_context(|| program.to_string())?;
        if !status.success() {
            return Err(anyhow!("{} --test: {}", program, status));
        }
    }
    build(project, None).await?;
    let (code, output) = boot(project, timeout, true).await?;
    let held = match gate_run_accepted(code, &output)? {
        skip if skip.starts_with(SKIP) => {
            println!("{}", output.trim_end());
            skip
        }
        held => {
            let with = translation_enabled(&output, held)?;
            let (code, output) = boot(project, timeout, false).await?;
            format!("with an SMMUv3, {}; without, {}", with, board_run_accepted(code, &output, None)?)
        }
    };
    Ok(format!("{}'s and {}'s tests pass; {}", ESP_BUILD, BOARD_RUN, held))
}

/// What a run with an SMMUv3 holds besides [`board_run_accepted`]: the kernel enabled its translation.
fn translation_enabled(output: &str, held: String) -> Result<String> {
    if !output.contains(TRANSLATION_ENABLED) {
        return Err(anyhow!("the serial log does not show the SMMUv3's translation enabled"));
    }
    Ok(format!("translation enabled; {}", held))
}

/// What the gate takes from a board run: the skip line of a board that was not reached, or what
/// [`board_run_accepted`] holds of one that was.
fn gate_run_accepted(code: Option<i32>, output: &str) -> Result<String> {
    match skip_line(output) {
        Some(skip) if code == Some(0) => Ok(format!("{}: this commit did not boot on aarch64", skip)),
        _ => board_run_accepted(code, output, None),
    }
}

/// The runner's skip line, when it printed one.
fn skip_line(output: &str) -> Option<&str> {
    output.lines().find(|line| line.starts_with(SKIP))
}

/// Builds the partition, with `command_line` in its cmdline file when given.
async fn build(project: &ProjectHandle, command_line: Option<&str>) -> Result<()> {
    let root = project.root();
    let mut build = Command::new(root.join(ESP_BUILD));
    build.arg(ESP);
    if let Some(line) = command_line {
        build.args(["--command-line", line]);
    }
    let built = build
        .current_dir(&root)
        .stdin(Stdio::null())
        .status()
        .await
        .with_context(|| ESP_BUILD.to_string())?;
    if !built.success() {
        return Err(anyhow!("{} {}: {}", ESP_BUILD, ESP, built));
    }
    Ok(())
}

/// Boots the partition on the board until QEMU exits, with an SMMUv3 on the machine under `iommu`,
/// and returns the runner's exit code and what it printed, which it also writes to the serial log.
async fn boot(project: &ProjectHandle, timeout: u64, iommu: bool) -> Result<(Option<i32>, String)> {
    let root = project.root();
    let timeout = timeout.to_string();
    let mut run = Command::new(root.join(BOARD_RUN));
    run.args(["--esp", ESP, "--memory-mib", MEMORY_MIB, "--boot-timeout", &timeout, "--until-exit"]);
    if iommu {
        run.arg("--iommu");
    }
    let ran = run
        .current_dir(&root)
        .stdin(Stdio::null())
        .stderr(Stdio::inherit())
        .output()
        .await
        .with_context(|| BOARD_RUN.to_string())?;
    fs::write(root.join(SERIAL_LOG), &ran.stdout).await?;
    Ok((ran.status.code(), String::from_utf8_lossy(&ran.stdout).into_owned()))
}

/// Whether the board run is a successful boot: the board was reached, the runner named the host and
/// launched QEMU under KVM, QEMU exited by itself with status 0, which on virt follows only the
/// power-off of a run that succeeded, and the serial log shows what the gate requires of the x86_64
/// boot's. Under `command_line` holding [`FAULT_KEPT`] it
/// also shows that the kernel served at least one access-flag fault and one dirty-state fault.
fn board_run_accepted(code: Option<i32>, output: &str, command_line: Option<&str>) -> Result<String> {
    if let Some(skip) = skip_line(output) {
        return Err(anyhow!("no run: {}", skip));
    }
    let host = output
        .lines()
        .find_map(|line| line.strip_prefix(HOST))
        .ok_or_else(|| anyhow!("{} did not name the host it ran on", BOARD_RUN))?;
    if !output.lines().any(|line| line == KVM) {
        return Err(anyhow!("{} did not say it launched QEMU under KVM", BOARD_RUN));
    }
    if code != Some(0) {
        return Err(anyhow!("{} exited with {:?}: QEMU did not exit 0 within the timeout", BOARD_RUN, code));
    }
    let held = format!("on {} under KVM: {}", host, boot_serial_accepted(output, Arch::Aarch64)?);
    if !command_line.is_some_and(|line| line.split(' ').any(|component| component == FAULT_KEPT)) {
        return Ok(held);
    }
    match faults_served(output) {
        Some((access, dirty)) if access > 0 && dirty > 0 => {
            Ok(format!("{}; {} access-flag and {} dirty-state faults served", held, access, dirty))
        }
        Some((access, dirty)) => Err(anyhow!(
            "under {} the kernel served {} access-flag and {} dirty-state faults, and both kinds must reach it",
            FAULT_KEPT,
            access,
            dirty
        )),
        None => Err(anyhow!("under {} the log has no line '{}'", FAULT_KEPT, FAULTS_SERVED.trim_end())),
    }
}

/// The counts of the kernel's line `Served from EL0: <a> access-flag faults, <d> dirty-state faults`.
fn faults_served(output: &str) -> Option<(u64, u64)> {
    let line = output.lines().find_map(|line| line.split_once(FAULTS_SERVED))?.1;
    let (access, dirty) = line.split_once(" access-flag faults, ")?;
    let dirty = dirty.split_once(" dirty-state faults")?.0;
    Some((access.parse().ok()?, dirty.parse().ok()?))
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
        assert!(board_run_accepted(Some(0), &board_output(), None).unwrap().contains("2 to 3 GiB as one 1G untyped"));
    }

    #[test]
    fn a_run_still_on_at_the_timeout_fails() {
        let output = board_output().replace("qemu: exit 0\n", "qemu: still running after 60 s\n");
        assert!(board_run_accepted(Some(1), &output, None).unwrap_err().to_string().contains("did not exit 0"));
    }

    #[test]
    fn a_run_whose_checks_failed_fails_whatever_qemu_did() {
        let output = board_output().replace("dom0 slot checks held\ndom0 capability done\n", "dom0 slot checks failed\n");
        assert!(board_run_accepted(Some(1), &output, None).is_err());
        assert!(board_run_accepted(Some(0), &output, None).unwrap_err().to_string().contains("check line"));
    }

    #[test]
    fn a_run_on_the_pc_s_memory_map_fails() {
        let output = board_output().replace("base 0x80000000 order 18", "base 0x40000000 order 18");
        assert!(board_run_accepted(Some(0), &output, None).unwrap_err().to_string().contains("2 to 3 GiB"));
    }

    /// A board run under the key, with the kernel's line of the faults it served.
    fn fault_kept_output(access: u64, dirty: u64) -> String {
        board_output().replace(
            "\u{1b}[34m INFO The system is shutting down",
            &format!(
                "\u{1b}[34m INFO Served from EL0: {} access-flag faults, {} dirty-state faults\u{1b}[0m\n\u{1b}[34m INFO The system is shutting down",
                access, dirty
            ),
        )
    }

    #[test]
    fn a_run_under_the_key_that_served_both_faults_passes() {
        let held = board_run_accepted(Some(0), &fault_kept_output(310, 42), Some("nologo access_dirty=fault")).unwrap();
        assert!(held.contains("310 access-flag and 42 dirty-state faults served"), "{}", held);
    }

    #[test]
    fn a_run_under_the_key_that_served_none_of_a_kind_fails() {
        let error = board_run_accepted(Some(0), &fault_kept_output(310, 0), Some("access_dirty=fault")).unwrap_err();
        assert!(error.to_string().contains("310 access-flag and 0 dirty-state"), "{}", error);
        assert!(board_run_accepted(Some(0), &fault_kept_output(0, 42), Some("access_dirty=fault")).is_err());
    }

    #[test]
    fn a_run_under_the_key_without_the_line_fails() {
        let error = board_run_accepted(Some(0), &board_output(), Some("access_dirty=fault")).unwrap_err();
        assert!(error.to_string().contains("has no line"), "{}", error);
    }

    #[test]
    fn the_line_is_not_asked_of_a_run_without_the_key() {
        assert!(board_run_accepted(Some(0), &board_output(), Some("nologo")).is_ok());
        assert!(board_run_accepted(Some(0), &fault_kept_output(0, 0), None).is_ok());
    }

    #[test]
    fn a_run_names_the_host_it_ran_on_and_kvm() {
        let held = board_run_accepted(Some(0), &board_output(), None).unwrap();
        assert!(held.starts_with("on orangepi5 under KVM: "), "{}", held);
    }

    #[test]
    fn a_run_that_does_not_name_its_host_or_kvm_fails() {
        let output = board_output().replace("host: orangepi5\n", "");
        assert!(board_run_accepted(Some(0), &output, None).unwrap_err().to_string().contains("host"));
        let output = board_output().replace("kvm: accel kvm\n", "");
        assert!(board_run_accepted(Some(0), &output, None).unwrap_err().to_string().contains("KVM"));
    }

    #[test]
    fn the_gate_takes_an_unreachable_board_as_a_skip() {
        let held = gate_run_accepted(Some(0), "skip: orangepi5 unreachable\n").unwrap();
        assert!(held.starts_with("skip: orangepi5 unreachable"), "{}", held);
    }

    #[test]
    fn the_gate_holds_a_reached_board_to_the_boot_checks() {
        assert!(gate_run_accepted(Some(0), &board_output()).unwrap().starts_with("on orangepi5 under KVM: "));
        let output = board_output().replace("dom0 slot checks held\ndom0 capability done\n", "dom0 slot checks failed\n");
        assert!(gate_run_accepted(Some(1), &output).is_err());
        assert!(gate_run_accepted(Some(2), "host: orangepi5\nkvm: accel kvm\n").is_err());
    }

    /// A board run with an SMMUv3, whose kernel enabled its translation.
    fn iommu_output() -> String {
        board_output().replace(
            "\u{1b}[34m INFO The system is shutting down",
            "\u{1b}[34m INFO Enabling translation\u{1b}[0m\n\u{1b}[34m INFO The system is shutting down",
        )
    }

    #[test]
    fn a_run_with_an_smmu_that_enabled_translation_passes() {
        let held = board_run_accepted(Some(0), &iommu_output(), None).unwrap();
        let held = translation_enabled(&iommu_output(), held).unwrap();
        assert!(held.starts_with("translation enabled; on orangepi5 under KVM: "), "{}", held);
    }

    #[test]
    fn a_run_with_an_smmu_that_did_not_enable_translation_fails() {
        let held = board_run_accepted(Some(0), &board_output(), None).unwrap();
        let error = translation_enabled(&board_output(), held).unwrap_err();
        assert!(error.to_string().contains("translation enabled"), "{}", error);
    }

    #[test]
    fn an_unreachable_board_is_no_run() {
        let output = "skip: orangepi5 unreachable\n";
        assert!(board_run_accepted(Some(0), output, None).unwrap_err().to_string().contains("no run: skip: orangepi5 unreachable"));
    }
}
