//! The gate: what makes a commit tested.

use std::io::ErrorKind;
use std::process::{ExitCode, Stdio};

use anyhow::{anyhow, Context};
use cargo_metadata::MetadataCommand;
use clap::Parser;
use futures::future::join_all;
use tokio::fs;
use tokio::process::Command;

use super::{external_body, license, verify, GlobalOpts, SubCommand};
use crate::error::Result;
use crate::project::{BuildOptions, Project, ProjectHandle};

/// Holds the number of verification errors the gate accepts, relative to the project root.
const VERIFY_ALLOWANCE_PATH: &str = "tools/verify-allowance";

/// The license guard's tests, relative to the project root.
const LICENSE_GUARD_TEST: &str = ".claude/hooks/license-guard-test.sh";

/// The boot stack's check, relative to the project root.
const BOOT_STACK_CHECK: &str = "tools/check-boot-stack.py";

/// The coverage report, relative to the project root.
const COVERAGE: &str = "tools/coverage.py";

/// The design index builder, relative to the project root; `--check` says whether the index is current.
const DESIGN_INDEX: &str = "tools/build-design-index.py";

/// The largest file the tree may hold. The largest source is a seventh of this, so anything over it is
/// a build or solver output that .gitignore missed.
const MAX_FILE_BYTES: u64 = 1024 * 1024;

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
        ("file sizes", check_file_sizes(&project).await),
        ("build", check_build(&project).await),
        ("license", license::check(&project)),
        ("license guard", check_license_guard(&project).await),
        ("verify", check_verify(&project).await),
        ("external body", external_body::check(&project)),
        ("design index", check_design_index(&project).await),
        ("boot stack", check_boot_stack(&project).await),
        ("coverage", check_coverage(&project).await),
        ("capability boot", check_capability_boot(&project, local.boot_timeout).await),
        ("iommu boot", check_iommu_boot(&project, local.boot_timeout).await),
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

/// Looks at everything `git add -A` would take, tracked or not, since the gate runs before the commit.
async fn check_file_sizes(project: &ProjectHandle) -> Result<String> {
    let root = project.root();
    let output = Command::new("git")
        .args(["ls-files", "-z", "--cached", "--others", "--exclude-standard"])
        .current_dir(&root)
        .output()
        .await?;
    if !output.status.success() {
        return Err(anyhow!("git ls-files: {}", output.status));
    }
    let listing = String::from_utf8(output.stdout).context("git ls-files")?;
    let mut sizes = Vec::new();
    for path in listing.split('\0').filter(|path| !path.is_empty()) {
        match fs::symlink_metadata(root.join(path)).await {
            Ok(metadata) => sizes.push((path, metadata.len())),
            // Deleted and not yet staged, so the commit will not hold it.
            Err(error) if error.kind() == ErrorKind::NotFound => {}
            Err(error) => return Err(error).context(path.to_string()),
        }
    }
    let over = oversized(&sizes);
    if !over.is_empty() {
        return Err(anyhow!("over {} bytes: {}", MAX_FILE_BYTES, over.join(", ")));
    }
    Ok(format!("{} files, none over {} bytes", sizes.len(), MAX_FILE_BYTES))
}

fn oversized<'a>(sizes: &[(&'a str, u64)]) -> Vec<&'a str> {
    sizes.iter().filter(|(_, size)| *size > MAX_FILE_BYTES).map(|(path, _)| *path).collect()
}

async fn check_build(project: &ProjectHandle) -> Result<String> {
    let members = build_members(project).await?;

    let options = BuildOptions::default();
    project.loader().build(&options).await.context("loader")?;
    // The measuring build, which no boot here runs, so that it cannot rot unseen.
    let lock_stats = BuildOptions { features: vec!["lock_stats".to_string()], ..BuildOptions::default() };
    project.kernel().build(&lock_stats).await.context("kernel with lock_stats")?;
    project.kernel().build(&options).await.context("kernel")?;
    project.dom0().build(&options).await.context("dom0")?;
    project.user(PAYLOAD).build(&options).await.context("payload")?;

    Ok(format!("{} workspace members, then the loader, kernel, dom0 and payload as atmo run builds them", members))
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

async fn check_license_guard(project: &ProjectHandle) -> Result<String> {
    run_check(project, LICENSE_GUARD_TEST, &[]).await?;
    Ok("the guard refuses what it must".to_string())
}

async fn check_boot_stack(project: &ProjectHandle) -> Result<String> {
    // Each profile's overflow build comes first, so the images left behind are the normal ones.
    let runs: [&[&str]; 4] = [
        &["debug", "overflow"],
        &["debug"],
        &["release", "overflow"],
        &["release"],
    ];
    for args in runs {
        run_check(project, BOOT_STACK_CHECK, args).await?;
    }
    Ok("debug and release, normal and overflow".to_string())
}

/// `design/INDEX.md` is generated from the records, so a record edited without regenerating it would leave
/// the index saying something the records do not.
async fn check_design_index(project: &ProjectHandle) -> Result<String> {
    run_check(project, DESIGN_INDEX, &["--check"]).await?;
    Ok("design/INDEX.md is current".to_string())
}

/// Reports coverage per crate. A low number does not fail the gate: only a capture that fails does.
async fn check_coverage(project: &ProjectHandle) -> Result<String> {
    let root = project.root();
    let output = Command::new(root.join(COVERAGE))
        .current_dir(&root)
        .stdin(Stdio::null())
        .stderr(Stdio::inherit())
        .output()
        .await
        .with_context(|| COVERAGE.to_string())?;
    if !output.status.success() {
        return Err(anyhow!("{}: {}", COVERAGE, output.status));
    }
    let report = String::from_utf8_lossy(&output.stdout);
    Ok(format!("\n  {}", report.trim_end().replace('\n', "\n  ")))
}

/// Runs a check from the tree, at the project root; it reports on failure with its exit status.
async fn run_check(project: &ProjectHandle, program: &str, args: &[&str]) -> Result<()> {
    let root = project.root();
    let status = Command::new(root.join(program))
        .args(args)
        .current_dir(&root)
        .stdin(Stdio::null())
        .status()
        .await
        .with_context(|| program.to_string())?;
    if !status.success() {
        return Err(anyhow!("{} {}: {}", program, args.join(" "), status));
    }
    Ok(())
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
    boot(project, timeout, &["run"]).await?;
    Ok("exit status 0, serial log ends with dom0's last line".to_string())
}

/// Boots with an IOMMU present, the only way the device syscalls run past their first check. The
/// plain boot comes after it, so the benchmark numbers and serial.log it leaves have no IOMMU.
async fn check_iommu_boot(project: &ProjectHandle, timeout: u64) -> Result<String> {
    let serial = boot(project, timeout, &["run", "--iommu"]).await?;
    if !iommu_boot_ran(&serial) {
        return Err(anyhow!("the serial log does not show the device syscalls succeeding"));
    }
    Ok("translation enabled, device syscalls returned 0, serial log ends with dom0's last line".to_string())
}

/// Boots the capability kernel's entry and dom0, which exits with success only when the kernel gave the
/// statuses it expected. Before the plain boots, so the serial.log they leave is the old kernel's.
async fn check_capability_boot(project: &ProjectHandle, timeout: u64) -> Result<String> {
    let serial = run_boot(project, timeout, &["run", "--capability"]).await?;
    if !first_operation_refused(&serial) {
        return Err(anyhow!("the serial log does not show the first operation refused"));
    }
    if !first_arguments_arrived(&serial) {
        return Err(anyhow!("the serial log does not show the first operation's five arguments in place"));
    }
    Ok("exit status 0, the first operation refused with its five arguments in the serial log".to_string())
}

/// The arguments dom0 passes its first invocation, in rsi, rdx, r8, r9 and r10, as the kernel logs them.
const FIRST_ARGUMENTS: &str = " with [1, 2, 3, 4, 5]: ";

/// Whether the capability kernel's first logged invocation carries dom0's arguments, r10's last.
fn first_arguments_arrived(serial: &str) -> bool {
    serial
        .lines()
        .find(|line| line.contains(CAPABILITY_ENTRY))
        .map_or(false, |line| line.contains(FIRST_ARGUMENTS))
}

/// What the kernel logs for each invocation of its capability entry.
const CAPABILITY_ENTRY: &str = "capability entry: operation ";

/// Whether the capability kernel's first logged invocation is a refusal.
fn first_operation_refused(serial: &str) -> bool {
    serial
        .lines()
        .find(|line| line.contains(CAPABILITY_ENTRY))
        .map_or(false, |line| line.contains(": refused"))
}

/// Runs atmo with `args` and returns the serial log of a boot that reached dom0's last line.
async fn boot(project: &ProjectHandle, timeout: u64, args: &[&str]) -> Result<String> {
    let serial = run_boot(project, timeout, args).await?;
    if !boot_finished(&serial) {
        return Err(anyhow!("the serial log does not end with dom0's last line"));
    }
    if !second_core_idle(&serial) {
        return Err(anyhow!("the serial log does not show CPU 1 idle on a syscall stack of its own"));
    }
    if !second_core_ran_thread(&serial) {
        return Err(anyhow!("the serial log does not show threads making syscalls on both cores"));
    }
    if !serial.contains(SYSCALLS_CONTENDED) {
        return Err(anyhow!("the serial log does not time a syscall with both cores contending"));
    }
    if !serial.contains(FLUSH_ACKNOWLEDGED) {
        return Err(anyhow!("the serial log does not show CPU 1 acknowledging a flush IPI"));
    }
    if !serial.contains(LOCK_CONTENDED) {
        return Err(anyhow!("the serial log does not show both cores contending for the kernel's lock"));
    }
    Ok(serial)
}

/// Runs atmo with `args` and returns the serial log of a run that exited with status 0.
async fn run_boot(project: &ProjectHandle, timeout: u64, args: &[&str]) -> Result<String> {
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
        .args(args)
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

    Ok(String::from_utf8_lossy(&fs::read(&log).await?).into_owned())
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

/// Whether the serial log shows CPU 1 reaching its idle loop, on a different syscall stack from CPU 0.
fn second_core_idle(serial: &str) -> bool {
    match (
        syscall_stack(serial, "CPU 0 syscall stack "),
        syscall_stack(serial, "CPU 1 idle, syscall stack "),
    ) {
        (Some(first), Some(second)) => first != second,
        _ => false,
    }
}

/// What dom0 logs once it has timed a syscall with the other core making the same call.
const SYSCALLS_CONTENDED: &str = "with the other core contending";

/// What the kernel logs once CPU 1 has taken a flush IPI and acknowledged it.
const FLUSH_ACKNOWLEDGED: &str = "flush IPI acknowledged by CPU 1";

/// What the kernel logs once both cores have contended for its lock with the protected pair intact.
const LOCK_CONTENDED: &str = "lock contended by 2 cores: pair intact at 400000";

/// Whether the serial log shows the kernel entering a thread on CPU 1, and dom0's report from each side.
fn second_core_ran_thread(serial: &str) -> bool {
    [
        "CPU 1 entering a thread",
        "CPU 0 entering a thread",
        "thread on CPU 1 made ",
        "thread on CPU 0 made ",
        "a thread blocked with nothing else to run on each core",
    ]
        .iter()
        .all(|line| serial.contains(line))
}

/// The hexadecimal address after `label` in the serial log.
fn syscall_stack(serial: &str, label: &str) -> Option<u64> {
    let digits = serial.split(label).nth(1)?.strip_prefix("0x")?;
    let end = digits.find(|c: char| !c.is_ascii_hexdigit()).unwrap_or(digits.len());
    u64::from_str_radix(&digits[..end], 16).ok()
}

fn iommu_boot_ran(serial: &str) -> bool {
    [
        "Enabling translation",
        "sys_set_device_iommu of dom0's own table: 0",
        "sys_invalidate_iotlb of that device: 0",
    ]
    .iter()
    .all(|line| serial.contains(line))
        && iommu_bound_own_table(serial)
}

/// Whether the table the kernel bound dom0's device to is the one dom0 was told it has.
fn iommu_bound_own_table(serial: &str) -> bool {
    let value = |prefix: &str| -> Option<String> {
        let rest = serial.split(prefix).nth(1)?;
        let hex: String = rest.chars().skip(2).take_while(char::is_ascii_hexdigit).collect();
        (rest.starts_with("0x") && !hex.is_empty()).then_some(hex)
    };
    match (value("the caller's IO table: "), value("IO page table of 0x0:0x1f.0x7: ")) {
        (Some(own), Some(bound)) => own == bound,
        _ => false,
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn a_file_over_the_limit_is_named() {
        let sizes = [("small.rs", MAX_FILE_BYTES), ("solver.profile", MAX_FILE_BYTES + 1)];
        assert_eq!(oversized(&sizes), vec!["solver.profile"]);
        assert!(oversized(&sizes[..1]).is_empty());
    }

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
    fn iommu_boot_needs_translation_and_both_syscalls() {
        let tables = "the caller's IO table: 0x2000\nIO page table of 0x0:0x1f.0x7: 0x2000\n";
        let ran = format!("Enabling translation\nsys_set_device_iommu of dom0's own table: 0\nsys_invalidate_iotlb of that device: 0\n{}", tables);
        assert!(iommu_boot_ran(&ran));
        assert!(!iommu_boot_ran("Enabling translation\nsys_invalidate_iotlb of that device: 0\n"));
        assert!(!iommu_boot_ran("sys_set_device_iommu of dom0's own table: 0\nsys_invalidate_iotlb of that device: 0\n"));
        assert!(!iommu_boot_ran("Enabling translation\nsys_set_device_iommu of dom0's own table: 1\nsys_invalidate_iotlb of that device: 1\n"));
    }

    #[test]
    fn iommu_boot_needs_the_callers_table() {
        assert!(iommu_bound_own_table("the caller's IO table: 0x2000\nIO page table of 0x0:0x1f.0x7: 0x2000\n"));
        assert!(!iommu_bound_own_table("the caller's IO table: 0x2000\nIO page table of 0x0:0x1f.0x7: 0x1000\n"));
        assert!(!iommu_bound_own_table("the caller's IO table: 0x2000\n"));
        assert!(!iommu_bound_own_table("IO page table of 0x0:0x1f.0x7: 0x2000\n"));
    }

    #[test]
    fn first_operation_refused_is_the_first_invocation() {
        let refused = " INFO capability entry: operation 14 on slot 0 with [1, 2, 3, 4, 5]: refused\u{1b}[0m\n";
        let unknown = " INFO capability entry: operation 65535 on slot 0 with [0, 0, 0, 0, 0]: unknown\n";
        assert!(first_operation_refused(&format!("boot\n{}{}", refused, unknown)));
        assert!(!first_operation_refused(&format!("{}{}", unknown, refused)));
        assert!(!first_operation_refused("dom0 benchmark done\n"));
    }

    #[test]
    fn first_arguments_arrived_reads_the_first_invocation() {
        let arrived = " INFO capability entry: operation 14 on slot 0 with [1, 2, 3, 4, 5]: refused\n";
        let dropped = " INFO capability entry: operation 14 on slot 0 with [1, 2, 3, 4, 0]: refused\n";
        let unknown = " INFO capability entry: operation 65535 on slot 0 with [0, 0, 0, 0, 0]: unknown\n";
        assert!(first_arguments_arrived(&format!("boot\n{}{}", arrived, unknown)));
        assert!(!first_arguments_arrived(&format!("{}{}", dropped, unknown)));
        assert!(!first_arguments_arrived(&format!("{}{}", unknown, arrived)));
        assert!(!first_arguments_arrived("dom0 benchmark done\n"));
    }

    #[test]
    fn boot_finishes_on_dom0s_last_line() {
        assert!(boot_finished("x\n\u{1b}[34m INFO dom0 benchmark done\u{1b}[0m\n"));
        assert!(boot_finished("x\r\n INFO dom0 benchmark done\r\n\r\n"));
    }

    #[test]
    fn second_core_idle_on_its_own_stack() {
        let serial = "\u{1b}[34m INFO CPU 0 syscall stack 0x1000\u{1b}[0m\n INFO CPU 1 idle, syscall stack 0x2000\n";
        assert!(second_core_idle(serial));
    }

    #[test]
    fn second_core_sharing_a_stack_is_not_idle() {
        assert!(!second_core_idle("CPU 0 syscall stack 0x1000\nCPU 1 idle, syscall stack 0x1000\n"));
    }

    #[test]
    fn both_cores_reporting_is_a_thread_on_the_second() {
        assert!(second_core_ran_thread(
            "CPU 1 entering a thread\nCPU 0 entering a thread\nthread on CPU 1 made 1000 syscalls\nthread on CPU 0 made 1000 syscalls beside it\na thread blocked with nothing else to run on each core\n"
        ));
    }

    #[test]
    fn dom0_alone_is_not_a_thread_on_the_second() {
        assert!(!second_core_ran_thread("thread on CPU 0 made 1000 syscalls beside it\n"));
    }

    #[test]
    fn no_second_core_is_not_idle() {
        assert!(!second_core_idle("CPU 0 syscall stack 0x1000\n"));
    }

    #[test]
    fn boot_does_not_finish_when_anything_follows() {
        assert!(!boot_finished(" INFO dom0 benchmark done\n INFO CPU 0: Page Fault\n"));
        assert!(!boot_finished(" INFO dom0 benchmark FAILED\n"));
        assert!(!boot_finished(""));
    }
}
