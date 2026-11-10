//! The gate: what makes a commit tested.

use std::io::{ErrorKind, Write};
use std::path::Path;
use std::process::{ExitCode, Stdio};
use std::time::{Duration, Instant};

use anyhow::{anyhow, Context};
use clap::Parser;
use tokio::fs;
use tokio::process::Command;

use super::build::Arch;
use super::{GlobalOpts, SubCommand};
use crate::error::Result;
use crate::project::{Project, ProjectHandle};

/// Holds the number of verification errors the gate accepts, relative to the project root.
const VERIFY_ALLOWANCE_PATH: &str = "tools/verify-allowance";

/// Verus over the crates marked for verification, relative to the project root.
const VERIFY: &str = "tools/verify.py";

/// The license check over every package in Cargo.lock, relative to the project root.
const LICENSE_CHECK: &str = "tools/check-licenses.py";

/// The check that every external_body and exec_allows_no_decreases_clause in kernel/verified is listed
/// with its reason and that no assume or admit is left there, relative to the project root.
const EXTERNAL_BODY_CHECK: &str = "tools/check-external-body.py";

/// The check that kernel/verified writes no page size, entries a level or size derived from them as a
/// literal outside the definitions, relative to the project root.
const PAGE_LITERALS_CHECK: &str = "tools/check-page-literals.py";
/// The check that the kernel's sources outside kernel/src/arch name no x86 and hold no inline assembly,
/// relative to the project root.
const ARCH_SOURCES_CHECK: &str = "tools/check-arch-sources.py";
/// The check that each file copied from upstream differs from it only by its record under
/// tools/upstream-copies, relative to the project root.
const UPSTREAM_COPIES_CHECK: &str = "tools/check-upstream-copies.py";

/// The hooks' tests, relative to the project root: the license guard's and the Beads actor's.
const HOOK_TESTS: [&str; 2] = [".claude/hooks/license-guard-test.sh", ".claude/hooks/beads-actor-test.sh"];

/// The boot stack's check, relative to the project root.
const BOOT_STACK_CHECK: &str = "tools/check-boot-stack.py";

/// The coverage report, relative to the project root; `--test` runs its own tests.
const COVERAGE: &str = "tools/coverage.py";

/// The design index builder, relative to the project root; `--check` says whether the index is current.
const DESIGN_INDEX: &str = "tools/build-design-index.py";

/// The largest file the tree may hold. The largest source is a seventh of this, so anything over it is
/// a build or solver output that .gitignore missed.
const MAX_FILE_BYTES: u64 = 1024 * 1024;

/// The boot, relative to the project root; `--test` runs its own tests.
const RUN: &str = "tools/run.py";

/// The gdb attach to a `tools/run.py --gdb` run, relative to the project root; `--test` runs its own
/// tests.
const GDB: &str = "tools/gdb.py";

/// Run the gate.
#[derive(Debug, Parser)]
pub struct Opts {
    /// Seconds dom0 has to boot and finish before the run counts as a hang.
    #[clap(long, default_value_t = 120)]
    boot_timeout: u64,

    /// Run one target's steps only: aarch64 is its verify and its boot on the Orange Pi, and x86_64 is
    /// every other step. Without it the gate runs both.
    #[clap(long, value_enum)]
    target: Option<Arch>,
}

/// A step of the gate, in the order the gate runs them.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum Step {
    FileSizes,
    Build,
    BuildToolTests,
    License,
    Hooks,
    Verify,
    VerifyAarch64,
    ExternalBody,
    PageLiterals,
    ArchSources,
    UpstreamCopies,
    DesignIndex,
    BootStack,
    Coverage,
    IommuBoot,
    Boot,
    Aarch64Boot,
}

impl Step {
    const ALL: [Step; 17] = [
        Step::FileSizes,
        Step::Build,
        Step::BuildToolTests,
        Step::License,
        Step::Hooks,
        Step::Verify,
        Step::VerifyAarch64,
        Step::ExternalBody,
        Step::PageLiterals,
        Step::ArchSources,
        Step::UpstreamCopies,
        Step::DesignIndex,
        Step::BootStack,
        Step::Coverage,
        Step::IommuBoot,
        Step::Boot,
        Step::Aarch64Boot,
    ];

    fn name(self) -> &'static str {
        match self {
            Step::FileSizes => "file sizes",
            Step::Build => "build",
            Step::BuildToolTests => "build-tool tests",
            Step::License => "license",
            Step::Hooks => "hooks",
            Step::Verify => "verify",
            Step::VerifyAarch64 => "verify aarch64",
            Step::ExternalBody => "external body",
            Step::PageLiterals => "page literals",
            Step::ArchSources => "arch sources",
            Step::UpstreamCopies => "upstream copies",
            Step::DesignIndex => "design index",
            Step::BootStack => "boot stack",
            Step::Coverage => "coverage",
            Step::IommuBoot => "iommu boot",
            Step::Boot => "boot",
            Step::Aarch64Boot => "aarch64 boot",
        }
    }

    /// The target the step belongs to. The steps that check the tree as a whole run with x86_64's,
    /// since the workstation that runs them is the x86_64 host.
    fn target(self) -> Arch {
        match self {
            Step::VerifyAarch64 | Step::Aarch64Boot => Arch::Aarch64,
            _ => Arch::X86_64,
        }
    }

    async fn run(self, project: &ProjectHandle, timeout: u64) -> Result<String> {
        match self {
            Step::FileSizes => check_file_sizes(project).await,
            Step::Build => check_build(project).await,
            Step::BuildToolTests => check_build_tool_tests(project).await,
            Step::License => check_licenses(project).await,
            Step::Hooks => check_hooks(project).await,
            Step::Verify => {
                run_check(project, VERIFY, &["--test"]).await?;
                check_verify(project, &[]).await
            }
            Step::VerifyAarch64 => check_verify(project, &["--target", "aarch64"]).await,
            Step::ExternalBody => check_external_body(project).await,
            Step::PageLiterals => check_page_literals(project).await,
            Step::ArchSources => check_arch_sources(project).await,
            Step::UpstreamCopies => check_upstream_copies(project).await,
            Step::DesignIndex => check_design_index(project).await,
            Step::BootStack => check_boot_stack(project).await,
            Step::Coverage => check_coverage(project).await,
            Step::IommuBoot => check_iommu_boot(project, timeout).await,
            Step::Boot => check_boot(project, timeout).await,
            Step::Aarch64Boot => super::board::gate_boot(project, timeout).await,
        }
    }
}

/// The steps the gate runs for `target`, or for both targets.
fn steps(target: Option<Arch>) -> Vec<Step> {
    Step::ALL.into_iter().filter(|step| target.is_none_or(|target| step.target() == target)).collect()
}

pub(super) async fn run(global: GlobalOpts) -> Result<()> {
    let local = unwrap_command!(global, SubCommand::Test);
    let project = Project::discover()?;

    let gate = Instant::now();
    let mut results = Vec::new();
    for step in steps(local.target) {
        let start = Instant::now();
        let result = step.run(&project, local.boot_timeout).await;
        results.push((step.name(), result, start.elapsed()));
    }
    let total = gate.elapsed();

    println!();
    for (name, result, elapsed) in &results {
        println!("{}", step_line(name, result, *elapsed));
    }
    println!("{}", total_line(total));

    if results.iter().any(|(_, result, _)| result.is_err()) {
        quit::with_code(ExitCode::FAILURE);
    }
    Ok(())
}

/// A step's result line, with its wall time, so a log shows what each step costs.
fn step_line(name: &str, result: &Result<String>, elapsed: Duration) -> String {
    let seconds = elapsed.as_secs_f64();
    match result {
        Ok(detail) => format!("gate {}: ok in {:.1} s: {}", name, seconds, detail),
        Err(error) => format!("gate {}: FAIL in {:.1} s: {:#}", name, seconds, error),
    }
}

/// The gate's last line: its wall time from the first step's start to the last step's end.
fn total_line(elapsed: Duration) -> String {
    format!("gate total: {:.1} s", elapsed.as_secs_f64())
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
    super::build::gate_build(project).await
}

/// build-tool's whole test suite, after the build, since the dom0 run check reads the built dom0. Its
/// tests include the loader map check, whose lines start with `free page ranges:`, and the dom0 run
/// check, whose lines start with `mapped runs:`.
/// The detail carries each test binary's result line.
async fn check_build_tool_tests(project: &ProjectHandle) -> Result<String> {
    let output = Command::new("cargo")
        .args(["test", "--manifest-path", "build-tool/Cargo.toml", "--", "--nocapture"])
        .current_dir(project.root())
        .stdin(Stdio::null())
        .stderr(Stdio::inherit())
        .output()
        .await
        .context("build-tool tests")?;
    let text = String::from_utf8_lossy(&output.stdout);
    print!("{}", text);
    let results = marked_lines(&text, TEST_RESULT);
    if !output.status.success() {
        return Err(anyhow!("cargo test of build-tool: {}{}", output.status, results));
    }
    if results.is_empty() {
        return Err(anyhow!("cargo test of build-tool: no test result line"));
    }
    Ok(format!("loader map and dom0 run checks among them{}", results))
}

/// Runs the license check's own tests, then the check over the workspace's graph.
async fn check_licenses(project: &ProjectHandle) -> Result<String> {
    run_check(project, LICENSE_CHECK, &["--test"]).await?;
    let output = check_output(project, LICENSE_CHECK).await?;
    Ok(output.trim_end().to_string())
}

/// Runs the external_body check's own tests, then the check over every crate marked verified.
async fn check_external_body(project: &ProjectHandle) -> Result<String> {
    run_check(project, EXTERNAL_BODY_CHECK, &["--test"]).await?;
    let output = check_output(project, EXTERNAL_BODY_CHECK).await?;
    Ok(output.trim_end().to_string())
}

/// Runs the page literal check's own tests, then the check over every crate marked verified.
async fn check_page_literals(project: &ProjectHandle) -> Result<String> {
    run_check(project, PAGE_LITERALS_CHECK, &["--test"]).await?;
    let output = check_output(project, PAGE_LITERALS_CHECK).await?;
    Ok(output.trim_end().to_string())
}

/// Runs the arch sources check's own tests, then the check over the kernel's shared sources.
async fn check_arch_sources(project: &ProjectHandle) -> Result<String> {
    run_check(project, ARCH_SOURCES_CHECK, &["--test"]).await?;
    let output = check_output(project, ARCH_SOURCES_CHECK).await?;
    Ok(output.trim_end().to_string())
}

/// Runs the upstream copies check's own tests, then the check over its records.
async fn check_upstream_copies(project: &ProjectHandle) -> Result<String> {
    run_check(project, UPSTREAM_COPIES_CHECK, &["--test"]).await?;
    let output = check_output(project, UPSTREAM_COPIES_CHECK).await?;
    Ok(output.trim_end().to_string())
}

async fn check_hooks(project: &ProjectHandle) -> Result<String> {
    for test in HOOK_TESTS {
        run_check(project, test, &[]).await?;
    }
    Ok("the license guard refuses what it must; the actor hook names the session".to_string())
}

async fn check_boot_stack(project: &ProjectHandle) -> Result<String> {
    // Each profile's overflow builds come first, so the images left behind are the normal ones.
    let runs: [&[&str]; 7] = [
        &["--test"],
        &["debug", "overflow"],
        &["debug", "syscall-overflow"],
        &["debug"],
        &["release", "overflow"],
        &["release", "syscall-overflow"],
        &["release"],
    ];
    for args in runs {
        run_check(project, BOOT_STACK_CHECK, args).await?;
    }
    Ok("its own tests, then debug and release, normal, boot stack overflow and syscall stack overflow".to_string())
}

/// `design/INDEX.md` is generated from the records, so a record edited without regenerating it would leave
/// the index saying something the records do not.
async fn check_design_index(project: &ProjectHandle) -> Result<String> {
    run_check(project, DESIGN_INDEX, &["--check"]).await?;
    Ok("design/INDEX.md is current".to_string())
}

/// Reports coverage per crate after the script's own tests pass. A low number does not fail the gate:
/// only a capture that fails does.
async fn check_coverage(project: &ProjectHandle) -> Result<String> {
    run_check(project, COVERAGE, &["--test"]).await?;
    let report = check_output(project, COVERAGE).await?;
    Ok(format!("\n  {}", report.trim_end().replace('\n', "\n  ")))
}

/// Runs a check from the tree, at the project root, and returns what it printed to stdout; its stderr
/// goes to the gate's own.
async fn check_output(project: &ProjectHandle, program: &str) -> Result<String> {
    let root = project.root();
    let output = Command::new(root.join(program))
        .current_dir(&root)
        .stdin(Stdio::null())
        .stderr(Stdio::inherit())
        .output()
        .await
        .with_context(|| program.to_string())?;
    if !output.status.success() {
        return Err(anyhow!("{}: {}", program, output.status));
    }
    Ok(String::from_utf8_lossy(&output.stdout).into_owned())
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

/// Runs Verus through the script for one target, the host's with no arguments or the one `--target`
/// names, and compares the errors on its results lines with the allowance, which holds for each target
/// alone. The script exits non-zero whenever a crate has an error, so its status alone does not decide
/// the check. The detail carries the results lines, so the gate log shows each crate's counts.
async fn check_verify(project: &ProjectHandle, args: &[&str]) -> Result<String> {
    let root = project.root();
    let path = root.join(VERIFY_ALLOWANCE_PATH);
    let allowance = parse_allowance(&fs::read_to_string(&path).await?)
        .ok_or_else(|| anyhow!("{} does not hold a number", VERIFY_ALLOWANCE_PATH))?;

    let command = [VERIFY].iter().chain(args).copied().collect::<Vec<_>>().join(" ");
    let output = Command::new(root.join(VERIFY))
        .args(args)
        .current_dir(&root)
        .stdin(Stdio::null())
        .output()
        .await
        .with_context(|| VERIFY.to_string())?;
    let text = String::from_utf8_lossy(&output.stdout) + String::from_utf8_lossy(&output.stderr);
    let counts: Vec<u64> = text.lines().filter_map(parse_verify_errors).collect();
    if counts.is_empty() {
        let last = text.lines().last().unwrap_or_default();
        return Err(anyhow!("{}: {}, no verification results line: {}", command, output.status, last));
    }
    let errors: u64 = counts.iter().sum();
    if errors == 0 && !output.status.success() {
        return Err(anyhow!("{}: {} with no errors counted", command, output.status));
    }

    let results = marked_lines(&text, VERIFY_RESULTS);
    if errors > allowance {
        return Err(anyhow!("{}: {} errors, allowance {}{}", command, errors, allowance, results));
    }
    Ok(format!("{} errors, allowance {}{}", errors, allowance, results))
}

async fn check_boot(project: &ProjectHandle, timeout: u64) -> Result<String> {
    run_check(project, RUN, &["--test"]).await?;
    run_check(project, GDB, &["--test"]).await?;
    let held = boot(project, timeout, &[]).await?;
    Ok(format!("tools/run.py's and tools/gdb.py's tests pass; {}", held))
}

/// Boots with an IOMMU present, which the kernel enables translation on. The plain boot comes after
/// it, so the serial.log it leaves has no IOMMU.
async fn check_iommu_boot(project: &ProjectHandle, timeout: u64) -> Result<String> {
    boot(project, timeout, &["--iommu"]).await
}

/// Runs tools/run.py with `args` and returns what the gate saw of a boot in which dom0 exited with
/// success, which it does only when the kernel gave the statuses it expected, and whose serial log
/// passes the boot log check, with the IOMMU's translation enabled under `--iommu`.
async fn boot(project: &ProjectHandle, timeout: u64, args: &[&str]) -> Result<String> {
    let serial = run_boot(project, timeout, args).await?;
    boot_log_accepted(&project.root(), &serial, Arch::X86_64, args.contains(&"--iommu"))
}

/// The boot log check, relative to the project root.
const BOOT_LOG_CHECK: &str = "tools/check-boot-log.py";

/// Holds a dom0 boot's serial log on `arch` to the boot log check, with the IOMMU's translation
/// enabled under `translation`, and returns what held or the check that failed.
pub(super) fn boot_log_accepted(root: &Path, serial: &str, arch: Arch, translation: bool) -> Result<String> {
    let mut check = std::process::Command::new(root.join(BOOT_LOG_CHECK));
    check.args(["--arch", &arch.to_string()]);
    if translation {
        check.arg("--translation");
    }
    let mut child = check
        .arg("-")
        .current_dir(root)
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .stderr(Stdio::inherit())
        .spawn()
        .with_context(|| BOOT_LOG_CHECK.to_string())?;
    child.stdin.take().expect("stdin is piped").write_all(serial.as_bytes())?;
    let output = child.wait_with_output()?;
    let said = String::from_utf8_lossy(&output.stdout).trim_end().to_string();
    match output.status.code() {
        Some(0) => Ok(said),
        Some(1) => Err(anyhow!("{}", said)),
        _ => Err(anyhow!("{}: {}", BOOT_LOG_CHECK, output.status)),
    }
}

/// Runs tools/run.py with `args` and returns the serial log of a run that exited with status 0.
async fn run_boot(project: &ProjectHandle, timeout: u64, args: &[&str]) -> Result<String> {
    let root = project.root();
    let log = root.join("serial.log");
    match fs::remove_file(&log).await {
        Err(error) if error.kind() != ErrorKind::NotFound => return Err(error.into()),
        _ => {}
    }

    // timeout signals its whole process group, which takes QEMU down with the script.
    let status = Command::new("timeout")
        .arg(timeout.to_string())
        .arg(root.join(RUN))
        .args(args)
        .current_dir(&root)
        .stdin(Stdio::null())
        .status()
        .await?;

    if status.code() == Some(124) {
        return Err(anyhow!("no exit within {} s", timeout));
    }
    if !status.success() {
        return Err(anyhow!("{}: {}", RUN, status));
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

/// Marks Verus's results line, one per crate.
const VERIFY_RESULTS: &str = "verification results:: ";

/// Marks cargo test's result line, one per test binary.
const TEST_RESULT: &str = "test result: ";

/// The lines of a run's output that hold `marker`, each on a line of its own.
fn marked_lines(output: &str, marker: &str) -> String {
    output
        .lines()
        .filter(|line| line.contains(marker))
        .map(|line| format!("\n  {}", line.trim()))
        .collect()
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_runs_both_targets_unless_one_is_named() {
        let target = |args: &[&str]| match GlobalOpts::try_parse_from(args).unwrap().cmd {
            SubCommand::Test(local) => local.target,
            other => panic!("not test: {other:?}"),
        };
        assert_eq!(target(&["atmo", "test"]), None);
        assert_eq!(target(&["atmo", "test", "--target", "aarch64"]), Some(Arch::Aarch64));
        assert_eq!(target(&["atmo", "test", "--target", "x86_64"]), Some(Arch::X86_64));
    }

    #[test]
    fn the_aarch64_target_is_its_verify_and_the_board_boot() {
        assert_eq!(steps(Some(Arch::Aarch64)), vec![Step::VerifyAarch64, Step::Aarch64Boot]);
        let x86_64 = steps(Some(Arch::X86_64));
        assert!(x86_64.contains(&Step::Boot) && x86_64.contains(&Step::Verify));
        assert!(x86_64.contains(&Step::PageLiterals) && x86_64.contains(&Step::ArchSources));
        assert!(!x86_64.contains(&Step::VerifyAarch64) && !x86_64.contains(&Step::Aarch64Boot));
        let both = steps(None);
        assert_eq!(both.len(), x86_64.len() + 2);
        assert_eq!(both.last(), Some(&Step::Aarch64Boot));
    }

    /// Each step's line names its wall time in seconds, whether it passed or failed, and the last line
    /// names the whole gate's.
    #[test]
    fn each_step_line_carries_its_wall_time() {
        let passed = Ok("0 errors, allowance 0".to_string());
        assert_eq!(
            step_line("verify", &passed, Duration::from_millis(212_449)),
            "gate verify: ok in 212.4 s: 0 errors, allowance 0"
        );
        let failed = Err(anyhow!("no exit within 120 s"));
        assert_eq!(step_line("boot", &failed, Duration::from_millis(120_051)), "gate boot: FAIL in 120.1 s: no exit within 120 s");
        assert_eq!(step_line("hooks", &passed, Duration::ZERO), "gate hooks: ok in 0.0 s: 0 errors, allowance 0");
        assert_eq!(total_line(Duration::from_millis(431_960)), "gate total: 432.0 s");
    }

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
    fn verify_results_lines_are_each_crates_line() {
        let output = "warning: x\nverification results:: 1345 verified, 0 errors\nnote: y\nverification results:: 5 verified, 0 errors\n";
        assert_eq!(
            marked_lines(output, VERIFY_RESULTS),
            "\n  verification results:: 1345 verified, 0 errors\n  verification results:: 5 verified, 0 errors"
        );
    }

    /// cargo test prints one result line per test binary, so each one reaches the gate log's detail.
    #[test]
    fn test_result_lines_are_each_binarys_line() {
        let output = "running 2 tests\ntest a ... ok\nfree page ranges: rejected x\ntest result: ok. 2 passed; 0 failed\n\nrunning 0 tests\ntest result: ok. 0 passed; 0 failed\n";
        assert_eq!(
            marked_lines(output, TEST_RESULT),
            "\n  test result: ok. 2 passed; 0 failed\n  test result: ok. 0 passed; 0 failed"
        );
    }

    #[test]
    fn no_results_line_is_not_zero_errors() {
        assert_eq!(parse_verify_errors("error: cannot find macro\n"), None);
    }
}
