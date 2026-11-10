//! The gate: what makes a commit tested.

use std::io::ErrorKind;
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
/// literal outside the definitions and the files its allowance lists, relative to the project root.
const PAGE_LITERALS_CHECK: &str = "tools/check-page-literals.py";

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
    DesignIndex,
    BootStack,
    Coverage,
    IommuBoot,
    Boot,
    Aarch64Boot,
}

impl Step {
    const ALL: [Step; 15] = [
        Step::FileSizes,
        Step::Build,
        Step::BuildToolTests,
        Step::License,
        Step::Hooks,
        Step::Verify,
        Step::VerifyAarch64,
        Step::ExternalBody,
        Step::PageLiterals,
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
/// tests include the loader map check, whose lines start with `free page ranges:`, the dom0 run check,
/// whose lines start with `mapped runs:`, and the check that the kernel's shared sources name no x86.
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
    Ok(format!("loader map, dom0 run and shared-source checks among them{}", results))
}

/// Runs the license check's own tests, then the check over the workspace's graph.
async fn check_licenses(project: &ProjectHandle) -> Result<String> {
    run_check(project, LICENSE_CHECK, &["--test"]).await?;
    let output = check_output(project, LICENSE_CHECK).await?;
    Ok(output.trim_end().to_string())
}

/// Runs the external_body check's own tests, then the check over kernel/verified.
async fn check_external_body(project: &ProjectHandle) -> Result<String> {
    run_check(project, EXTERNAL_BODY_CHECK, &["--test"]).await?;
    let output = check_output(project, EXTERNAL_BODY_CHECK).await?;
    Ok(output.trim_end().to_string())
}

/// Runs the page literal check's own tests, then the check over kernel/verified.
async fn check_page_literals(project: &ProjectHandle) -> Result<String> {
    run_check(project, PAGE_LITERALS_CHECK, &["--test"]).await?;
    let output = check_output(project, PAGE_LITERALS_CHECK).await?;
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
    let (_, held) = boot(project, timeout, &[]).await?;
    Ok(format!("tools/run.py's and tools/gdb.py's tests pass; {}", held))
}

/// Boots with an IOMMU present, which the kernel enables translation on. The plain boot comes after
/// it, so the serial.log it leaves has no IOMMU.
async fn check_iommu_boot(project: &ProjectHandle, timeout: u64) -> Result<String> {
    let (serial, held) = boot(project, timeout, &["--iommu"]).await?;
    if !serial.contains(TRANSLATION_ENABLED) {
        return Err(anyhow!("the serial log does not show the IOMMU's translation enabled"));
    }
    Ok(format!("translation enabled; {}", held))
}

/// What the kernel logs when it turns on the IOMMU's translation.
pub(super) const TRANSLATION_ENABLED: &str = "Enabling translation";

/// The line dom0 prints through its console when every fixed-slot check held.
const CONSOLE_LINE: &str = "dom0 slot checks held";

/// The line dom0 prints after that check line, and only then exits with success.
const EXIT_MARKER: &str = "dom0 capability done";

/// Whether the serial log holds dom0's exit marker as a line of its own.
fn exit_marker_printed(serial: &str) -> bool {
    serial.lines().any(|line| line.trim_end_matches('\r') == EXIT_MARKER)
}

/// Whether the serial log holds dom0's console line as a line of its own.
fn console_line_printed(serial: &str) -> bool {
    serial.lines().any(|line| line.trim_end_matches('\r') == CONSOLE_LINE)
}

/// What the kernel logs of the root's untyped and frame capabilities, before it prints each slot.
const ROOT_HOLDS: &str = "root holds ";

/// What the kernel logs for each fixed slot of the root's table, followed by the slot and its kind.
const ROOT_SLOT: &str = "root slot ";

/// The first untyped and frame slots of the root's table, design/root-process-at-boot/.
const ROOT_UNTYPED_SLOT: usize = 5;
const ROOT_FRAME_SLOT: usize = 129;

/// The root's untyped and frame counts when the serial log prints, in order, one line per fixed slot
/// with its kind: process at 1, thread at 2, console at 3, power at 4, the untyped from 5 and the
/// frames from 129, as many as the kernel says the root holds, at least one of each.
fn fixed_slots_printed(serial: &str) -> Result<(usize, usize)> {
    let holds = serial
        .lines()
        .find_map(|line| line.find(ROOT_HOLDS).map(|at| &line[at + ROOT_HOLDS.len()..]))
        .ok_or_else(|| anyhow!("the serial log does not say what the root holds"))?;
    let words: Vec<&str> = holds.split(|c: char| !c.is_ascii_alphanumeric()).filter(|word| !word.is_empty()).collect();
    let (untyped, frames) = match words.as_slice() {
        [untyped, "untyped", "and", frames, "frames", ..] => (untyped.parse::<usize>(), frames.parse::<usize>()),
        _ => return Err(anyhow!("the root's holdings are not counted: {}", holds)),
    };
    let (untyped, frames) = match (untyped, frames) {
        (Ok(untyped), Ok(frames)) if untyped > 0 && frames > 0 => (untyped, frames),
        _ => return Err(anyhow!("the root holds no untyped or no frames: {}", holds)),
    };
    let mut expected = vec![(1, "process"), (2, "thread"), (3, "console"), (4, "power")];
    expected.extend((0..untyped).map(|k| (ROOT_UNTYPED_SLOT + k, "untyped")));
    expected.extend((0..frames).map(|k| (ROOT_FRAME_SLOT + k, "frame")));
    let printed: Vec<(usize, &str)> = serial
        .lines()
        .filter_map(|line| line.find(ROOT_SLOT).map(|at| &line[at + ROOT_SLOT.len()..]))
        .map(|slot| {
            let (index, rest) = slot.split_once(':').unwrap_or((slot, ""));
            (index.parse().unwrap_or(0), rest.trim_start().split(|c: char| !c.is_ascii_alphabetic()).next().unwrap_or(""))
        })
        .collect();
    match printed.iter().zip(&expected).position(|(printed, expected)| printed != expected) {
        Some(at) => Err(anyhow!("root slot {} prints as {:?}, not {}", expected[at].0, printed[at].1, expected[at].1)),
        None if printed.len() != expected.len() => Err(anyhow!(
            "the serial log prints {} of the root's slots, not {}",
            printed.len(),
            expected.len()
        )),
        None => Ok((untyped, frames)),
    }
}

/// The base of the 1G region the test guest leaves wholly free. The loader allocates in the first GiB
/// of RAM and the firmware above the second, and RAM starts at 0 on the PC and at 1 GiB on QEMU virt:
/// design/test-guest-memory/.
fn free_gigabyte(arch: Arch) -> u64 {
    match arch {
        Arch::X86_64 => 0x4000_0000,
        Arch::Aarch64 => 0x8000_0000,
    }
}

/// Whether the serial log shows the root holding the 1G region at `base` as one untyped, a 1G block.
fn gigabyte_untyped_printed(serial: &str, base: u64) -> bool {
    // What follows the slot number on the kernel's line for that untyped, up to its rights.
    let untyped = format!(": untyped base {:#x} order 18 ", base);
    serial
        .lines()
        .filter_map(|line| line.find(ROOT_SLOT).map(|at| &line[at + ROOT_SLOT.len()..]))
        .any(|slot| slot.trim_start_matches(|c: char| c.is_ascii_digit()).starts_with(&untyped))
}

/// Runs tools/run.py with `args` and returns the serial log of a boot in which dom0 exited with
/// success, which it does only when the kernel gave the statuses it expected, with what the gate saw
/// of it. The serial log shows the kernel's per-slot lines with their kinds, the 1G untyped among
/// them, dom0's check line and exit marker, and CPU 1 idle beside it.
async fn boot(project: &ProjectHandle, timeout: u64, args: &[&str]) -> Result<(String, String)> {
    let serial = run_boot(project, timeout, args).await?;
    let held = boot_serial_accepted(&serial, Arch::X86_64)?;
    Ok((serial, held))
}

/// The lines the serial log of a successful boot on `arch` must show.
pub(super) fn boot_serial_accepted(serial: &str, arch: Arch) -> Result<String> {
    let (untyped, frames) = fixed_slots_printed(serial)?;
    let base = free_gigabyte(arch);
    let gigabyte = format!("{} to {} GiB as one 1G untyped", base >> 30, (base >> 30) + 1);
    if !gigabyte_untyped_printed(serial, base) {
        return Err(anyhow!("the serial log does not show the root holding {}", gigabyte));
    }
    if !console_line_printed(serial) {
        return Err(anyhow!("the serial log does not hold dom0's check line"));
    }
    if !exit_marker_printed(serial) {
        return Err(anyhow!("the serial log does not show dom0's exit marker"));
    }
    if !second_core_idle(serial) {
        return Err(anyhow!("the serial log does not show CPU 1 idle on a syscall stack of its own"));
    }
    if !serial.contains(FLUSH_ACKNOWLEDGED) {
        return Err(anyhow!("the serial log does not show CPU 1 acknowledging a flush IPI"));
    }
    if !serial.contains(LOCK_CONTENDED) {
        return Err(anyhow!("the serial log does not show both cores contending for the kernel's lock"));
    }
    Ok(format!(
        "exit status 0, the kernel's per-slot lines with their kinds ({} untyped, {} frames), {}, dom0's \
         check line and exit marker, CPU 1 idle on its own stack, a flush IPI acknowledged, the lock \
         contended",
        untyped, frames, gigabyte
    ))
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

/// What the kernel logs once CPU 1 has taken a flush IPI and acknowledged it.
const FLUSH_ACKNOWLEDGED: &str = "flush IPI acknowledged by CPU 1";

/// What the kernel logs once both cores have contended for its lock with the protected pair intact.
const LOCK_CONTENDED: &str = "lock contended by 2 cores: pair intact at 400000";

/// The hexadecimal address after `label` in the serial log.
fn syscall_stack(serial: &str, label: &str) -> Option<u64> {
    let digits = serial.split(label).nth(1)?.strip_prefix("0x")?;
    let end = digits.find(|c: char| !c.is_ascii_hexdigit()).unwrap_or(digits.len());
    u64::from_str_radix(&digits[..end], 16).ok()
}

#[cfg(test)]
pub(super) mod tests {
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
        assert!(x86_64.contains(&Step::PageLiterals));
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

    /// A boot log with the lines the gate keeps, and no capability-entry line.
    pub(in crate::command) fn boot_log() -> String {
        format!(
            "{}\
             dom0 slot checks held\n\
             dom0 capability done\n\
             \u{1b}[34m INFO CPU 0 syscall stack 0x1000\u{1b}[0m\n\
             INFO CPU 1 idle, syscall stack 0x2000\n\
             flush IPI acknowledged by CPU 1\n\
             lock contended by 2 cores: pair intact at 400000\n",
            slot_lines("frame")
        )
    }

    #[test]
    fn a_boot_without_a_capability_entry_line_passes() {
        let log = boot_log();
        assert!(!log.contains("capability entry"));
        assert!(boot_serial_accepted(&log, Arch::X86_64).unwrap().contains("1 to 2 GiB as one 1G untyped"));

        let no_console = log.replace("dom0 slot checks held\n", "");
        assert!(boot_serial_accepted(&no_console, Arch::X86_64).unwrap_err().to_string().contains("check line"));

        let no_exit = log.replace("dom0 capability done\n", "");
        assert!(boot_serial_accepted(&no_exit, Arch::X86_64).unwrap_err().to_string().contains("exit marker"));

        let no_slot = log.replace(" INFO root slot 2: thread\n", "");
        assert!(boot_serial_accepted(&no_slot, Arch::X86_64).is_err());

        let no_power = log.replace(" INFO root slot 4: power base 0x2000000001000 order 0 rights 0x0\n", "");
        assert!(boot_serial_accepted(&no_power, Arch::X86_64).unwrap_err().to_string().contains("root slot 4"));

        let console_twice = log.replace("root slot 4: power", "root slot 4: console");
        assert!(boot_serial_accepted(&console_twice, Arch::X86_64).unwrap_err().to_string().contains("not power"));

        let no_gigabyte = log.replace("base 0x40000000 order 18", "base 0x40000000 order 17");
        assert!(boot_serial_accepted(&no_gigabyte, Arch::X86_64).unwrap_err().to_string().contains("1G untyped"));

        // QEMU virt's RAM starts at 1 GiB, so there the block is 2 to 3 GiB and the PC's does not count.
        let virt = log.replace("base 0x40000000 order 18", "base 0x80000000 order 18");
        assert!(boot_serial_accepted(&virt, Arch::Aarch64).unwrap().contains("2 to 3 GiB as one 1G untyped"));
        assert!(boot_serial_accepted(&virt, Arch::X86_64).unwrap_err().to_string().contains("1 to 2 GiB as one 1G untyped"));
        assert!(boot_serial_accepted(&log, Arch::Aarch64).unwrap_err().to_string().contains("2 to 3 GiB as one 1G untyped"));

        let no_idle = log.replace("CPU 1 idle, syscall stack 0x2000\n", "");
        assert!(boot_serial_accepted(&no_idle, Arch::X86_64).unwrap_err().to_string().contains("CPU 1 idle"));

        let no_flush = log.replace("flush IPI acknowledged by CPU 1\n", "");
        assert!(boot_serial_accepted(&no_flush, Arch::X86_64).unwrap_err().to_string().contains("flush IPI"));

        let no_lock = log.replace("lock contended by 2 cores: pair intact at 400000\n", "");
        assert!(boot_serial_accepted(&no_lock, Arch::X86_64).unwrap_err().to_string().contains("contending"));
    }

    #[test]
    fn console_line_is_a_line_of_its_own() {
        assert!(console_line_printed(" INFO root slot 3: console\ndom0 slot checks held\n INFO root slot 4: power\n"));
        assert!(console_line_printed("x\r\ndom0 slot checks held\r\n"));
        assert!(!console_line_printed(" INFO dom0 slot checks held\n"));
        assert!(!console_line_printed("dom0 slot checks\n"));
    }

    /// The kernel's slot lines for a root with two untyped and one frame.
    fn slot_lines(frame_kind: &str) -> String {
        format!(
            " INFO root holds 2 untyped and 1 frames\u{1b}[0m\n INFO root slot 1: process base 0x8000\n INFO root slot 2: thread\n\
             INFO root slot 3: console\n INFO root slot 4: power base 0x2000000001000 order 0 rights 0x0\n\
             INFO root slot 5: untyped base 0x40000000 order 18 rights 0x8\n\
             \u{1b}[34m INFO root slot 6: untyped\u{1b}[0m\n\
             INFO root slot 129: {} order 0\n",
            frame_kind
        )
    }

    #[test]
    fn the_free_gigabyte_is_one_untyped() {
        let pc = free_gigabyte(Arch::X86_64);
        assert_eq!(pc, 0x4000_0000);
        assert!(gigabyte_untyped_printed(&slot_lines("frame"), pc));
        assert!(gigabyte_untyped_printed(" INFO root slot 9: untyped base 0x40000000 order 18 rights 0x8\u{1b}[0m\r\n", pc));
        // Another kind, another base, another order, and a base or an order this one is a prefix of.
        assert!(!gigabyte_untyped_printed(" INFO root slot 129: frame base 0x40000000 order 18 rights 0x8\n", pc));
        assert!(!gigabyte_untyped_printed(" INFO root slot 5: untyped base 0x0 order 18 rights 0x8\n", pc));
        assert!(!gigabyte_untyped_printed(" INFO root slot 5: untyped base 0x40000000 order 9 rights 0x8\n", pc));
        assert!(!gigabyte_untyped_printed(" INFO root slot 5: untyped base 0x400000000 order 18 rights 0x8\n", pc));
        assert!(!gigabyte_untyped_printed(" INFO root slot 5: untyped base 0x40000000 order 180 rights 0x8\n", pc));
        assert!(!gigabyte_untyped_printed(" INFO root holds 2 untyped and 1 frames\n", pc));

        // The kernel's line for QEMU virt's block, where RAM starts at 1 GiB.
        let virt = free_gigabyte(Arch::Aarch64);
        assert_eq!(virt, 0x8000_0000);
        assert!(gigabyte_untyped_printed(" INFO root slot 5: untyped base 0x80000000 order 18 rights 0x8\n", virt));
        assert!(!gigabyte_untyped_printed(" INFO root slot 5: untyped base 0x80000000 order 16 rights 0x8\n", virt));
        assert!(!gigabyte_untyped_printed(&slot_lines("frame"), virt));
    }

    #[test]
    fn a_log_missing_the_exit_marker_does_not_pass() {
        let slots = slot_lines("frame");
        assert!(fixed_slots_printed(&slots).is_ok());
        assert!(!exit_marker_printed(&slots));
        assert!(exit_marker_printed(&format!("{slots}dom0 capability done\n")));
        assert!(exit_marker_printed("x\r\ndom0 capability done\r\n"));
        assert!(!exit_marker_printed(" INFO dom0 capability done\n"));
    }

    #[test]
    fn a_log_with_a_wrong_slot_kind_does_not_pass() {
        assert!(fixed_slots_printed(&slot_lines("page")).is_err());
        assert_eq!(fixed_slots_printed(&slot_lines("frame")).unwrap(), (2, 1));
    }

    #[test]
    fn fixed_slots_are_each_printed_with_their_kind() {
        assert_eq!(fixed_slots_printed(&slot_lines("frame")).unwrap(), (2, 1));
        assert!(fixed_slots_printed(&slot_lines("untyped")).is_err());
        let missing = slot_lines("frame").replace(" INFO root slot 2: thread\n", "");
        assert!(fixed_slots_printed(&missing).is_err());
        let extra = format!("{} INFO root slot 130: frame\n", slot_lines("frame"));
        assert!(fixed_slots_printed(&extra).is_err());
        let empty = slot_lines("frame").replace("holds 2 untyped", "holds 0 untyped");
        assert!(fixed_slots_printed(&empty).is_err());
        assert!(fixed_slots_printed(" INFO root slot 1: process\n").is_err());
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
    fn no_second_core_is_not_idle() {
        assert!(!second_core_idle("CPU 0 syscall stack 0x1000\n"));
    }
}
