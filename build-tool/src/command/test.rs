//! The gate: what makes a commit tested.

use std::io::ErrorKind;
use std::process::{ExitCode, Stdio};

use anyhow::{anyhow, Context};
use cargo_metadata::MetadataCommand;
use clap::Parser;
use tokio::fs;
use tokio::process::Command;

use super::{GlobalOpts, SubCommand};
use crate::error::Result;
use crate::project::{BuildOptions, Project, ProjectHandle};

/// Holds the number of verification errors the gate accepts, relative to the project root.
const VERIFY_ALLOWANCE_PATH: &str = "tools/verify-allowance";

/// Verus over the crates marked for verification, relative to the project root.
const VERIFY: &str = "tools/verify.py";

/// The license check over every package in Cargo.lock, relative to the project root.
const LICENSE_CHECK: &str = "tools/check-licenses.py";

/// The check that every external_body in kernel/verified is listed with its reason, relative to the
/// project root.
const EXTERNAL_BODY_CHECK: &str = "tools/check-external-body.py";

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

/// The payload tools/run.py loads.
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
        ("free ranges", check_free_ranges(&project).await),
        ("mapped runs", check_mapped_runs(&project).await),
        ("license", check_licenses(&project).await),
        ("hooks", check_hooks(&project).await),
        ("verify", check_verify(&project).await),
        ("external body", check_external_body(&project).await),
        ("design index", check_design_index(&project).await),
        ("boot stack", check_boot_stack(&project).await),
        ("coverage", check_coverage(&project).await),
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

    Ok(format!("{} workspace members, then the loader, kernel, dom0 and payload from their own directories", members))
}

/// The loader map check. Its lines start with `free page ranges:` in this step's output.
async fn check_free_ranges(project: &ProjectHandle) -> Result<String> {
    let status = Command::new("cargo")
        .args(["test", "--manifest-path", "build-tool/Cargo.toml", "--", "--nocapture", "free_page"])
        .current_dir(project.root())
        .stdin(Stdio::null())
        .status()
        .await
        .context("free page ranges")?;
    if !status.success() {
        return Err(anyhow!("cargo test free_page: {}", status));
    }
    Ok("unaligned, repeated and out-of-range pages rejected; set-aside pages taken out of the free runs".to_string())
}

/// The dom0 run check. Its lines start with `mapped runs:` in this step's output.
async fn check_mapped_runs(project: &ProjectHandle) -> Result<String> {
    let status = Command::new("cargo")
        .args(["test", "--manifest-path", "build-tool/Cargo.toml", "--", "--nocapture", "mapped_run"])
        .current_dir(project.root())
        .stdin(Stdio::null())
        .status()
        .await
        .context("mapped runs")?;
    if !status.success() {
        return Err(anyhow!("cargo test mapped_run: {}", status));
    }
    Ok("real dom0 load accepted; unaligned, empty, outside, kernel-entry and overlapping runs rejected".to_string())
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

async fn check_hooks(project: &ProjectHandle) -> Result<String> {
    for test in HOOK_TESTS {
        run_check(project, test, &[]).await?;
    }
    Ok("the license guard refuses what it must; the actor hook names the session".to_string())
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

/// Runs Verus through the script and compares the errors on its results lines with the allowance. The
/// script exits non-zero whenever a crate has an error, so its status alone does not decide the check.
async fn check_verify(project: &ProjectHandle) -> Result<String> {
    let root = project.root();
    let path = root.join(VERIFY_ALLOWANCE_PATH);
    let allowance = parse_allowance(&fs::read_to_string(&path).await?)
        .ok_or_else(|| anyhow!("{} does not hold a number", VERIFY_ALLOWANCE_PATH))?;

    let output = Command::new(root.join(VERIFY))
        .current_dir(&root)
        .stdin(Stdio::null())
        .output()
        .await
        .with_context(|| VERIFY.to_string())?;
    let text = String::from_utf8_lossy(&output.stdout) + String::from_utf8_lossy(&output.stderr);
    let counts: Vec<u64> = text.lines().filter_map(parse_verify_errors).collect();
    if counts.is_empty() {
        return Err(anyhow!("{}: {}, no verification results line", VERIFY, output.status));
    }
    let errors: u64 = counts.iter().sum();
    if errors == 0 && !output.status.success() {
        return Err(anyhow!("{}: {} with no errors counted", VERIFY, output.status));
    }

    if errors > allowance {
        return Err(anyhow!("{} errors, allowance {}", errors, allowance));
    }
    Ok(format!("{} errors, allowance {}", errors, allowance))
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
const TRANSLATION_ENABLED: &str = "Enabling translation";

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
const ROOT_UNTYPED_SLOT: usize = 4;
const ROOT_FRAME_SLOT: usize = 129;

/// The root's untyped and frame counts when the serial log prints, in order, one line per fixed slot
/// with its kind: process at 1, thread at 2, console at 3, the untyped from 4 and the frames from 129,
/// as many as the kernel says the root holds, at least one of each.
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
    let mut expected = vec![(1, "process"), (2, "thread"), (3, "console")];
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

/// Runs tools/run.py with `args` and returns the serial log of a boot in which dom0 exited with
/// success, which it does only when the kernel gave the statuses it expected, with what the gate saw
/// of it. The serial log shows the kernel's per-slot lines with their kinds, dom0's check line and
/// exit marker, and CPU 1 idle beside it.
async fn boot(project: &ProjectHandle, timeout: u64, args: &[&str]) -> Result<(String, String)> {
    let serial = run_boot(project, timeout, args).await?;
    if !first_operation_refused(&serial) {
        return Err(anyhow!("the serial log does not show the first operation refused"));
    }
    if !first_arguments_arrived(&serial) {
        return Err(anyhow!("the serial log does not show the first operation's five arguments in place"));
    }
    let (untyped, frames) = fixed_slots_printed(&serial)?;
    if !console_line_printed(&serial) {
        return Err(anyhow!("the serial log does not hold dom0's check line"));
    }
    if !exit_marker_printed(&serial) {
        return Err(anyhow!("the serial log does not show dom0's exit marker"));
    }
    if !second_core_idle(&serial) {
        return Err(anyhow!("the serial log does not show CPU 1 idle on a syscall stack of its own"));
    }
    if !serial.contains(FLUSH_ACKNOWLEDGED) {
        return Err(anyhow!("the serial log does not show CPU 1 acknowledging a flush IPI"));
    }
    if !serial.contains(LOCK_CONTENDED) {
        return Err(anyhow!("the serial log does not show both cores contending for the kernel's lock"));
    }
    let held = format!(
        "exit status 0, the kernel's per-slot lines with their kinds ({} untyped, {} frames), dom0's check \
         line and exit marker, CPU 1 idle on its own stack, a flush IPI acknowledged, the lock contended",
        untyped, frames
    );
    Ok((serial, held))
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
    fn first_operation_refused_is_the_first_invocation() {
        let refused = " INFO capability entry: operation 14 on slot 0 with [1, 2, 3, 4, 5]: refused\u{1b}[0m\n";
        let unknown = " INFO capability entry: operation 65535 on slot 0 with [0, 0, 0, 0, 0]: unknown\n";
        assert!(first_operation_refused(&format!("boot\n{}{}", refused, unknown)));
        assert!(!first_operation_refused(&format!("{}{}", unknown, refused)));
        assert!(!first_operation_refused("dom0 capability done\n"));
    }

    #[test]
    fn first_arguments_arrived_reads_the_first_invocation() {
        let arrived = " INFO capability entry: operation 14 on slot 0 with [1, 2, 3, 4, 5]: refused\n";
        let dropped = " INFO capability entry: operation 14 on slot 0 with [1, 2, 3, 4, 0]: refused\n";
        let unknown = " INFO capability entry: operation 65535 on slot 0 with [0, 0, 0, 0, 0]: unknown\n";
        assert!(first_arguments_arrived(&format!("boot\n{}{}", arrived, unknown)));
        assert!(!first_arguments_arrived(&format!("{}{}", dropped, unknown)));
        assert!(!first_arguments_arrived(&format!("{}{}", unknown, arrived)));
        assert!(!first_arguments_arrived("dom0 capability done\n"));
    }

    #[test]
    fn console_line_is_a_line_of_its_own() {
        assert!(console_line_printed(" INFO root slot 3: console\ndom0 slot checks held\n INFO capability entry\n"));
        assert!(console_line_printed("x\r\ndom0 slot checks held\r\n"));
        assert!(!console_line_printed(" INFO dom0 slot checks held\n"));
        assert!(!console_line_printed("dom0 slot checks\n"));
    }

    /// The kernel's slot lines for a root with two untyped and one frame.
    fn slot_lines(frame_kind: &str) -> String {
        format!(
            " INFO root holds 2 untyped and 1 frames\u{1b}[0m\n INFO root slot 1: process base 0x8000\n INFO root slot 2: thread\n\
             INFO root slot 3: console\n INFO root slot 4: untyped order 9\n\u{1b}[34m INFO root slot 5: untyped\u{1b}[0m\n\
             INFO root slot 129: {} order 0\n",
            frame_kind
        )
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
