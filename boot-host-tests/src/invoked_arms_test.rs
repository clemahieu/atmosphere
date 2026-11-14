// SPDX-License-Identifier: MIT

//! tools/check-invoked-arms.py on fixtures. The gate's workspace tests run these; the script is not
//! itself a gate step. design/invoked-arm-is-the-operation-postcondition/.

use std::fs;
use std::path::PathBuf;
use std::process::Command;

fn script() -> PathBuf {
    PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("../tools/check-invoked-arms.py")
}

fn run(root: &std::path::Path) -> (i32, String, String) {
    let output = Command::new("python3")
        .arg(script())
        .arg("--root")
        .arg(root)
        .output()
        .expect("run check-invoked-arms.py");
    let code = output.status.code().expect("script exit status");
    let stdout = String::from_utf8(output.stdout).expect("stdout");
    let stderr = String::from_utf8(output.stderr).expect("stderr");
    (code, stdout, stderr)
}

/// A tree whose arms call the predicates the ensures call, including the shapes the record skips.
fn carried() -> String {
    "\
impl CapKernel {
    pub open spec fn spec_retyped(pre: Self, post: Self) -> bool {
        post == pre && Self::frame_retyped(pre, post) && pre.can_retype_frame(root) && Self::kept(pre, post)
    }
    pub open spec fn spec_outcome(&self) -> Outcome {
        self.holds_console(root)
    }
    pub open spec fn invoked(pre: Self, post: Self) -> bool {
        match spec_operation(frame.operation_number()) {
            Some(Operation::Retype) => Self::spec_retyped(pre, post),
            _ => post == pre && out == pre.spec_outcome(),
        }
    }
    pub fn dispatch(&mut self) -> (ret: Option<Outcome>) {
        match operation(frame.operation_number()) {
            Some(Operation::Retype) => Some(self.invoke_retype()),
            Some(Operation::Print) => Some(self.print()),
            Some(_) => Some(status_only_outcome(STATUS_REFUSED)),
            None => Some(status_only_outcome(STATUS_UNKNOWN)),
        }
    }
    fn invoke_retype(&mut self) -> (ret: Outcome)
        ensures
            final(self).not_the_operation == old(self).not_the_operation,
    {
        self.retype_frame()
    }
    pub fn retype_frame(&mut self) -> (ret: bool)
        ensures
            final(steps).count <= old(steps).count + 1,
            final(self).wf(),
            old(self).wf(),
            *final(self) == *old(self),
            ret ==> Self::frame_retyped(old(self), final(self), root),
            ret == old(self).can_retype_frame(root),
            !(ret is Refused) ==> #[trigger] Self::kept(old(self), final(self)),
    {
        self.helper()
    }
    pub fn helper(&mut self) -> (ret: bool)
        ensures
            final(self).helper_field == old(self).helper_field,
    {
    }
    pub fn print(&mut self) -> (ret: bool)
        ensures
            final(steps).count <= old(steps).count + 1,
            *final(self) == *old(self),
            ret == self.holds_console(root),
    {
    }
    pub fn destroy(&mut self) -> (ret: bool)
        ensures
            final(self).destroyed == old(self).destroyed,
    {
    }
}
"
    .to_string()
}

#[test]
fn a_fixture_that_meets_the_rule_exits_0() {
    let dir = std::env::temp_dir().join(format!("invoked-arms-meets-{}", std::process::id()));
    let _ = fs::remove_dir_all(&dir);
    fs::create_dir_all(&dir).unwrap();
    fs::write(dir.join("op.rs"), carried()).unwrap();
    let (code, stdout, stderr) = run(&dir);
    let _ = fs::remove_dir_all(&dir);
    assert_eq!(code, 0, "stdout:\n{stdout}\nstderr:\n{stderr}");
    assert_eq!(stdout, "");
}

#[test]
fn a_dropped_field_comparison_is_named() {
    let dir = std::env::temp_dir().join(format!("invoked-arms-drops-{}", std::process::id()));
    let _ = fs::remove_dir_all(&dir);
    fs::create_dir_all(&dir).unwrap();
    let source = carried().replace(
        "            final(self).wf(),\n",
        "            final(self).wf(),\n            final(self).flush_epoch == old(self).flush_epoch,\n",
    );
    fs::write(dir.join("op.rs"), source).unwrap();
    let (code, stdout, stderr) = run(&dir);
    let _ = fs::remove_dir_all(&dir);
    assert_ne!(code, 0, "stdout:\n{stdout}\nstderr:\n{stderr}");
    assert_eq!(
        stdout,
        "op.rs:retype_frame:final(self).flush_epoch == old(self).flush_epoch\n",
        "stderr:\n{stderr}"
    );
}

#[test]
fn the_verified_sources_parse() {
    let output = Command::new("python3").arg(script()).output().expect("run check-invoked-arms.py");
    let code = output.status.code().expect("script exit status");
    let stdout = String::from_utf8(output.stdout).expect("stdout");
    let stderr = String::from_utf8(output.stderr).expect("stderr");
    assert!(code == 0 || code == 1, "code {code}\n{stderr}\n{stdout}");
    assert!(stderr.is_empty(), "{stderr}");
    for line in stdout.lines() {
        let mut parts = line.splitn(3, ':');
        let path = parts.next().expect(line);
        let function = parts.next().expect(line);
        let conjunct = parts.next().expect(line);
        assert!(path.ends_with(".rs") && !function.is_empty() && !conjunct.is_empty(), "{line}");
    }
}
