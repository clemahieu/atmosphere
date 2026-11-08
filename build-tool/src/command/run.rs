//! Run the OS in QEMU.

use std::fs::OpenOptions;
use std::path::{Path, PathBuf};
use std::process::ExitCode;

use anyhow::Context;
use clap::Parser;
use tempfile::Builder as TempfileBuilder;
use tokio::fs;

use super::{GlobalOpts, SubCommand};
use crate::emulator::{CpuModel, Emulator, EmulatorExit, GdbServer, Qemu, RunConfiguration};
use crate::error::Result;
use crate::project::{Binary, BuildOptions, Project};

/// Run Atmosphere.
#[derive(Debug, Parser)]
pub struct Opts {
    /// The CPU model to emulate.
    #[clap(long = "cpu")]
    cpu_model: Option<CpuModel>,

    /// Use TCG even if /dev/kvm is writable.
    ///
    /// This only has an effect for QEMU.
    #[clap(long)]
    no_kvm: bool,

    /// Whether to enable IOMMU.
    #[clap(long)]
    iommu: bool,

    /// Whether to enable the early loader.
    #[clap(long, hide = true)]
    loader: bool,

    /// Whether to enable the GDB server.
    #[clap(long)]
    gdb: bool,

    /// The userspace program to pass to dom0.
    #[clap(long, default_value = "hello")]
    payload: String,

    /// Report how long the kernel's lock is held and waited for, in the serial log.
    ///
    /// A build option, since the timing is a real share of a syscall.
    #[clap(long)]
    lock_stats: bool,

    /// Whether to emit full output from the emulator.
    #[clap(long)]
    full_output: bool,

    /// Do not automatically shutdown.
    ///
    /// This will pass `-no-shutdown` to QEMU.
    #[clap(long)]
    no_shutdown: bool,

    /// (Hidden) Kernel file to execute.
    ///
    /// This is used by the Cargo runner.
    #[clap(long, hide = true)]
    cargo_runner: Option<PathBuf>,
}

pub(super) async fn run(global: GlobalOpts) -> Result<()> {
    let local = unwrap_command!(global, SubCommand::Run);

    let project = Project::discover()?;
    log::info!("Project: {:?}", project.root());

    let mut opts = BuildOptions::default();
    opts.release = global.release || local.cargo_runner.is_some();
    opts.verbose = global.verbose;

    let kernel = if let Some(prebuilt) = local.cargo_runner {
        Binary::new(prebuilt)
    } else {
        let kernel_crate = project.kernel();
        let mut kernel_opts = BuildOptions {
            release: opts.release,
            verbose: opts.verbose,
            features: Vec::new(),
        };
        if local.lock_stats {
            kernel_opts.features.push("lock_stats".to_string());
        }
        kernel_crate
            .build(&kernel_opts)
            .await?
            .expect("No binary was produced")
    };

    let loader = project
        .uefi_loader()
        .build(&opts)
        .await?
        .expect("No binary was reproduced for the early loader");

    let dom0 = project
        .dom0()
        .build(&opts)
        .await?
        .expect("No binary was reproduced for Dom0");

    let payload = project
        .user(&local.payload)
        .build(&opts)
        .await?
        .expect("No binary was reproduced for payload");

    let mut run_config = RunConfiguration::new(kernel, loader);
    run_config.use_virtualization(use_kvm(local.no_kvm, Path::new("/dev/kvm")));
    run_config.auto_shutdown(!local.no_shutdown);
    run_config.dom0(dom0);
    run_config.payload(payload);
    run_config.use_iommu(local.iommu);

    if let Some(cpu_model) = local.cpu_model {
        run_config.cpu_model(cpu_model);
    }

    if local.full_output {
        run_config.suppress_initial_outputs(false);
    }

    let run_dir = TempfileBuilder::new().prefix("atmo-run-").tempdir()?;

    // FIXME: Make this configurable
    if local.gdb {
        let gdb_server = {
            let socket_path = run_dir.path().join("gdb.sock").to_owned();
            GdbServer::Unix(socket_path)
        };

        run_config.gdb_server(gdb_server.clone());
        run_config.freeze_on_startup(true);
    }

    // TODO: Bring Bochs back maybe?
    let mut emulator: Box<dyn Emulator> = Box::new(Qemu::new(project.clone(), run_config));

    if let Some(gdb_info) = emulator.gdb_connection_info() {
        // Save connection info to `.gdb`
        let json_path = project.gdb_info_path();
        let json = serde_json::to_vec(&gdb_info)?;

        if json_path.exists() {
            log::warn!("GDB connection info file already exists - Overwriting");
        }

        fs::write(&json_path, json).await?;

        log::warn!("Run `atmo gdb` in another terminal. Execution will be frozen until you continue in the debugger.");
    }

    let ret = emulator.run().await?;

    if local.gdb {
        let json_path = project.gdb_info_path();
        fs::remove_file(&json_path)
            .await
            .with_context(|| "Failed to remove GDB connection info JSON")?;
    }

    match ret {
        EmulatorExit::Code(code) => {
            quit::with_code(code as u8);
        }
        EmulatorExit::Killed => {
            log::error!("The emulator was killed by a signal");
            quit::with_code(ExitCode::FAILURE);
        }
        _ => {}
    }

    drop(run_dir);

    Ok(())
}

/// Whether to pass -enable-kvm: unless told not to, whenever QEMU could open the device.
fn use_kvm(no_kvm: bool, device: &Path) -> bool {
    !no_kvm && OpenOptions::new().read(true).write(true).open(device).is_ok()
}

#[cfg(test)]
mod tests {
    use std::fs::{set_permissions, File, Permissions};
    use std::os::unix::fs::PermissionsExt;

    use tempfile::tempdir;

    use super::*;

    fn device(mode: u32) -> (tempfile::TempDir, PathBuf) {
        let dir = tempdir().unwrap();
        let path = dir.path().join("kvm");
        File::create(&path).unwrap();
        set_permissions(&path, Permissions::from_mode(mode)).unwrap();
        (dir, path)
    }

    #[test]
    fn writable_device_uses_kvm() {
        let (_dir, path) = device(0o666);
        assert!(use_kvm(false, &path));
    }

    #[test]
    fn no_kvm_overrides_a_writable_device() {
        let (_dir, path) = device(0o666);
        assert!(!use_kvm(true, &path));
    }

    #[test]
    fn read_only_device_does_not_use_kvm() {
        let (_dir, path) = device(0o444);
        assert!(!use_kvm(false, &path));
    }

    #[test]
    fn missing_device_does_not_use_kvm() {
        let dir = tempdir().unwrap();
        assert!(!use_kvm(false, &dir.path().join("kvm")));
    }

    #[test]
    fn no_kvm_parses() {
        assert!(Opts::try_parse_from(["run", "--no-kvm"]).unwrap().no_kvm);
    }

    #[test]
    fn kvm_flag_is_gone() {
        assert!(Opts::try_parse_from(["run", "--kvm"]).is_err());
    }
}
