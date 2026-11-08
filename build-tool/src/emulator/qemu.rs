//! QEMU integration.

use std::ffi::OsString;
use std::fs::OpenOptions as SyncOpenOptions;
use std::path::PathBuf;
use std::process::Stdio;

use async_trait::async_trait;
use byte_unit::ByteUnit;
use tempfile::{Builder as TempfileBuilder, NamedTempFile, TempPath};
use tokio::io::{self, BufReader};
use tokio::process::Command;

use super::output_filter::InitialOutputFilter;
use super::{CpuModel, Emulator, EmulatorExit, GdbConnectionInfo, GdbServer, RunConfiguration};
use crate::error::Result;
use crate::grub::BootableImage;
use crate::project::{Binary, ProjectHandle};

/// A QEMU instance.
pub struct Qemu {
    /// The QEMU binary to use.
    qemu_binary: PathBuf,

    /// The run configuration.
    config: RunConfiguration,

    /// I/O port for the isa-debug-exit device.
    debug_exit_io_base: u16,
}

impl Qemu {
    /// Create a QEMU instance.
    pub fn new(_project: ProjectHandle, config: RunConfiguration) -> Self {
        Self {
            qemu_binary: PathBuf::from("qemu-system-x86_64"),
            config,
            debug_exit_io_base: 0xf4,
        }
    }
}

/// The arguments every run shares that depend on the configuration.
fn common_args(memory_mib: usize, debug_exit_io_base: u16, auto_shutdown: bool) -> Vec<String> {
    let mut args: Vec<String> = vec![
        "-smp".into(),
        "2".into(),
        "-m".into(),
        memory_mib.to_string(),
        "-device".into(),
        format!("isa-debug-exit,iobase={:#x},iosize=0x04", debug_exit_io_base),
        "-no-reboot".into(),
    ];
    if !auto_shutdown {
        args.push("-no-shutdown".into());
    }
    args
}

/// QEMU's status when dom0 reports success: isa-debug-exit makes QEMU exit with `code << 1 | 1`,
/// and dom0 writes 0x10. Every other odd status is a failure.
const DOM0_SUCCESS_STATUS: i32 = 33;

/// Interprets QEMU's exit status.
fn exit_from_status(status: Option<i32>) -> EmulatorExit {
    match status {
        Some(0) | Some(DOM0_SUCCESS_STATUS) => EmulatorExit::Success,
        Some(code) => {
            log::error!("QEMU exited with code {}", code);
            EmulatorExit::Code(code)
        }
        None => {
            log::error!("QEMU was killed by a signal");
            EmulatorExit::Killed
        }
    }
}

#[async_trait]
impl Emulator for Qemu {
    /// Start the QEMU process.
    async fn run(&mut self) -> Result<EmulatorExit> {
        let config = &self.config;
        let memory = config.memory.get_adjusted_unit(ByteUnit::MiB).get_value() as usize;

        let command_line = config.full_command_line()
            + &format!(" qemu_debug_exit_io_base={}", self.debug_exit_io_base);
        let suppress_initial_outputs = config.suppress_initial_outputs; // FIXME

        // VFIO passthrough needs root; everything else (including KVM) does not.
        let mut command = if config.pci_dev.is_empty() {
            Command::new(self.qemu_binary.as_os_str())
        } else {
            let mut sudo = Command::new("sudo");
            sudo.arg("-E").arg("--preserve-env=PATH").arg(self.qemu_binary.as_os_str());
            sudo
        };

        let mut initrd = JumboBinary::new()?;
        initrd.push(&config.kernel)?;

        if let Some(dom0) = &config.dom0 {
            initrd.push(dom0)?;
        }

        if let Some(payload) = &config.payload {
            initrd.push(payload)?;
        }

        let initrd = initrd.finalize();

        let iso = if config.use_grub {
            let iso = BootableImage::generate(command_line, Some(&config.loader), Some(&initrd)).await?;
            command.arg("-hda");
            command.arg(iso.iso_path());
            Some(iso)
        } else {
            command.args(&[
                "-kernel",
                config
                    .loader
                    .path()
                    .to_str()
                    .expect("Early loader path contains non-UTF-8"),
            ]);
            command.args(&[
                "-initrd",
                initrd
                    .as_os_str()
                    .to_str()
                    .expect("Kernel path contains non-UTF-8"),
            ]);
            None
        };

        command
            .arg("-nographic")
            .args(&["-serial", "chardev:char0"])
            .args(&["-mon", "chardev=char0"])
            .args(&[
                "-chardev",
                "stdio,id=char0,mux=on,logfile=serial.log,signal=off",
            ])
            .args(common_args(memory, self.debug_exit_io_base, config.auto_shutdown))
            //.args(&["-d", "int"])
            .args(&["-machine", "q35,kernel_irqchip=split"])
            .args(config.cpu_model.to_qemu()?);

        if let Some(img_path) = &config.nvme_img {
            command.args(&["-drive", &format!("file={},if=none,id=nvm", img_path)]);
            command.args(&["-device", "nvme,id=nvm,serial=deadbeef,drive=nvm"]);
        }

        if config.use_iommu {
            // The intel-iommu device must come before vfio-pci, otherwise
            // shadow IOMMU tables won't be configured correctly
            command.args(&["-device", "intel-iommu,intremap=on,aw-bits=48,caching-mode=on"]); // FIXME: AMD

            command.args(&["--trace", "vfio_*"]);
            command.args(&["--trace", "vtd_*"]);
            command.args(&["--trace", "iommufd_*"]);
            command.args(&["-D", "/tmp/qemu-log.txt"]);
        }

        if !config.pci_dev.is_empty() {
            for dev in &config.pci_dev {
                command.args(&["-device", &format!("vfio-pci,host={}", dev)]);
            }
        }

        if config.use_virtualization {
            command.arg("-enable-kvm");
        }

        if suppress_initial_outputs {
            command.stdout(Stdio::piped());
        }

        if config.freeze_on_startup {
            command.arg("-S");
        }

        if let Some(server) = &config.gdb_server {
            command.args(server.to_qemu()?);
        }

        log::error!("Starting QEMU with {:?}", command);

        let mut child = command.spawn()?;

        if suppress_initial_outputs {
            let stdout = {
                let reader = child
                    .stdout
                    .take()
                    .expect("Could not capture emulator stdout");
                BufReader::new(reader)
            };

            let mut filter = InitialOutputFilter::new(stdout);
            tokio::io::copy(&mut filter, &mut io::stdout()).await?;
        }

        let status = child.wait_with_output().await?.status;
        drop(iso);

        Ok(exit_from_status(status.code()))
    }

    /// Returns the GDB connection info for the instance.
    fn gdb_connection_info(&self) -> Option<GdbConnectionInfo> {
        let gdb_server = self.config.gdb_server.as_ref()?;
        let mut gdb_info = GdbConnectionInfo::new(
            self.config.loader.path().to_owned(),
            gdb_server.to_owned(),
        );

        gdb_info.add_binary("kernel".to_string(), self.config.kernel.path().to_owned());

        if let Some(dom0) = &self.config.dom0 {
            gdb_info.add_binary("dom0".to_string(), dom0.path().to_owned());
        }

        Some(gdb_info)
    }
}

trait QemuArgs {
    fn to_qemu(&self) -> Result<Vec<OsString>>;
}

impl QemuArgs for CpuModel {
    fn to_qemu(&self) -> Result<Vec<OsString>> {
        let mut result = vec![];

        result.push("-cpu".to_string().into());

        match self {
            Self::Host => result.push("host".to_string().into()),
            Self::Haswell => result.push("Haswell-IBRS".to_string().into()),
        }

        Ok(result)
    }
}

impl QemuArgs for GdbServer {
    fn to_qemu(&self) -> Result<Vec<OsString>> {
        let mut result: Vec<OsString> = vec!["-gdb".to_string().into()];

        match self {
            GdbServer::Unix(path) => {
                let path = path
                    .to_str()
                    .expect("Socket path contains non-UTF-8 characters");
                result.push(format!("unix:{},server,nowait", path).into());
            }
            GdbServer::Tcp(port) => {
                result.push(format!("tcp::{}", port).into());
            }
        }

        Ok(result)
    }
}

/// A set of binaries.
///
/// Right now it's just a simple concatenantion of them, but
/// in the future it will be more structured.
struct JumboBinary(NamedTempFile);

impl JumboBinary {
    fn new() -> Result<Self> {
        let tmp = TempfileBuilder::new().prefix("atmo-jumbo-").tempfile()?;

        Ok(Self(tmp))
    }

    fn push(&mut self, binary: &Binary) -> Result<()> {
        let mut f = SyncOpenOptions::new()
            .read(true)
            .write(false)
            .open(binary.path())?;

        std::io::copy(&mut f, &mut self.0)?;

        Ok(())
    }

    fn finalize(self) -> TempPath {
        self.0.into_temp_path()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn no_shutdown_count(auto_shutdown: bool) -> usize {
        common_args(1024, 0xf4, auto_shutdown)
            .iter()
            .filter(|arg| arg.as_str() == "-no-shutdown")
            .count()
    }

    /// With -no-shutdown QEMU stays alive after isa-debug-exit, so a run never ends by itself.
    #[test]
    fn auto_shutdown_omits_no_shutdown() {
        assert_eq!(no_shutdown_count(true), 0);
    }

    #[test]
    fn no_auto_shutdown_passes_no_shutdown() {
        assert_eq!(no_shutdown_count(false), 1);
    }

    #[test]
    fn dom0_success_status_is_success() {
        assert!(matches!(exit_from_status(Some(33)), EmulatorExit::Success));
    }

    /// The kernel's failure shutdown writes 0 to the isa-debug-exit port, which is status 1.
    #[test]
    fn kernel_failure_status_is_failure() {
        assert!(matches!(exit_from_status(Some(1)), EmulatorExit::Code(1)));
    }

    /// dom0's bench_fail writes 1, which is status 3.
    #[test]
    fn dom0_failure_status_is_failure() {
        assert!(matches!(exit_from_status(Some(3)), EmulatorExit::Code(3)));
    }

    #[test]
    fn killed_is_failure() {
        assert!(matches!(exit_from_status(None), EmulatorExit::Killed));
    }
}
