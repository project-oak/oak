use std::{ffi::OsStr, path::Path, process::Stdio};

use anyhow::Result;
use command_fds::{tokio::CommandFdAsyncExt, FdMapping};
use std::os::unix::io::AsRawFd;
use tokio::net::UnixStream;

pub struct Qemu {
    // Communication channels.
    pub console: UnixStream,
    pub channel: UnixStream,
    pub qmp: UnixStream,

    instance: tokio::process::Child,
}

impl Qemu {
    pub fn start(binary: &Path, firmware: &Path, app: &Path) -> Result<Qemu> {
        // Create three socket pairs: for (a) console, (b) communication and (c) QMP.
        let console = UnixStream::pair()?;
        let comms = UnixStream::pair()?;
        let qmp = UnixStream::pair()?;

        let mut cmd = tokio::process::Command::new(binary);
        // There should not be any communication over stdin/stdout/stderr, but let's inherit
        // stderr just in case.
        cmd.stdin(Stdio::null());
        cmd.stdout(Stdio::null());
        cmd.stderr(Stdio::inherit());

        // Set up the plumbing for communication sockets
        cmd.fd_mappings(vec![
            FdMapping {
                parent_fd: console.1.as_raw_fd(),
                child_fd: 10,
            },
            FdMapping {
                parent_fd: comms.1.as_raw_fd(),
                child_fd: 11,
            },
            FdMapping {
                parent_fd: qmp.1.as_raw_fd(),
                child_fd: 12,
            },
        ])?;

        // Construct the command-line arguments for `qemu`. See
        // https://www.qemu.org/docs/master/system/invocation.html for all available options.

        // We're going to run qemu as a noninteractive embedded program, so disable any
        // graphical outputs.
        cmd.arg("-nographic");
        // Don't bother with default hardware, such as a VGA adapter, floppy drive, etc.
        cmd.arg("-nodefaults");
        // Use the more modern `q35` machine as the basis.
        // TODO: q35 comes with a ton of stuff we don't need (eg a PC speaker). We should
        // use something simpler (microvm?), if possible.
        cmd.args(&[
            "-machine",
            "q35,usb=off,sata=off,acpi=off,smbus=off,graphics=off,vmport=off,smm=off",
        ]);
        // Add the qemu isa-debug-exit device. This can be used to exit qemu with a status
        // code within the VM.
        cmd.args(&["-device", "isa-debug-exit,iobase=0xf4,iosize=0x04"]);
        // First serial port: this will be used by the console (UEFI firmware itself)
        cmd.args(&[
            "-chardev",
            "socket,id=consock,fd=10,abstract=on,server=on,wait=on",
        ]);
        cmd.args(&["-serial", "chardev:consock"]);
        // Second serial port: for communicating with the UEFI app
        cmd.args(&[
            "-chardev",
            "socket,id=commsock,fd=11,abstract=on,server=on,wait=on",
        ]);
        cmd.args(&["-serial", "chardev:commsock"]);
        // Expose the QEMU monitor (QMP) over a socket as well.
        cmd.args(&[
            "-chardev",
            "socket,id=qmpsock,fd=11,abstract=on,server=on,wait=on",
        ]);
        cmd.args(&["-qmp", "chardev:qmpsock"]);
        // Point to the UEFI firmware
        cmd.args(&[OsStr::new("-bios"), firmware.as_os_str()]);
        // And finally -- say that the "kernel" is our UEFI app. Although according to docs
        // this is Linux-specific, OVMF seems to be fine with the "kernel" pointing to an UEFI
        // app.
        cmd.args(&[OsStr::new("-kernel"), app.as_os_str()]);

        Ok(Qemu {
            console: console.0,
            channel: comms.0,
            qmp: qmp.0,

            instance: cmd.spawn()?,
        })
    }

    pub async fn kill(mut self) -> Result<std::process::ExitStatus> {
        // TODO: tell qemu to stop via QMP instead of just killing it.
        self.instance.kill().await.map_err(anyhow::Error::from)?;
        self.instance.wait().await.map_err(anyhow::Error::from)
    }
}
