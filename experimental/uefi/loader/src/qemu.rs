use std::{ffi::OsStr, path::Path, process::Stdio};

use anyhow::Result;
use command_fds::{tokio::CommandFdAsyncExt, FdMapping};
use std::os::unix::io::AsRawFd;
use tokio::{io::AsyncWriteExt, net::UnixStream};

pub struct Qemu {
    console: UnixStream,
    comms: UnixStream,
    qmp: UnixStream,
    instance: tokio::process::Child,
}

#[derive(Debug)]
pub struct QemuParams<'a> {
    pub binary: &'a Path,
    pub firmware: &'a Path,
    pub app: &'a Path,

    pub console: UnixStream,
    pub comms: UnixStream,
}

impl Qemu {
    pub fn start(params: QemuParams) -> Result<Qemu> {
        let mut cmd = tokio::process::Command::new(params.binary);

        // There should not be any communication over stdin/stdout/stderr, but let's inherit
        // stderr just in case.
        cmd.stdin(Stdio::null());
        cmd.stdout(Stdio::null());
        cmd.stderr(Stdio::inherit());

        // We're keeping the QMP socket to ourselves.
        let qmp = UnixStream::pair()?;

        // Set up the plumbing for communication sockets
        cmd.fd_mappings(vec![
            FdMapping {
                parent_fd: params.console.as_raw_fd(),
                child_fd: 10,
            },
            FdMapping {
                parent_fd: params.comms.as_raw_fd(),
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
            "q35,usb=off,sata=off,smbus=off,graphics=off,vmport=off,smm=off",
        ]);
        // Add the qemu isa-debug-exit device. This can be used to exit qemu with a status
        // code within the VM.
        cmd.args(&["-device", "isa-debug-exit,iobase=0xf4,iosize=0x04"]);
        // First serial port: this will be used by the console (UEFI firmware itself)
        cmd.args(&["-chardev", "socket,id=consock,fd=10"]);
        cmd.args(&["-serial", "chardev:consock"]);
        // Second serial port: for communicating with the UEFI app
        cmd.args(&["-chardev", "socket,id=commsock,fd=11"]);
        cmd.args(&["-serial", "chardev:commsock"]);
        // Expose the QEMU monitor (QMP) over a socket as well.
        cmd.args(&["-chardev", "socket,id=qmpsock,fd=12"]);
        cmd.args(&["-qmp", "chardev:qmpsock"]);
        // Point to the UEFI firmware
        cmd.args(&[OsStr::new("-bios"), params.firmware.as_os_str()]);
        // And finally -- say that the "kernel" is our UEFI app. Although according to docs
        // this is Linux-specific, OVMF seems to be fine with the "kernel" pointing to an UEFI
        // app.
        cmd.args(&[OsStr::new("-kernel"), params.app.as_os_str()]);

        println!("Executing: {:?}", cmd);

        Ok(Qemu {
            instance: cmd.spawn()?,
            console: params.console,
            comms: params.comms,
            qmp: qmp.0,
        })
    }

    pub async fn kill(mut self) -> Result<std::process::ExitStatus> {
        println!("Cleaning up and shutting down.");
        // TODO: tell qemu to stop via QMP instead of just killing it.
        self.console.shutdown().await?;
        self.comms.shutdown().await?;
        self.qmp.shutdown().await?;
        self.instance.kill().await.map_err(anyhow::Error::from)?;
        self.instance.wait().await.map_err(anyhow::Error::from)
    }
}
