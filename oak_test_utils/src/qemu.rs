//
// Copyright 2026 The Project Oak Authors
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
//     http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.
//

//! Utilities for booting QEMU virtual machines and capturing guest-physical
//! memory dumps via QMP.

use std::{
    io::{BufRead, BufReader, Write},
    os::{fd::AsRawFd, unix::net::UnixStream},
    path::PathBuf,
    process::{Command, Stdio},
    sync::{
        atomic::{AtomicU32, Ordering},
        mpsc,
    },
    thread,
    time::{Duration, Instant},
};

use anyhow::Context;
use command_fds::CommandFdExt;
use sha2::{Digest, Sha256};

use crate::core::Core;

/// Monotonic counter used to give each guest boot within a test process a
/// distinct socket and dump-file name, so concurrently running tests in the
/// same binary do not clash.
static BOOT_SEQ: AtomicU32 = AtomicU32::new(0);

/// Structure holding the memory dump and standard output lines captured during
/// a QEMU guest run.
pub struct QemuDump {
    /// Parsed ELF core dump of guest physical memory.
    pub core: Core,
    /// Lines received on the guest's serial console (stdout) before the ready
    /// marker.
    pub stdout_lines: Vec<String>,
}

impl QemuDump {
    /// Returns the stripped rest of the first stdout line that starts with
    /// `prefix`.
    pub fn line_matching(&self, prefix: &str) -> Option<&str> {
        self.stdout_lines.iter().find_map(|line| line.trim().strip_prefix(prefix))
    }

    /// Finds a line starting with `prefix` followed by a hex string, and
    /// decodes it into a fixed-size `N`-byte array.
    pub fn parse_line_hex<const N: usize>(&self, prefix: &str) -> Option<[u8; N]> {
        let hex_str = self.line_matching(prefix)?;
        let mut bytes = [0u8; N];
        hex::decode_to_slice(hex_str, &mut bytes).ok()?;
        Some(bytes)
    }
}

/// Helper wrapper to implement oak_channel::Channel for UnixStream.
struct SocketChannel(UnixStream);

impl oak_channel::Write for SocketChannel {
    fn write_all(&mut self, data: &[u8]) -> anyhow::Result<()> {
        std::io::Write::write_all(&mut self.0, data).map_err(anyhow::Error::msg)
    }

    fn flush(&mut self) -> anyhow::Result<()> {
        std::io::Write::flush(&mut self.0).map_err(anyhow::Error::msg)
    }
}

impl oak_channel::Read for SocketChannel {
    fn read_exact(&mut self, data: &mut [u8]) -> anyhow::Result<()> {
        std::io::Read::read_exact(&mut self.0, data).map_err(anyhow::Error::msg)
    }
}

/// Builder for configuring and executing a QEMU instance for memory-dump
/// testing.
pub struct QemuBuilder {
    kernel: PathBuf,
    bios: Option<PathBuf>,
    initrd: Option<PathBuf>,
    app_binary: Option<PathBuf>,
    machine: String,
    memory: Option<String>,
    extra_args: Vec<String>,
    timeout: Duration,
}

impl QemuBuilder {
    /// Creates a new builder with the path to the kernel binary.
    pub fn new(kernel: impl Into<PathBuf>) -> Self {
        Self {
            kernel: kernel.into(),
            bios: None,
            initrd: None,
            app_binary: None,
            machine: "microvm".to_string(),
            memory: None,
            extra_args: Vec::new(),
            timeout: Duration::from_secs(120),
        }
    }

    /// Sets the BIOS / firmware image (e.g. Stage 0 binary).
    pub fn bios(mut self, bios: impl Into<PathBuf>) -> Self {
        self.bios = Some(bios.into());
        self
    }

    /// Sets the initrd / ramdisk image (e.g. orchestrator or test application).
    pub fn initrd(mut self, initrd: impl Into<PathBuf>) -> Self {
        self.initrd = Some(initrd.into());
        self
    }

    /// Sets the application binary to be passed to the orchestrator via the
    /// communication channel.
    pub fn app_binary(mut self, app_binary: impl Into<PathBuf>) -> Self {
        self.app_binary = Some(app_binary.into());
        self
    }

    /// Sets the QEMU machine type (defaults to `"microvm"`).
    pub fn machine(mut self, machine: impl Into<String>) -> Self {
        self.machine = machine.into();
        self
    }

    /// Sets the guest memory size (e.g. `"512M"`).
    pub fn memory(mut self, memory: impl Into<String>) -> Self {
        self.memory = Some(memory.into());
        self
    }

    /// Appends extra CLI arguments to the QEMU command.
    pub fn extra_args(mut self, args: impl IntoIterator<Item = impl Into<String>>) -> Self {
        self.extra_args.extend(args.into_iter().map(Into::into));
        self
    }

    /// Sets the maximum duration to wait for the guest to reach `ready_marker`.
    pub fn timeout(mut self, timeout: Duration) -> Self {
        self.timeout = timeout;
        self
    }

    /// Boots QEMU, waits until `ready_marker` is observed on stdout, captures a
    /// full guest physical memory dump as an ELF core file, and parses it
    /// into a [`QemuDump`].
    pub fn boot_and_dump(self, ready_marker: &str) -> anyhow::Result<QemuDump> {
        let (raw, stdout_lines) = self.boot_and_dump_raw(ready_marker)?;
        let core = Core::parse(raw)?;
        Ok(QemuDump { core, stdout_lines })
    }

    /// Boots QEMU and returns the raw memory dump bytes along with captured
    /// stdout lines.
    pub fn boot_and_dump_raw(self, ready_marker: &str) -> anyhow::Result<(Box<[u8]>, Vec<String>)> {
        let test_tmpdir = std::env::var("TEST_TMPDIR")
            .unwrap_or_else(|_| std::env::temp_dir().to_string_lossy().to_string());
        let seq = BOOT_SEQ.fetch_add(1, Ordering::Relaxed);

        // Unix socket paths are length-limited (~108 bytes on Linux), so keep the QMP
        // socket under `/tmp` with a short, unique name derived from a hash of
        // `test_tmpdir`.
        let mut hasher = Sha256::new();
        hasher.update(test_tmpdir.as_bytes());
        let tmpdir_hash: String =
            hasher.finalize()[..8].iter().map(|b| format!("{b:02x}")).collect();
        let unique = format!("oak_qemu_dump_{tmpdir_hash}_{seq}");
        let qmp_path = PathBuf::from(format!("/tmp/{unique}.qmp"));
        let dump_path = PathBuf::from(&test_tmpdir).join(format!("{unique}.elf"));
        let _ = std::fs::remove_file(&qmp_path);
        let _ = std::fs::remove_file(&dump_path);

        let qemu_bin = which::which("qemu-system-x86_64")
            .map_err(|e| anyhow::anyhow!("finding qemu-system-x86_64: {e}"))?;
        let mut cmd = Command::new(qemu_bin);
        cmd.args(["-cpu", "host"]);
        cmd.arg("-enable-kvm");
        cmd.args(["-display", "none"]);
        cmd.args(["-nographic"]);
        cmd.args(["-nodefaults"]);
        cmd.args(["-no-reboot"]);
        cmd.args(["-serial", "stdio"]);
        cmd.args(["-qmp", &format!("unix:{},server,nowait", qmp_path.display())]);
        cmd.args(["-kernel", self.kernel.to_str().context("invalid kernel path")?]);
        if let Some(ref bios) = self.bios {
            cmd.args(["-bios", bios.to_str().context("invalid bios path")?]);
        }
        if let Some(ref initrd) = self.initrd {
            cmd.args(["-initrd", initrd.to_str().context("invalid initrd path")?]);
        }
        cmd.args(["-machine", &self.machine]);
        if let Some(ref memory) = self.memory {
            cmd.args(["-m", memory]);
        }
        cmd.args(&self.extra_args);

        let comm_channel = if self.app_binary.is_some() {
            let (guest_socket, host_socket) = UnixStream::pair()?;
            let guest_socket_fd = guest_socket.as_raw_fd();
            cmd.preserved_fds(vec![guest_socket.into()]);
            cmd.args(["-chardev", format!("socket,id=commsock,fd={guest_socket_fd}").as_str()]);
            cmd.args(["-global", "virtio-mmio.force-legacy=false"]);
            cmd.args(["-device", "virtio-serial-device,max_ports=1"]);
            cmd.args(["-device", "virtconsole,chardev=commsock"]);
            Some(host_socket)
        } else {
            None
        };

        cmd.stdin(Stdio::null());
        cmd.stdout(Stdio::piped());
        cmd.stderr(Stdio::inherit());

        let mut child = cmd.spawn().map_err(|e| anyhow::anyhow!("spawning qemu: {e}"))?;

        if let Some(ref app_path) = self.app_binary {
            let host_socket = comm_channel.unwrap();
            host_socket.set_read_timeout(Some(Duration::from_secs(30)))?;
            let app_bytes = std::fs::read(app_path)
                .with_context(|| format!("failed to read app binary {}", app_path.display()))?;
            let initial_data = oak_proto_rust::oak::restricted_kernel::InitialData {
                application_bytes: app_bytes,
                endorsement_bytes: Vec::new(),
            };
            let mut initial_data_bytes =
                oak_restricted_kernel_interface::initial_data::INITIAL_DATA_V1_HEADER.to_vec();
            prost::Message::encode(&initial_data, &mut initial_data_bytes)
                .context("failed to encode initial data")?;
            let mut channel = SocketChannel(host_socket);
            oak_channel::basic_framed::send_raw(&mut channel, &initial_data_bytes)
                .context("failed to send initial data to guest")?;
            let _evidence = oak_channel::basic_framed::receive_raw(&mut channel)
                .context("failed to receive attestation evidence from orchestrator")?;
        }

        let stdout = child.stdout.take().context("qemu stdout should be piped")?;
        let (tx, rx) = mpsc::channel();
        let ready_marker_owned = ready_marker.to_string();
        let reader = thread::spawn(move || {
            let mut reader = BufReader::new(stdout);
            let mut line = String::new();
            loop {
                line.clear();
                match reader.read_line(&mut line) {
                    Ok(0) | Err(_) => break,
                    Ok(_) => {
                        let is_marker = line.contains(&ready_marker_owned);
                        let _ = tx.send(line.clone());
                        if is_marker {
                            break;
                        }
                    }
                }
            }
        });

        let dump_result = (|| -> anyhow::Result<(Box<[u8]>, Vec<String>)> {
            let deadline = Instant::now() + self.timeout;
            let mut ready = false;
            let mut stdout_lines = Vec::new();

            while Instant::now() < deadline {
                match rx.recv_timeout(Duration::from_secs(1)) {
                    Ok(line) => {
                        let is_ready = line.contains(ready_marker);
                        stdout_lines.push(line);
                        if is_ready {
                            ready = true;
                            break;
                        }
                    }
                    Err(mpsc::RecvTimeoutError::Timeout) => continue,
                    Err(mpsc::RecvTimeoutError::Disconnected) => break,
                }
            }

            if !ready {
                return Err(anyhow::anyhow!(
                    "guest did not reach the ready marker '{ready_marker}' within timeout"
                ));
            }

            // Connect to the QMP socket.
            let connect_deadline = Instant::now() + Duration::from_secs(10);
            let mut writer = loop {
                match UnixStream::connect(&qmp_path) {
                    Ok(stream) => break stream,
                    Err(_) if Instant::now() < connect_deadline => {
                        thread::sleep(Duration::from_millis(50));
                    }
                    Err(e) => return Err(anyhow::anyhow!("connecting to QMP socket: {e}")),
                }
            };
            let mut qmp_reader = BufReader::new(writer.try_clone()?);
            qmp_reader.get_ref().set_read_timeout(Some(Duration::from_secs(120)))?;

            // Enter command mode, then dump all of guest memory to `dump_path`.
            qmp_transact(&mut qmp_reader, &mut writer, r#"{"execute":"qmp_capabilities"}"#)?;
            let dump_cmd = format!(
                r#"{{"execute":"dump-guest-memory","arguments":{{"paging":false,"protocol":"file:{}"}}}}"#,
                dump_path.display()
            );
            qmp_transact(&mut qmp_reader, &mut writer, &dump_cmd)?;

            let raw = std::fs::read(&dump_path)?.into_boxed_slice();
            Ok((raw, stdout_lines))
        })();

        let _ = child.kill();
        let _ = child.wait();
        let _ = reader.join();
        let _ = std::fs::remove_file(&qmp_path);
        let _ = std::fs::remove_file(&dump_path);

        dump_result
    }
}

/// Convenience helper to boot QEMU and dump guest memory.
pub fn boot_and_dump_guest_memory(
    kernel: impl Into<PathBuf>,
    bios: Option<PathBuf>,
    initrd: Option<PathBuf>,
    ready_marker: &str,
) -> anyhow::Result<QemuDump> {
    let mut builder = QemuBuilder::new(kernel);
    if let Some(bios) = bios {
        builder = builder.bios(bios);
    }
    if let Some(initrd) = initrd {
        builder = builder.initrd(initrd);
    }
    builder.boot_and_dump(ready_marker)
}

/// Sends a single QMP command and waits for its reply.
fn qmp_transact(
    reader: &mut BufReader<UnixStream>,
    writer: &mut UnixStream,
    command: &str,
) -> anyhow::Result<()> {
    writeln!(writer, "{command}")?;
    writer.flush()?;
    loop {
        let mut line = String::new();
        if reader.read_line(&mut line)? == 0 {
            return Err(anyhow::anyhow!("qmp connection closed unexpectedly"));
        }
        if line.contains("\"return\"") {
            return Ok(());
        }
        if line.contains("\"error\"") {
            return Err(anyhow::anyhow!("qmp command failed: {}", line.trim()));
        }
    }
}
