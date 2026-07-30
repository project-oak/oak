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

//! Integration tests that verify how stage0 handles its DICE signing keys in
//! guest memory before handing control to the next stage.
//!
//! The stage0 DICE flow uses two ECA signing keys:
//!
//! * the **root** key, used only to sign the layer-1 certificate. It is never
//!   handed onward and must be erased entirely from guest memory.
//! * the **layer-1** (stage1) key, generated randomly and intentionally handed
//!   to the next stage inside the reserved DICE region (the `Stage0DiceData`
//!   struct and the serialized proto). The next stage knows to zero this region
//!   out, so this key is expected to exist *only* within that region.
//!
//! Each test boots stage0 together with a halting test kernel (the
//! `test_kernel` built with the `keep_alive` feature), then dumps the guest's
//! physical memory via the QEMU monitor `dump-guest-memory` command:
//!
//! * [`assert_root_key_erased`] asserts the (fixed-seed, test-only) root key is
//!   absent everywhere.
//! * [`assert_layer1_key_confined`] recovers the random layer-1 key from the
//!   handoff structure and asserts every copy of it lies within the reserved
//!   DICE region.

use std::{
    io::{self, BufRead, BufReader, Write},
    ops::Range,
    os::unix::net::UnixStream,
    path::PathBuf,
    process::{Command, Stdio},
    sync::{
        atomic::{AtomicU32, Ordering},
        mpsc,
    },
    thread,
    time::{Duration, Instant},
};

use goblin::elf::{Elf, ProgramHeader, program_header::PT_LOAD};
use googletest::prelude::*;
use oak_dice::evidence::Stage0DiceData;
use oak_file_utils::data_path;
use sha2::{Digest, Sha256};

/// Marker printed by the halting test kernel once stage0 has handed control to
/// the kernel. See `test_kernel.rs`.
const BOOT_MARKER: &str = "boot successful";

/// Monotonic counter used to give each guest boot within this test process a
/// distinct socket and dump-file name, so concurrently running tests in the
/// same binary do not clash.
static BOOT_SEQ: AtomicU32 = AtomicU32::new(0);

/// Boots stage0 together with the test kernel and, once the kernel is running,
/// captures a full dump of the guest's physical memory as the raw bytes of an
/// ELF core file. Parse the result with [`Core::parse`] to inspect it.
fn boot_and_dump_guest_memory() -> Result<Box<[u8]>> {
    let kernel = data_path("oak_restricted_kernel_wrapper/stage0_dump_test_kernel_bin");
    let bios = data_path("stage0_bin/insecure_stage0_bin_fixed_key");

    let test_tmpdir =
        std::env::var("TEST_TMPDIR").expect("TEST_TMPDIR should be set by the Bazel test runner");
    let seq = BOOT_SEQ.fetch_add(1, Ordering::Relaxed);

    // Unix socket paths are length-limited (~108 bytes on Linux), and the Bazel
    // test tmpdir can be long, so keep the QMP socket under `/tmp` with a short,
    // unique name derived from a hash of `TEST_TMPDIR`. The (unbounded-length)
    // dump file can live in the test tmpdir itself.
    // See https://bazel.build/reference/test-encyclopedia#test-interaction-filesystem for guidance on this exact scenario.
    let mut hasher = Sha256::new();
    hasher.update(test_tmpdir.as_bytes());
    let tmpdir_hash: String = hasher.finalize()[..8].iter().map(|b| format!("{b:02x}")).collect();
    let unique = format!("oak_stage0_dump_{tmpdir_hash}_{seq}");
    let qmp_path = PathBuf::from(format!("/tmp/{unique}.qmp"));
    let dump_path = PathBuf::from(&test_tmpdir).join(format!("{unique}.elf"));
    let _ = std::fs::remove_file(&qmp_path);
    let _ = std::fs::remove_file(&dump_path);

    let mut cmd = Command::new(which::which("qemu-system-x86_64")?);
    cmd.args(["-cpu", "host"]);
    cmd.arg("-enable-kvm");
    cmd.args(["-display", "none"]);
    cmd.arg("-nographic");
    cmd.arg("-nodefaults");
    cmd.arg("-no-reboot");
    cmd.args(["-serial", "stdio"]);
    cmd.args(["-qmp", &format!("unix:{},server,nowait", qmp_path.display())]);
    cmd.args(["-kernel", kernel.to_str().unwrap()]);
    cmd.args(["-bios", bios.to_str().unwrap()]);
    cmd.args(["-machine", "microvm"]);
    cmd.stdin(Stdio::null());
    cmd.stdout(Stdio::piped());
    cmd.stderr(Stdio::inherit());

    let mut child = cmd.spawn()?;

    // Read the serial console on a background thread so we can wait for the boot
    // marker with a timeout rather than blocking forever if the guest hangs.
    let stdout = child.stdout.take().expect("qemu stdout should be piped");
    let (tx, rx) = mpsc::channel();
    let reader = thread::spawn(move || {
        let mut reader = BufReader::new(stdout);
        let mut line = String::new();
        loop {
            line.clear();
            match reader.read_line(&mut line) {
                Ok(0) | Err(_) => break,
                Ok(_) => {
                    let is_marker = line.contains(BOOT_MARKER);
                    let _ = tx.send(line.clone());
                    if is_marker {
                        break;
                    }
                }
            }
        }
    });

    let dump_result = (|| -> Result<Box<[u8]>> {
        // Wait for the kernel to signal that stage0 has handed over control.
        let deadline = Instant::now() + Duration::from_secs(120);
        let mut booted = false;
        while Instant::now() < deadline {
            match rx.recv_timeout(Duration::from_secs(1)) {
                Ok(line) if line.contains(BOOT_MARKER) => {
                    booted = true;
                    break;
                }
                Ok(_) => continue,
                Err(mpsc::RecvTimeoutError::Timeout) => continue,
                Err(mpsc::RecvTimeoutError::Disconnected) => break,
            }
        }
        if !booted {
            return Err(io::Error::other("guest did not reach the boot marker").into());
        }

        // Connect to the QMP socket (QEMU may take a moment to create it).
        let connect_deadline = Instant::now() + Duration::from_secs(10);
        let mut writer = loop {
            match UnixStream::connect(&qmp_path) {
                Ok(stream) => break stream,
                Err(_) if Instant::now() < connect_deadline => {
                    thread::sleep(Duration::from_millis(50));
                }
                Err(e) => return Err(e.into()),
            }
        };
        let mut qmp_reader = BufReader::new(writer.try_clone()?);
        qmp_reader.get_ref().set_read_timeout(Some(Duration::from_secs(120)))?;

        // Enter command mode, then dump all of guest memory to `dump_path`.
        // `paging: false` dumps guest-physical memory (no guest page-table walk).
        qmp_transact(&mut qmp_reader, &mut writer, r#"{"execute":"qmp_capabilities"}"#)?;
        let dump_cmd = format!(
            r#"{{"execute":"dump-guest-memory","arguments":{{"paging":false,"protocol":"file:{}"}}}}"#,
            dump_path.display()
        );
        qmp_transact(&mut qmp_reader, &mut writer, &dump_cmd)?;

        Ok(std::fs::read(&dump_path)?.into_boxed_slice())
    })();

    // Always tear down the guest and reader thread, and clean up temp files.
    let _ = child.kill();
    let _ = child.wait();
    let _ = reader.join();
    let _ = std::fs::remove_file(&qmp_path);
    let _ = std::fs::remove_file(&dump_path);

    dump_result
}

/// Sends a single QMP command and waits for its reply, skipping the QMP
/// greeting and any asynchronous events. See the QMP specification:
/// <https://www.qemu.org/docs/master/interop/qmp-spec.html>
fn qmp_transact(
    reader: &mut BufReader<UnixStream>,
    writer: &mut UnixStream,
    command: &str,
) -> Result<()> {
    writeln!(writer, "{command}")?;
    writer.flush()?;
    loop {
        let mut line = String::new();
        if reader.read_line(&mut line)? == 0 {
            return Err(io::Error::other("qmp connection closed unexpectedly").into());
        }
        if line.contains("\"return\"") {
            return Ok(());
        }
        if line.contains("\"error\"") {
            return Err(io::Error::other(format!("qmp command failed: {}", line.trim())).into());
        }
        // Otherwise this is the greeting or an asynchronous event: keep
        // reading.
    }
}

/// A parsed QEMU guest-memory ELF core dump, providing access to the guest's
/// physical memory.
struct Core {
    /// Raw bytes of the ELF core dump file.
    raw: Box<[u8]>,
    /// Program headers parsed from `raw`, describing the guest-memory mappings.
    program_headers: Vec<ProgramHeader>,
}

impl Core {
    /// Parses the raw bytes of a QEMU guest-memory ELF core dump.
    fn parse(raw: Box<[u8]>) -> Result<Self> {
        let program_headers = Elf::parse(&raw)?.program_headers;
        Ok(Self { raw, program_headers })
    }

    /// Iterates over the segments that map bytes from guest memory.
    fn load_segments(&self) -> impl Iterator<Item = &ProgramHeader> + '_ {
        self.program_headers.iter().filter(|h| h.p_type == PT_LOAD && h.p_filesz > 0)
    }

    /// Returns the GPA at which `needle` occurs within guest memory.
    fn find_in_guest_memory(&self, needle: &[u8]) -> Vec<u64> {
        let mut hits = Vec::new();
        for header in self.load_segments() {
            let mut range = header.file_range();
            range.end = range.end.min(self.raw.len());
            if range.start >= range.end {
                continue;
            }
            // The segment's first file byte maps to guest-physical address
            // `p_paddr`, so an offset within `haystack` is that same offset past
            // `p_paddr`.
            let haystack = &self.raw[range];
            hits.extend(
                find_subslices(haystack, needle).map(|offset| header.p_paddr + offset as u64),
            );
        }
        hits
    }

    /// Reads the bytes of guest-physical memory in the address range `range`,
    /// returning `None` if the range is empty or not fully contained in a
    /// single mapped segment.
    fn read_guest_memory(&self, range: Range<u64>) -> Option<&[u8]> {
        if range.is_empty() {
            return None;
        }
        for header in self.load_segments() {
            let seg_start = header.p_paddr;
            let seg_end = seg_start + header.p_filesz;
            if range.start < seg_start || range.end > seg_end {
                continue;
            }
            let seg_range = header.file_range();
            let file_start = seg_range.start + (range.start - seg_start) as usize;
            let file_end = file_start + (range.end - range.start) as usize;
            if file_end <= self.raw.len() {
                return Some(&self.raw[file_start..file_end]);
            }
        }
        None
    }

    /// Reads a fixed-size `N`-byte array of guest-physical memory starting at
    /// `phys_addr`, returning `None` if the range is not fully mapped.
    ///
    /// This is a convenience wrapper around [`Core::read_guest_memory`] for the
    /// common case of reading a statically-sized value (e.g. a 32-byte key).
    fn read_fixed<const N: usize>(&self, phys_addr: u64) -> Option<[u8; N]> {
        let bytes = self.read_guest_memory(phys_addr..phys_addr + N as u64)?;
        Some(bytes.try_into().expect("read_guest_memory returns exactly N bytes"))
    }
}

/// Returns the offset of every (possibly overlapping) occurrence of `needle`
/// within `haystack`.
///
/// `needle` must not be empty.
fn find_subslices<'a>(haystack: &'a [u8], needle: &'a [u8]) -> impl Iterator<Item = usize> + 'a {
    assert!(!needle.is_empty(), "needle must not be empty");
    haystack
        .windows(needle.len())
        .enumerate()
        .filter(move |(_, window)| *window == needle)
        .map(|(offset, _)| offset)
}

/// Extracts the value that follows an ASCII `key` (e.g. `b"--oak-dice="`) in
/// `dump`, up to the next whitespace or NUL.
fn parse_cmdline_value(dump: &[u8], key: &[u8]) -> Option<String> {
    let pos = find_subslices(dump, key).next()?;
    let start = pos + key.len();
    let end = dump[start..]
        .iter()
        .position(|&b| b == b' ' || b == b'\n' || b == b'\r' || b == 0)
        .map(|p| start + p)
        .unwrap_or(dump.len());
    core::str::from_utf8(&dump[start..end]).ok().map(|s| s.to_string())
}

/// Derives the fixed, well-known stage0 root ECA signing key that the
/// `stage0_bin_fixed_key` firmware uses.
///
/// That firmware is built with the `fixed_root_key` feature, under which
/// `oak_stage0_dice` derives the root key scalar as the SHA-256 digest of a
/// hard-coded seed (see `stage0_dice/src/lib.rs`). This mirrors that derivation
/// so the test knows exactly which private-key bytes to search for. Keep the
/// seed in sync with that crate.
fn stage0_root_signing_key() -> [u8; 32] {
    let mut hasher = Sha256::new();
    hasher.update(b"oak stage0 root eca fixed test signing key seed v1");
    let digest = hasher.finalize();
    let mut key = [0u8; 32];
    key.copy_from_slice(&digest);
    key
}

/// Parses the reserved DICE handoff region that stage0 declares to the next
/// stage on the kernel command line, returning `(start_phys_addr, length)`.
///
/// Stage0 appends `--oak-dice=<hex-addr>` and `--oak-dice-length=<decimal>`
/// (see [`oak_dice::evidence::DICE_DATA_CMDLINE_PARAM`] and
/// [`oak_dice::evidence::DICE_DATA_LENGTH_CMDLINE_PARAM`]).
fn dice_region(core: &Core) -> Result<(u64, u64)> {
    let addr_param = oak_dice::evidence::DICE_DATA_CMDLINE_PARAM;
    let len_param = oak_dice::evidence::DICE_DATA_LENGTH_CMDLINE_PARAM;

    let addr = parse_cmdline_value(&core.raw, format!("--{addr_param}=").as_bytes())
        .and_then(|value| u64::from_str_radix(value.strip_prefix("0x")?, 16).ok());
    let len = parse_cmdline_value(&core.raw, format!("--{len_param}=").as_bytes())
        .and_then(|value| value.parse::<u64>().ok());

    addr.zip(len).or_fail().with_failure_message(|| {
        format!(
            "could not find the DICE handoff region ({addr_param} / {len_param}) on the kernel \
             command line in the dump"
        )
    })
}

/// Reads the raw 32-byte layer-1 (handoff) ECA private key out of the
/// `Stage0DiceData` structure that stage0 writes at the start of the reserved
/// DICE region (guest-physical address `region_start`).
///
/// The layer-1 key is generated randomly, so unlike the root key its bytes are
/// not known ahead of time and must be recovered from guest memory. The P256
/// scalar occupies the first [`P256_PRIVATE_KEY_SIZE`] bytes of the
/// `eca_private_key` field.
///
/// [`P256_PRIVATE_KEY_SIZE`]: oak_dice::evidence::P256_PRIVATE_KEY_SIZE
fn read_layer1_signing_key(core: &Core, region_start: u64) -> Result<[u8; 32]> {
    let field_offset = std::mem::offset_of!(Stage0DiceData, layer_1_certificate_authority);
    let key_addr = region_start + field_offset as u64;
    core.read_fixed::<32>(key_addr).or_fail().with_failure_message(|| {
        format!(
            "could not read the layer-1 ECA private key at guest-physical address 0x{key_addr:x} \
             from the core dump"
        )
    })
}

/// Verifies that stage0 erases its transient root ECA signing key before
/// handing control to the next stage.
///
/// The root key is used only to sign the layer-1 certificate and is never
/// handed onward, so it must not appear anywhere in guest memory. It is derived
/// from a fixed seed (see [`stage0_root_signing_key`]) so this test knows
/// exactly which bytes to search for.
#[googletest::test]
fn assert_root_key_erased() -> Result<()> {
    let root_key = stage0_root_signing_key();

    let core = Core::parse(boot_and_dump_guest_memory()?)?;

    // The transient root ECA key must not appear anywhere in guest memory.
    verify_that!(core.find_in_guest_memory(&root_key), is_empty())
}

/// Verifies that the random layer-1 (stage1) handoff ECA signing key exists
/// only within the reserved DICE region that stage0 hands to the next stage.
#[googletest::test]
fn assert_layer1_key_confined() -> Result<()> {
    let core = Core::parse(boot_and_dump_guest_memory()?)?;

    let (region_start, region_len) = dice_region(&core)?;
    let region_end = region_start + region_len;

    // The layer-1 key is random, so recover its bytes from the handoff structure.
    let layer1_key = read_layer1_signing_key(&core, region_start)?;
    let hits = core.find_in_guest_memory(&layer1_key);

    // Sanity: the key must be present in its handoff location, otherwise the
    // confinement assertion below would pass vacuously.
    assert_that!(hits, not(is_empty()));

    // Every copy of the key must lie within the reserved DICE region.
    let leaked: Vec<String> = hits
        .iter()
        .filter(|&&addr| !(region_start..region_end).contains(&addr))
        .map(|a| format!("0x{a:x}"))
        .collect();

    verify_that!(leaked, is_empty())
}

// Tests for some of the test helper functions.

#[googletest::test]
fn find_subslices_finds_non_overlapping_matches() -> Result<()> {
    verify_that!(
        find_subslices(b"abcXXabc", b"abc").collect::<Vec<_>>(),
        container_eq(vec![0usize, 5])
    )
}

#[googletest::test]
fn find_subslices_finds_overlapping_matches() -> Result<()> {
    verify_that!(
        find_subslices(b"aaaa", b"aa").collect::<Vec<_>>(),
        container_eq(vec![0usize, 1, 2])
    )
}

#[googletest::test]
fn find_subslices_reports_no_match_when_absent() -> Result<()> {
    verify_that!(find_subslices(b"abcdef", b"xyz").collect::<Vec<_>>(), is_empty())
}

#[googletest::test]
fn find_subslices_reports_no_match_when_needle_longer_than_haystack() -> Result<()> {
    verify_that!(find_subslices(b"ab", b"abcd").collect::<Vec<_>>(), is_empty())
}
