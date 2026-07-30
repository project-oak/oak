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

use std::{
    io::{self, BufRead, BufReader, Write},
    os::unix::net::UnixStream,
    path::PathBuf,
    process::{Command, Stdio},
    sync::mpsc,
    thread,
    time::{Duration, Instant},
};

use goblin::elf::{Elf, program_header::PT_LOAD};
use googletest::prelude::*;
use oak_file_utils::data_path;
use sha2::{Digest, Sha256};

/// Marker printed by the halting test kernel once stage0 has handed control to
/// the kernel. See `test_kernel.rs`.
const BOOT_MARKER: &str = "boot successful";

/// Boots stage0 together with the test kernel and, once the kernel is running,
/// captures a full dump of the guest's physical memory.
fn boot_and_dump_guest_memory() -> Result<Vec<u8>> {
    let kernel = data_path("oak_restricted_kernel_wrapper/stage0_dump_test_kernel_bin");
    let bios = data_path("stage0_bin/insecure_stage0_bin_fixed_key");

    // Unix socket paths are length-limited (~108 bytes on Linux), and the Bazel
    // test tmpdir can be long, so keep the QMP socket under `/tmp` with a short,
    // unique name. The (unbounded-length) dump file can live in the test tmpdir.
    let unique = format!("oak_stage0_dump_{}", std::process::id());
    let qmp_path = PathBuf::from(format!("/tmp/{unique}.qmp"));
    let dump_path = std::env::temp_dir().join(format!("{unique}.elf"));
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

    let dump_result = (|| -> Result<Vec<u8>> {
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

        Ok(std::fs::read(&dump_path)?)
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

/// Returns the guest-physical addresses at which `needle` occurs within the
/// `PT_LOAD` segments of the parsed ELF core `dump`.
///
/// QEMU's `dump-guest-memory` writes an ELF core dump whose `PT_LOAD` program
/// headers map regions of the file onto guest-physical memory. See the QEMU
/// dump format documentation:
/// <https://www.qemu.org/docs/master/interop/dump-format.html>
fn find_in_guest_memory(dump: &[u8], needle: &[u8]) -> Result<Vec<u64>> {
    let elf = Elf::parse(dump)?;

    let mut hits = Vec::new();
    for header in elf.program_headers.iter().filter(|h| h.p_type == PT_LOAD && h.p_filesz > 0) {
        let mut range = header.file_range();
        range.end = range.end.min(dump.len());
        if range.start >= range.end {
            continue;
        }
        // The segment's first file byte maps to guest-physical address `p_paddr`,
        // so an offset within `haystack` is that same offset past `p_paddr`.
        let haystack = &dump[range];
        hits.extend(find_subslices(haystack, needle).map(|offset| header.p_paddr + offset as u64));
    }
    Ok(hits)
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

    let dump = boot_and_dump_guest_memory()?;

    // The transient root ECA key must not appear anywhere in guest memory.
    verify_that!(find_in_guest_memory(&dump, &root_key)?, is_empty())
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
