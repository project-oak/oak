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

use googletest::prelude::*;
use oak_dice::evidence::Stage0DiceData;
use oak_file_utils::data_path;
use oak_test_utils::{Core, QemuBuilder};
use sha2::{Digest, Sha256};

/// Marker printed by the halting test kernel once stage0 has handed control to
/// the kernel. See `test_kernel.rs`.
const BOOT_MARKER: &str = "boot successful";

/// Boots stage0 together with the test kernel and captures a full dump of the
/// guest's physical memory.
fn boot_and_dump_guest_memory() -> anyhow::Result<Core> {
    let kernel = data_path("oak_restricted_kernel_wrapper/stage0_dump_test_kernel_bin");
    let bios = data_path("stage0_bin/insecure_stage0_bin_fixed_key");

    let dump = QemuBuilder::new(kernel).bios(bios).boot_and_dump(BOOT_MARKER)?;
    Ok(dump.core)
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
fn dice_region(core: &Core) -> anyhow::Result<(u64, u64)> {
    let addr_param = oak_dice::evidence::DICE_DATA_CMDLINE_PARAM;
    let len_param = oak_dice::evidence::DICE_DATA_LENGTH_CMDLINE_PARAM;

    let addr = parse_cmdline_value(&core.raw, format!("--{addr_param}=").as_bytes())
        .and_then(|value| u64::from_str_radix(value.strip_prefix("0x")?, 16).ok());
    let len = parse_cmdline_value(&core.raw, format!("--{len_param}=").as_bytes())
        .and_then(|value| value.parse::<u64>().ok());

    addr.zip(len).ok_or_else(|| {
        anyhow::anyhow!(
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
fn read_layer1_signing_key(core: &Core, region_start: u64) -> anyhow::Result<[u8; 32]> {
    let field_offset = std::mem::offset_of!(Stage0DiceData, layer_1_certificate_authority);
    let key_addr = region_start + field_offset as u64;
    core.read_fixed::<32>(key_addr).ok_or_else(|| {
        anyhow::anyhow!(
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
fn assert_root_key_erased() {
    let root_key = stage0_root_signing_key();

    let core = boot_and_dump_guest_memory().unwrap();

    // The transient root ECA key must not appear anywhere in guest memory.
    assert_that!(core.find_in_guest_memory(&root_key), is_empty());
}

/// Verifies that the random layer-1 (stage1) handoff ECA signing key exists
/// only within the reserved DICE region that stage0 hands to the next stage.
#[googletest::test]
fn assert_layer1_key_confined() {
    let core = boot_and_dump_guest_memory().unwrap();

    let (region_start, region_len) = dice_region(&core).unwrap();
    let region_end = region_start + region_len;

    // The layer-1 key is random, so recover its bytes from the handoff structure.
    let layer1_key = read_layer1_signing_key(&core, region_start).unwrap();
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

    assert_that!(leaked, is_empty());
}

// Tests for some of the test helper functions.

#[googletest::test]
fn find_subslices_finds_non_overlapping_matches() {
    assert_that!(
        find_subslices(b"abcXXabc", b"abc").collect::<Vec<_>>(),
        container_eq(vec![0usize, 5])
    );
}

#[googletest::test]
fn find_subslices_finds_overlapping_matches() {
    assert_that!(
        find_subslices(b"aaaa", b"aa").collect::<Vec<_>>(),
        container_eq(vec![0usize, 1, 2])
    );
}

#[googletest::test]
fn find_subslices_reports_no_match_when_absent() {
    assert_that!(find_subslices(b"abcdef", b"xyz").collect::<Vec<_>>(), is_empty());
}

#[googletest::test]
fn find_subslices_reports_no_match_when_needle_longer_than_haystack() {
    assert_that!(find_subslices(b"ab", b"abcd").collect::<Vec<_>>(), is_empty());
}
