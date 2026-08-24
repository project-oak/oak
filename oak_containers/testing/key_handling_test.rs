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

//! Integration tests that verify that intermediate DICE signing keys, CDIs,
//! and stage-to-stage handoff material are erased from guest memory once
//! Oak Containers boots and executes stage1.
//!
//! The Oak Containers DICE evidence chain transitions as follows:
//!
//! * **Stage 0 (Firmware)**: Stage 0 generates a transient Stage 1 ECA signing
//!   key and Layer 1 CDI, passed to the guest in the reserved physical memory
//!   region (`Stage0DiceData`).
//! * **Stage 1 (Initramfs)**: Stage 1 maps the reserved memory, deserializes
//!   the attester, zeroizes the Stage 0 physical memory, and drops the Stage 1
//!   key.
//!
//! This test boots Stage 0 together with the Linux kernel and the test-only
//! insecure build of `stage1` (`insecure_stage1_bin`), captures a full guest
//! physical memory dump via the QEMU QMP `dump-guest-memory` command, and
//! verifies that:
//!
//! 1. The Stage 1 ECA signing key is absent everywhere in guest memory.
//! 2. The Stage 1 CDI is absent everywhere in guest memory.
//! 3. Memory scanning is functional (sanity check finding the panic marker).

use std::sync::LazyLock;

use googletest::prelude::*;
use oak_file_utils::data_path;
use oak_test_utils::{Core, QemuBuilder};

const PANIC_MARKER: &str = "Kernel panic - not syncing: Attempted to kill init!";

/// Structure holding the memory dump and keys extracted during the test boot.
struct GuestDump {
    core: Core,
    layer1_key: [u8; 32],
    layer1_cdi: [u8; 32],
}

/// Boots Stage 0, Linux Kernel, and the insecure stage1 initramfs, waits for
/// stage1 to complete its DICE transitions and wipe physical memory, and
/// captures a full dump of the guest's physical memory as an ELF core file.
fn boot_and_dump() -> anyhow::Result<GuestDump> {
    let kernel = data_path("oak_containers/kernel/bzImage");
    let bios = data_path("stage0_bin/stage0_bin");
    let initrd = data_path("oak_containers/stage1_bin/insecure_stage1.cpio");

    let dump = QemuBuilder::new(kernel)
        .bios(bios)
        .initrd(initrd)
        .machine("microvm,acpi=on,pcie=on")
        .memory("1G")
        .extra_args(["-append", "console=ttyS0 panic=-1 loglevel=7 --"])
        .boot_and_dump(PANIC_MARKER)?;

    let layer1_key = dump
        .parse_line_hex::<32>("LAYER1_KEY=")
        .ok_or_else(|| anyhow::anyhow!("did not receive LAYER1_KEY from guest"))?;
    let layer1_cdi = dump
        .parse_line_hex::<32>("LAYER1_CDI=")
        .ok_or_else(|| anyhow::anyhow!("did not receive LAYER1_CDI from guest"))?;

    Ok(GuestDump { core: dump.core, layer1_key, layer1_cdi })
}

static DUMP: LazyLock<GuestDump> =
    LazyLock::new(|| boot_and_dump().expect("failed to boot guest and dump memory"));

fn get_dump() -> &'static GuestDump {
    &DUMP
}

/// Verifies that the Stage 1 (Layer 1) ECA signing key handed from Stage 0 is
/// completely erased from guest physical memory once Stage 1 has consumed it
/// and zeroized the reserved physical memory.
#[googletest::test]
fn assert_layer1_key_erased() {
    let dump = get_dump();

    // Sanity check: the extracted key should not be trivial (all-zeros).
    assert_that!(dump.layer1_key, not(eq([0u8; 32])));

    let hits = dump.core.find_in_guest_memory(&dump.layer1_key);
    let leaked: Vec<String> = hits.iter().map(|a| format!("0x{a:x}")).collect();

    assert_that!(leaked, is_empty());
}

/// Verifies that the Stage 1 (Layer 1) Compound Device Identifier (CDI) is
/// completely erased from guest physical memory once Stage 1 has transitioned.
#[googletest::test]
fn assert_layer1_cdi_erased() {
    let dump = get_dump();

    // Sanity check: the extracted CDI should not be trivial (all-zeros).
    assert_that!(dump.layer1_cdi, not(eq([0u8; 32])));

    let hits = dump.core.find_in_guest_memory(&dump.layer1_cdi);
    let leaked: Vec<String> = hits.iter().map(|a| format!("0x{a:x}")).collect();

    assert_that!(leaked, is_empty());
}

/// Sanity test: verifies that search in guest memory works as expected by
/// finding the panic marker string in guest memory.
#[googletest::test]
fn sanity_finds_marker_in_guest_memory() {
    let dump = get_dump();

    let hits = dump.core.find_in_guest_memory(PANIC_MARKER.as_bytes());
    assert_that!(hits, not(is_empty()));
}
