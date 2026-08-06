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

//! Integration tests that verify that intermediate DICE signing keys and CDIs
//! are wiped from guest memory once Oak Restricted Kernel boots and executes an
//! application.
//!
//! The DICE evidence chain transitions as follows:
//!
//! * **Stage 1 (Kernel / Orchestrator)**: Stage 0 generates a transient Stage 1
//!   ECA key and Layer 1 CDI, passed to the kernel via the reserved DICE
//!   region. Once the kernel / initial application performs the DICE transition
//!   to Stage 2 (generating application keys and signing the application
//!   certificate), all intermediate Stage 1 keys and CDIs must be erased from
//!   guest memory.
//!
//! This test boots Stage 0 together with the Oak Restricted Kernel and a test
//! application that performs the DICE handoff, captures a full guest physical
//! memory dump via the QEMU QMP `dump-guest-memory` command, and verifies that:
//!
//! 1. The Stage 1 ECA signing key is absent everywhere in memory.
//! 2. The Stage 1 CDI is absent everywhere in memory.

use googletest::prelude::*;
use oak_file_utils::data_path;
use oak_test_utils::{Core, QemuBuilder};

const READY_MARKER: &str = "test application ready for memory dump";

/// Structure holding the memory dump and keys extracted during the test boot.
struct GuestDump {
    core: Core,
    layer1_key: [u8; 32],
    layer1_cdi: [u8; 32],
}

/// Boots Stage 0, Restricted Kernel, and the test application, and once the
/// application signals that it has completed its DICE transition, captures a
/// full dump of the guest's physical memory as an ELF core file.
fn boot_and_dump() -> anyhow::Result<GuestDump> {
    let kernel =
        data_path("oak_restricted_kernel_wrapper/oak_restricted_kernel_wrapper_serial_channel_bin");
    let bios = data_path("stage0_bin/stage0_bin");
    let initrd = data_path("oak_restricted_kernel/testing/test_orchestrator");

    let dump = QemuBuilder::new(kernel).bios(bios).initrd(initrd).boot_and_dump(READY_MARKER)?;

    let layer1_key = dump
        .parse_line_hex::<32>("LAYER1_KEY=")
        .ok_or_else(|| anyhow::anyhow!("did not receive LAYER1_KEY from guest"))?;
    let layer1_cdi = dump
        .parse_line_hex::<32>("LAYER1_CDI=")
        .ok_or_else(|| anyhow::anyhow!("did not receive LAYER1_CDI from guest"))?;

    Ok(GuestDump { core: dump.core, layer1_key, layer1_cdi })
}

/// Verifies that the Stage 1 (Restricted Kernel) ECA signing key is completely
/// erased from guest memory once the application has completed the DICE
/// transition.
#[googletest::test]
fn assert_layer1_key_erased() {
    let dump = boot_and_dump().unwrap();

    // Sanity check: the extracted key should not be trivial (all-zeros).
    assert_that!(dump.layer1_key, not(eq([0u8; 32])));

    let hits = dump.core.find_in_guest_memory(&dump.layer1_key);
    let leaked: Vec<String> = hits.iter().map(|a| format!("0x{a:x}")).collect();

    assert_that!(leaked, is_empty());
}

/// Verifies that the Stage 1 CDI (Compound Device Identifier) is completely
/// erased from guest memory once the application has completed the DICE
/// transition.
#[googletest::test]
fn assert_layer1_cdi_erased() {
    let dump = boot_and_dump().unwrap();

    // Sanity check: the extracted CDI should not be trivial (all-zeros).
    assert_that!(dump.layer1_cdi, not(eq([0u8; 32])));

    let hits = dump.core.find_in_guest_memory(&dump.layer1_cdi);
    let leaked: Vec<String> = hits.iter().map(|a| format!("0x{a:x}")).collect();

    assert_that!(leaked, is_empty());
}

/// Sanity test: verifies that search in guest memory works as expected by
/// finding the ready marker string that the test app emitted.
#[googletest::test]
fn sanity_finds_marker_in_guest_memory() {
    let dump = boot_and_dump().unwrap();

    let hits = dump.core.find_in_guest_memory(READY_MARKER.as_bytes());
    assert_that!(hits, not(is_empty()));
}
