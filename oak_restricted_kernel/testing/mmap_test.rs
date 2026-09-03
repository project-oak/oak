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

//! Checks that the kernel grants Ring 3 no executable memory.
//!
//! Boots a guest running `mmap_test_app` and compares its whole report, so a
//! guest that stopped part way through fails too. To check the test can fail,
//! drop the `PROT_EXEC` guard in `oak_restricted_kernel/src/syscall/mmap.rs`:
//! the `EPERM` lines become `mapped`.

use googletest::prelude::*;
use oak_file_utils::data_path;
use oak_test_utils::QemuBuilder;

/// Kept in step with `mmap_test_app.rs`, a separate crate.
const REPORT_PREFIX: &str = "mmap_test: ";
const READY_MARKER: &str = "mmap test done";

/// `EPERM` and not merely a failure: `EINVAL` would mean the kernel did not
/// understand the request, and it could start understanding it again.
const EXPECTED_REPORT: &[&str] = &["rw=mapped,writable", "rwx=EPERM", "rx=EPERM", "x=EPERM"];

#[googletest::test]
fn ring3_cannot_map_executable_memory() {
    let dump = QemuBuilder::new(data_path(
        "oak_restricted_kernel_wrapper/oak_restricted_kernel_wrapper_virtio_console_channel_bin",
    ))
    .bios(data_path("stage0_bin/stage0_bin"))
    .initrd(data_path("enclave_apps/oak_orchestrator/oak_orchestrator"))
    .app_binary(data_path("oak_restricted_kernel/testing/mmap_test_app"))
    .boot_and_dump(READY_MARKER)
    .unwrap();

    let report: Vec<&str> =
        dump.stdout_lines.iter().filter_map(|l| l.trim().strip_prefix(REPORT_PREFIX)).collect();

    assert_that!(report.as_slice(), eq(EXPECTED_REPORT));
}
