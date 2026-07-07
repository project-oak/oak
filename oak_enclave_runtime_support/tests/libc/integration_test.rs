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

//! Integration test for the Oak LLVM libc port.
//!
//! Boots the FFI test app (`//oak_enclave_runtime_support/tests/libc/app`)
//! inside a QEMU VM
//! running Oak Restricted Kernel and verifies that the serial console output
//! contains the expected success markers. This exercises the `__llvm_libc_*`
//! vendor callbacks provided by `oak_enclave_runtime_support` end to end.

use std::{
    io::Read,
    process::{Command, Stdio},
    sync::mpsc,
    time::Duration,
};

use googletest::prelude::*;
use oak_file_utils::data_path;

/// Launches QEMU with the restricted kernel and FFI test app as the initrd,
/// captures serial output, and returns it as a string.
///
/// The VM is given a generous timeout to account for kernel boot time and
/// test execution.
fn launch_ffi_test_app() -> Result<String> {
    let kernel = data_path(
        "oak_restricted_kernel_wrapper/oak_restricted_kernel_wrapper_simple_io_channel_bin",
    );
    let bios = data_path("stage0_bin/stage0_bin");
    let initrd = data_path("oak_enclave_runtime_support/tests/libc/app/oak_ffi_test_app");

    let mut child = Command::new(which::which("qemu-system-x86_64")?)
        .args(["-cpu", "host"])
        .arg("-enable-kvm")
        .args(["-machine", "microvm,acpi=on"])
        .arg("-nographic")
        .arg("-nodefaults")
        .arg("-no-reboot")
        .args(["-m", "256M"])
        .args(["-serial", "stdio"])
        .args(["-bios", bios.to_str().unwrap()])
        .args(["-kernel", kernel.to_str().unwrap()])
        .args(["-initrd", initrd.to_str().unwrap()])
        .stdin(Stdio::null())
        .stdout(Stdio::piped())
        .stderr(Stdio::inherit())
        .spawn()?;

    let stdout = child.stdout.take().expect("stdout was piped");
    let (tx, rx) = mpsc::channel();

    // Read serial output in a background thread so we can apply a timeout.
    std::thread::spawn(move || {
        let mut buf = String::new();
        let mut reader = std::io::BufReader::new(stdout);
        let _ = reader.read_to_string(&mut buf);
        let _ = tx.send(buf);
    });

    let output = rx
        .recv_timeout(Duration::from_secs(120))
        .unwrap_or_else(|_| String::from("<timeout: no output within 120s>"));

    // Ensure QEMU is cleaned up.
    let _ = child.kill();
    let _ = child.wait();

    Ok(output)
}

#[test]
fn ffi_test_app_runs_successfully() -> Result<()> {
    let output = launch_ffi_test_app()?;
    verify_that!(
        output,
        all![
            contains_substring("malloc alignment tests passed"),
            contains_substring("aligned_alloc tests passed"),
            contains_substring("all FFI tests passed"),
        ]
    )
}
