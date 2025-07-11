//
// Copyright 2025 The Project Oak Authors
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

use std::{
    ffi::OsStr,
    process::{Command, Stdio},
};

use googletest::prelude::*;
use oak_file_utils::data_path;

fn launch_vmm<I, S>(additional_args: I) -> Result<Vec<u8>>
where
    I: IntoIterator<Item = S>,
    S: AsRef<OsStr>,
{
    let kernel = data_path("oak_restricted_kernel_wrapper/stage0_test_kernel_bin");
    let bios = data_path("stage0_bin/stage0_bin");

    let mut cmd = Command::new(which::which("qemu-system-x86_64")?);
    cmd.args(["-cpu", "host"]);
    cmd.arg("-enable-kvm");
    cmd.args(["-display", "none"]);
    cmd.arg("-nographic");
    cmd.arg("-nodefaults");
    cmd.arg("-no-reboot");
    cmd.args(["-d", "int,unimp,guest_errors"]);
    cmd.args(["-serial", "stdio"]);
    cmd.args(["-kernel", kernel.into_os_string().into_string().unwrap().as_str()]);
    cmd.args(["-bios", bios.into_os_string().into_string().unwrap().as_str()]);
    cmd.args(additional_args);

    // stderr goes to stderr, we only capture stdout
    cmd.stdin(Stdio::null());
    cmd.stderr(Stdio::inherit());
    let output = cmd.output()?.stdout;
    Ok(output)
}

#[test]
fn microvm_smoke_test() -> Result<()> {
    let output = launch_vmm(vec!["-machine", "microvm"])?;
    let output = String::try_from(output)?;
    verify_that!(output, contains_substring("boot successful"))
}

#[test]
fn q35_smoke_test() -> Result<()> {
    let output = launch_vmm(vec!["-machine", "q35"])?;
    let output = String::try_from(output)?;
    verify_that!(output, contains_substring("boot successful"))
}
