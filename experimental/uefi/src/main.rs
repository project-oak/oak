//
// Copyright 2022 The Project Oak Authors
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

#![no_main]
#![no_std]
#![feature(abi_efiapi)]
#![feature(custom_test_frameworks)]
#![test_runner(crate::test_runner)]
#![reexport_test_harness_main = "test_main"]

use uefi::{prelude::*, table::runtime::ResetType, ResultExt};

#[entry]
fn _start(_handle: Handle, mut system_table: SystemTable<Boot>) -> Status {
    uefi_services::init(&mut system_table).unwrap_success();

    let status = if cfg!(test) {
        #[cfg(test)]
        test_main();
        Status::SUCCESS
    } else {
        main(_handle, &mut system_table)
    };

    system_table
        .runtime_services()
        .reset(ResetType::Shutdown, status, None);
}

fn main(_handle: Handle, system_table: &mut SystemTable<Boot>) -> Status {
    use core::fmt::Write;

    let status = writeln!(system_table.stdout(), "Hello World!");

    match status {
        Ok(_) => Status::SUCCESS,
        Err(core::fmt::Error) => Status::DEVICE_ERROR,
    }
}

#[cfg(test)]
fn test_runner(tests: &[&dyn Fn()]) {
    for test in tests {
        test();
    }
}

#[test_case]
fn test_simple() {
    assert_eq!(1, 1);
}
