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

use core::fmt::Write;
use uefi::{prelude::*, table::runtime::ResetType, ResultExt};

#[entry]
fn main(_handle: Handle, mut system_table: SystemTable<Boot>) -> Status {
    uefi_services::init(&mut system_table).unwrap_success();

    let status = writeln!(system_table.stdout(), "Hello World!");

    system_table.runtime_services().reset(
        ResetType::Shutdown,
        match status {
            Ok(_) => Status::SUCCESS,
            Err(core::fmt::Error) => Status::DEVICE_ERROR,
        },
        None,
    );
}
