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
#![feature(never_type)]
#![feature(custom_test_frameworks)]
// As we're in a `no_std` environment, testing requires special handling. This
// approach was inspired by https://os.phil-opp.com/testing/.
#![test_runner(crate::test_runner)]
#![reexport_test_harness_main = "test_main"]

#[macro_use]
extern crate log;
extern crate alloc;

use ciborium::{de, ser};
use uefi::{prelude::*, table::runtime::ResetType};

mod serial;

// The main entry point of the UEFI application.
//
// The choice of name (`_start`) is entirely arbitrary; what matters is that
// there's exactly one function with the `#[entry]` attribute in the
// dependency graph.
#[entry]
fn _start(handle: Handle, mut system_table: SystemTable<Boot>) -> Status {
    uefi_services::init(&mut system_table).unwrap();

    // As we're not relying on the normal Rust test harness, we need to call
    // the tests ourselves if necessary.
    let status = if cfg!(test) {
        #[cfg(test)]
        test_main();
        Status::SUCCESS
    } else {
        main(handle, &mut system_table)
    };

    // After we're done running our code, we also tell the UEFI runtime to shut
    // down the machine, otherwise we'd go back to the UEFI shell.
    system_table
        .runtime_services()
        .reset(ResetType::Shutdown, status, None);
}

// Run the echo on the first serial port in the system (the UEFI console will
// use the first serial port in the system)
const ECHO_SERIAL_PORT_INDEX: usize = 1;


fn main(handle: Handle, system_table: &mut SystemTable<Boot>) -> Status {
    use core::fmt::Write;

    writeln!(system_table.stdout(), "Hello World!").unwrap();

    serial_echo(handle, system_table.boot_services(), ECHO_SERIAL_PORT_INDEX).unwrap();
}


// Opens the index-th serial port on the system and echoes back all frames sent over the serial port.
//
// Panics if the index-th serial port does not exist.
//
// Arguments:
//    * `handle` - UEFI handle of the agent (eg of the UEFI app)
//    * `boot_services` - reference to the UEFI Boot Services struct (obtained from the system table)
//    * `index` - index of the serial port, zero-based.
//
//  Normally does not return, unless an error is raised.
fn serial_echo(handle: Handle, bt: &BootServices, index: usize) -> Result<!, uefi::Error<()>> {
    let mut serial = serial::Serial::get(handle, bt, index)?;
    loop {
        let msg: alloc::string::String = de::from_reader(&mut serial).map_err(|err| match err {
            de::Error::Io(err) => err,
            de::Error::Syntax(idx) => {
                error!("Error reading data at index {}", idx);
                uefi::Error::from(Status::INVALID_PARAMETER)
            }
            de::Error::Semantic(_, err) => {
                error!("Error parsing cbor data: {:?}", err);
                uefi::Error::from(Status::INVALID_PARAMETER)
            }
            de::Error::RecursionLimitExceeded => uefi::Error::from(Status::ABORTED),
        })?;
        ser::into_writer(&msg, &mut serial).map_err(|err| match err {
            ser::Error::Io(err) => err,
            ser::Error::Value(msg) => {
                error!("Error serializing value: {}", msg);
                uefi::Error::from(Status::INVALID_PARAMETER)
            }
        })?;
    }
}

#[cfg(test)]
fn test_runner(tests: &[&dyn Fn()]) {
    for test in tests {
        test();
    }
}

// Simple silly test just to prove that the test infrastructure works.
#[test_case]
fn test_simple() {
    let x = 1;
    assert_eq!(x, 1);
}
