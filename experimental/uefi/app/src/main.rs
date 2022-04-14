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
extern crate anyhow;

use uefi::{
    prelude::*,
    proto::console::serial::Serial,
    table::{
        boot::{OpenProtocolAttributes, OpenProtocolParams},
        runtime::ResetType,
    },
};

#[cfg(test)]
use ring::rand::SecureRandom;

// The main entry point of the UEFI application.
//
// The choice of name (`_start`) is entirely arbitrary; what matters is that
// there's exactly one function with the `#[entry]` attribute in the
// dependency graph.
#[entry]
fn _start(_handle: Handle, mut system_table: SystemTable<Boot>) -> Status {
    uefi_services::init(&mut system_table).unwrap();

    // As we're not relying on the normal Rust test harness, we need to call
    // the tests ourselves if necessary.
    let status = if cfg!(test) {
        #[cfg(test)]
        test_main();
        Status::SUCCESS
    } else {
        main(_handle, &mut system_table)
    };

    // After we're done running our code, we also tell the UEFI runtime to shut
    // down the machine, otherwise we'd go back to the UEFI shell.
    system_table
        .runtime_services()
        .reset(ResetType::Shutdown, status, None);
}

fn main(handle: Handle, system_table: &mut SystemTable<Boot>) -> Status {
    use core::fmt::Write;

    writeln!(system_table.stdout(), "Hello World!").unwrap();

    serial_echo(handle, system_table.boot_services()).unwrap();
}

fn echo_loop(serial: &mut Serial) -> Result<!, uefi::Error<()>> {
    let mut buf: [u8; 1024] = [0; 1024];

    loop {
        // read() returns Ok if it managed to fill the whole buffer, or the error will contain
        // the number of bytes read. The only error we're fine with is TIMEOUT, as we can simply
        // retry that (and we'll keep getting TIMEOUTs when nobody is talking to us). In case of
        // any other error, bail out.
        let len = serial.read(&mut buf).map(|_| buf.len()).or_else(|err| {
            if err.status() == Status::TIMEOUT {
                Ok(*err.data())
            } else {
                Err(err.status())
            }
        })?;

        // Write out what we read; if we get any errors, propagate them.
        if len > 0 {
            info!("Read data: {:?}", &buf[..len]);
            serial.write(&buf[..len]).discard_errdata()?;
        }
    }
}

fn serial_echo(handle: Handle, bt: &BootServices) -> Result<!, uefi::Error<()>> {
    // Expect (at least) two serial ports on the system; the first will be used
    // for stdio, and we can use the second one for our echo example. If we don't
    // seem to have a second serial port, err out with the (arbitrarily chosen)
    // NO_MAPPING error.
    let serial_handles = bt.find_handles::<Serial>()?;
    let serial_handle = serial_handles.get(1).ok_or(Status::NO_MAPPING)?;
    let serial = bt.open_protocol::<Serial>(
        OpenProtocolParams {
            handle: *serial_handle,
            agent: handle,
            controller: None,
        },
        OpenProtocolAttributes::Exclusive,
    )?;
    // Dereference the raw pointer (*mut Serial) we get to the serial interface.
    // This is safe as according to the UEFI spec for the OpenProtocol call to succeed the
    // interface must not be null (see Section 7.3 in the UEFI Specification, Version 2.9).
    let serial = unsafe { &mut *serial.interface.get() };

    echo_loop(serial)
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

#[cfg(test)]
const EMPTY_ARRAY: [u8; 8] = [0, 0, 0, 0, 0, 0, 0, 0];

// Simple test source of randomness, for more straightforward debugging
#[test_case]
fn random_test() {
    let rng = ring::rand::SystemRandom::new();
    let mut array = EMPTY_ARRAY.clone();
    assert_eq!(rng.fill(&mut array).is_err(), false);
    assert_ne!(array, EMPTY_ARRAY);
}
