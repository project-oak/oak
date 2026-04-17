//
// Copyright 2024 The Project Oak Authors
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

#![no_std]
#![no_main]
#![feature(alloc_error_handler)]

extern crate alloc;

use alloc::vec::Vec;
use core::fmt::Write;

use oak_dice::evidence::Stage0DiceData;
use oak_restricted_kernel_interface::{DERIVED_KEY_FD, DICE_DATA_FD, EVENT_LOG_FD, syscall};
use oak_restricted_kernel_orchestrator::AttestedApp;
use oak_restricted_kernel_sdk::channel::FileDescriptorChannel;
use zerocopy::{FromZeros, IntoBytes};
use zeroize::Zeroize;

struct OrchestratorLogger {}

impl log::Log for OrchestratorLogger {
    fn enabled(&self, _metadata: &log::Metadata) -> bool {
        true
    }

    fn log(&self, record: &log::Record) {
        writeln!(
            oak_restricted_kernel_sdk::utils::Stderr {},
            "orchestrator {}: {}",
            record.level(),
            record.args()
        )
        .unwrap();
    }

    fn flush(&self) {
        oak_restricted_kernel_sdk::utils::Stderr::flush();
    }
}

#[global_allocator]
static ALLOCATOR: oak_restricted_kernel_sdk::utils::heap::LockedGrowableHeap =
    oak_restricted_kernel_sdk::utils::heap::LockedGrowableHeap::empty();

static LOGGER: OrchestratorLogger = OrchestratorLogger {};

// The orchestrator uses a custom logging implementation, hence the
// #[oak_restricted_kernel_sdk::entrypoint] is not used. The allocator,
// handlers, etc are declared explicitly.
#[unsafe(no_mangle)]
fn _start() {
    oak_restricted_kernel_sdk::utils::log::set_logger(&LOGGER).expect("failed to set logger");
    oak_restricted_kernel_sdk::utils::log::set_max_level(
        oak_restricted_kernel_sdk::utils::log::LevelFilter::Debug,
    );
    entrypoint()
}

#[alloc_error_handler]
fn out_of_memory(layout: ::core::alloc::Layout) -> ! {
    panic!("error allocating memory in orchestrator: {:#?}", layout);
}

#[panic_handler]
fn panic(info: &core::panic::PanicInfo) -> ! {
    log::error!("orchestrator PANIC: {}", info);
    oak_restricted_kernel_interface::syscall::exit(-1);
}

fn read_stage0_dice_data() -> Stage0DiceData {
    let mut result = Stage0DiceData::new_zeroed();
    let buffer = result.as_mut_bytes();
    let len = syscall::read(DICE_DATA_FD, buffer).expect("failed to read dice data");
    assert!(len == buffer.len(), "invalid dice data size");
    result
}

fn read_encoded_event_log() -> Vec<u8> {
    let mut event_log = Vec::new();
    let mut buffer = [0u8; 1024]; // Read in 1KB chunks

    loop {
        match syscall::read(EVENT_LOG_FD, &mut buffer) {
            Ok(0) => break, // End of file
            Ok(n) => event_log.extend_from_slice(&buffer[..n]),
            Err(e) => panic!("Failed to read event log: {:?}", e),
        }
    }

    event_log
}

fn entrypoint() {
    let mut attested_app = {
        let stage0_dice_data = read_stage0_dice_data();
        let encoded_event_log = read_encoded_event_log();
        let channel = FileDescriptorChannel::default();
        AttestedApp::load_and_attest(channel, stage0_dice_data, encoded_event_log)
    };

    syscall::write(DERIVED_KEY_FD, attested_app.derived_key.as_bytes())
        .expect("failed to write derived key");
    attested_app.derived_key.as_mut_bytes().zeroize();
    syscall::write(DICE_DATA_FD, attested_app.dice_data.as_bytes())
        .expect("failed to write dice data");
    attested_app.dice_data.as_mut_bytes().zeroize();
    syscall::write(EVENT_LOG_FD, attested_app.get_encoded_event_log().as_slice())
        .expect("failed to write event log");

    log::info!(
        "Received {} bytes of endorsement data",
        attested_app.initial_data.endorsement_bytes.len()
    );

    log::info!("Finished setup, handing off executing to the app and going to sleep.");
    let pid =
        syscall::unstable_create_proccess(attested_app.initial_data.application_bytes.as_bytes())
            .expect("failed to create app process");
    log::warn!(
        "Orchestrator has been awoken! This only happens if the enclave app uses unstable syscalls."
    );
    for _ in 0..1 {
        log::info!("Zzz... (Hitting snooze, resuming the app)");
        let _ = syscall::unstable_switch_proccess(pid);
    }
    log::info!("That's it I quit!");
    oak_restricted_kernel_interface::syscall::sys_exit(0);
}
