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

use core::fmt::Write;

use oak_dice::evidence::Stage0DiceData;
use oak_restricted_kernel_interface::{syscall, DERIVED_KEY_FD, DICE_DATA_FD};
use oak_restricted_kernel_orchestrator::AttestedApp;
use oak_restricted_kernel_sdk::channel::FileDescriptorChannel;
use zerocopy::{AsBytes, FromZeroes};
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
#[no_mangle]
fn _start() -> ! {
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
    let buffer = result.as_bytes_mut();
    let len = syscall::read(DICE_DATA_FD, buffer).expect("failed to read dice data");
    assert!(len == buffer.len(), "invalid dice data size");
    result
}

fn entrypoint() -> ! {
    let mut attested_app = {
        let stage0_dice_data = read_stage0_dice_data();
        let channel = FileDescriptorChannel::default();
        AttestedApp::load_and_attest(channel, stage0_dice_data)
    };

    syscall::write(DERIVED_KEY_FD, attested_app.derived_key.as_bytes())
        .expect("failed to write derived key");
    attested_app.derived_key.as_bytes_mut().zeroize();
    syscall::write(DICE_DATA_FD, attested_app.dice_data.as_bytes())
        .expect("failed to write dice data");
    attested_app.dice_data.as_bytes_mut().zeroize();

    log::info!("Exiting and launching application.");
    syscall::unstable_switch_proccess(attested_app.elf_binary.as_slice())
}
