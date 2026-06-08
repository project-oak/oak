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

use core::arch::asm;

use oak_core::sync::OnceCell;
use oak_hal::{IoPortFactory, PortFactory, PortWriter};
use x86_64::{VirtAddr, instructions::tables::lidt, structures::DescriptorTablePointer};

/// Stored platform-specific shutdown function, registered during
/// initialization via [`init`].
static SHUTDOWN_FN: OnceCell<fn() -> !> = OnceCell::new();

/// Registers the platform-specific shutdown function.
///
/// Must be called during kernel initialization. This bridges the gap between
/// the generic `start_kernel<P>` and the non-generic [`shutdown`] / panic
/// handler.
pub fn init<P: crate::Platform + crate::hal::KernelPlatform>() {
    SHUTDOWN_FN.set(P::shutdown).expect("shutdown function already initialized");
}

/// Tries various ways to shut down the machine.
pub fn shutdown() -> ! {
    if let Some(platform_shutdown) = SHUTDOWN_FN.get() {
        platform_shutdown()
    }

    // If init hasn't been called yet (very early panic), fall back to the
    // last resort.
    halt()
}

/// Attempts shutdown via the i8042 controller, then falls back to [`halt`].
///
/// This is intended to be called by `KernelPlatform::shutdown()`
/// implementations after they have exhausted platform-specific shutdown
/// mechanisms.
pub fn shutdown_with_port_factory(port_factory: &PortFactory) -> ! {
    let mut port: oak_hal::Port<u8> = port_factory.new_writer(0x64);
    // Safety: This is safe as both qemu and crosvm expose the i8042 device by
    // default.
    unsafe {
        let _ = port.try_write(0xFE_u8);
    }

    halt()
}

/// Last resort: load a garbage IDT and cause #UD, forcing a triple fault.
fn halt() -> ! {
    let idt = DescriptorTablePointer { limit: 0, base: VirtAddr::new(0x0) };
    // Safety: this is technically safe, as it will cause the machine to crash, and
    // that's the intent.
    unsafe {
        lidt(&idt);
        asm! {
            "ud2",
            options(noreturn)
        }
    }
}
