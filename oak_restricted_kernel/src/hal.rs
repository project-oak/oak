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

pub mod sev;

use oak_linux_boot_params::BootParams;

/// Kernel-specific trait for the Hardware Abstraction Layer (HAL).
pub trait KernelPlatform {
    /// Platform-specific initialization logic that must run after logging is
    /// configured and the initial page tables are set up.
    fn initialize_platform(info: &BootParams);

    /// Platform-specific method to register any additional interrupt handlers.
    fn add_additional_interrupt_handlers(
        idt: &mut x86_64::structures::idt::InterruptDescriptorTable,
    );

    /// Attempts to shut down the machine using platform-specific mechanisms.
    ///
    /// Implementations should first try any platform-specific shutdown
    /// protocol (e.g., the SEV-ES VMGEXIT-based termination), then fall
    /// back to [`crate::shutdown::shutdown_with_port_factory`] which
    /// attempts the i8042 reset and ultimately forces a triple fault.
    fn shutdown() -> !;
}
