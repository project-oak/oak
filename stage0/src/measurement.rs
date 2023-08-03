//
// Copyright 2023 The Project Oak Authors
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

use oak_linux_boot_params::BootE820Entry;

// A builder for recording measurements and publishing the results.
pub trait MeasurementBuilder {
    /// Measures the raw kernel image bytes.
    fn measure_kernel(&mut self, kernel_image: &[u8]);
    /// Measures the kernel setup data bytes.
    fn measure_kernel_setup_data(&mut self, setup_data: &[u8]);
    /// Measures the kernel command-line.
    fn measure_kernel_cmdline(&mut self, kernel_cmdline: &[u8]);
    /// Measures the initial RAM disk bytes.
    fn measure_init_ram_fs(&mut self, init_ram_fs: &[u8]);
    /// Measures the concatenated ACPI table generation command.
    fn measure_acpi_data(&mut self, acpi_data: &[u8]);
    /// Measures the concatenated ACPI table generation command.
    fn measure_memory_map(&mut self, e820_table: &[BootE820Entry]);
    /// Finalises the measurement and publishes the results.
    fn publish(self) -> Result<(), &'static str>;
}

// A measurement builder that does nothing.
pub struct NoOpBuilder {}

impl MeasurementBuilder for NoOpBuilder {
    fn measure_kernel(&mut self, _kernel_image: &[u8]) {}
    fn measure_kernel_setup_data(&mut self, _setup_data: &[u8]) {}
    fn measure_kernel_cmdline(&mut self, _kernel_cmdline: &[u8]) {}
    fn measure_init_ram_fs(&mut self, _init_ram_fs: &[u8]) {}
    fn measure_acpi_data(&mut self, _acpi_data: &[u8]) {}
    fn measure_memory_map(&mut self, _e820_table: &[BootE820Entry]) {}
    fn publish(self) -> Result<(), &'static str> {
        Ok(())
    }
}
