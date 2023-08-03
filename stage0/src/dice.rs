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

//! Data structures for representing Stage 0's measurement of the next boot stage and the related
//! DICE artifacts.

use crate::measurement::MeasurementBuilder;
use oak_linux_boot_params::BootE820Entry;
use oak_sev_guest::guest::AttestationReport;
use sha2::{Digest, Sha384};
use zerocopy::{AsBytes, FromBytes};

/// Measurement builder to support DICE-specific measurements.
#[derive(Default)]
pub struct DiceBuilder {
    /// The digest of the kernel image that was loaded.
    pub kernel_digest: Sha384,
    /// The digest of the setup data for the kernel. This is only provided when booting a bzImage
    /// kernel.
    pub setup_data_digest: Sha384,
    /// The digest of the kernel command-line.
    pub kernel_cmdline_digest: Sha384,
    /// The digest of the initial RAM disk.
    pub init_ram_fs_digest: Sha384,
    /// The digest of the concatenated ACPI table building commands received from the VMM.
    pub acpi_digest: Sha384,
    /// The digest of the  e820 memory map for the VM.
    pub memory_map_digest: Sha384,
}

impl From<DiceBuilder> for Stage1Measurements {
    fn from(builder: DiceBuilder) -> Self {
        let kernel_digest = builder.kernel_digest.finalize();
        let kernel_cmdline_digest = builder.kernel_cmdline_digest.finalize();
        let init_ram_fs_digest = builder.init_ram_fs_digest.finalize();
        let setup_data_digest = builder.setup_data_digest.finalize();
        let acpi_digest = builder.acpi_digest.finalize();
        let memory_map_digest = builder.memory_map_digest.finalize();
        let mut result = Stage1Measurements::default();
        result.kernel_digest.copy_from_slice(&kernel_digest[..]);
        result
            .kernel_cmdline_digest
            .copy_from_slice(&kernel_cmdline_digest[..]);
        result
            .setup_data_digest
            .copy_from_slice(&setup_data_digest[..]);
        result
            .init_ram_fs_digest
            .copy_from_slice(&init_ram_fs_digest[..]);
        result.acpi_digest.copy_from_slice(&acpi_digest[..]);
        result
            .memory_map_digest
            .copy_from_slice(&memory_map_digest[..]);
        result
    }
}

impl MeasurementBuilder for DiceBuilder {
    fn measure_kernel(&mut self, kernel_image: &[u8]) {
        self.kernel_digest.update(kernel_image);
    }
    fn measure_kernel_setup_data(&mut self, setup_data: &[u8]) {
        self.setup_data_digest.update(setup_data);
    }
    fn measure_kernel_cmdline(&mut self, kernel_cmdline: &[u8]) {
        self.kernel_cmdline_digest.update(kernel_cmdline);
    }
    fn measure_init_ram_fs(&mut self, init_ram_fs: &[u8]) {
        self.init_ram_fs_digest.update(init_ram_fs);
    }
    fn measure_acpi_data(&mut self, acpi_data: &[u8]) {
        self.acpi_digest.update(acpi_data);
    }
    fn measure_memory_map(&mut self, e820_table: &[BootE820Entry]) {
        self.memory_map_digest.update(e820_table.as_bytes());
    }
    fn publish(self) -> Result<(), &'static str> {
        let measurements: Stage1Measurements = self.into();
        // For now we just log the measurements.
        log::info!("DICE measurements: {measurements:?}");
        Ok(())
    }
}

/// Measurements of the components that could affect the behaviour of the next boot stage.
///
/// If any of the components were not loaded the associated digest value will be left as all 0.
#[repr(C)]
#[derive(Debug, AsBytes, FromBytes)]
pub struct Stage1Measurements {
    /// The digest of the kernel image that was loaded.
    pub kernel_digest: [u8; 48],
    /// The digest of the setup data for the kernel. This is only provided when booting a bzImage
    /// kernel.
    pub setup_data_digest: [u8; 48],
    /// The digest of the kernel command-line.
    pub kernel_cmdline_digest: [u8; 48],
    /// The digest of the initial RAM disk.
    pub init_ram_fs_digest: [u8; 48],
    /// The digest of the concatenated ACPI table building commands received from the VMM.
    pub acpi_digest: [u8; 48],
    /// The digest of the  e820 memory map for the VM.
    pub memory_map_digest: [u8; 48],
}

impl Default for Stage1Measurements {
    fn default() -> Self {
        Self {
            kernel_digest: [0u8; 48],
            kernel_cmdline_digest: [0u8; 48],
            setup_data_digest: [0u8; 48],
            init_ram_fs_digest: [0u8; 48],
            acpi_digest: [0u8; 48],
            memory_map_digest: [0u8; 48],
        }
    }
}

/// Non-standard unsigned certificate format that binds a public key for the next stage to the
/// measurements of the components that could influence its behaviour.
#[repr(C)]
#[derive(Debug, AsBytes, FromBytes)]
pub struct Stage1Certificate {
    /// The measurements of the next stage's components.
    pub measurements: Stage1Measurements,
    /// The embedded certificate authority (ECA) public key for the next stage. The field is large
    /// enough to support an uncompressed public key with additional padding to ensure field
    /// alignment.
    pub eca_public_key: [u8; 128],
}

impl Default for Stage1Certificate {
    fn default() -> Self {
        Self {
            measurements: Stage1Measurements::default(),
            eca_public_key: [0u8; 128],
        }
    }
}

/// Non-standard signed certificate format that binds a public key for the next stage to the
/// measurements of the components that could influence its behaviour.
///
/// We use the Attestation report as a non-standard signature for the certificate by providing the
/// digest of the unsigned certificate as additional data when requesting the attestation report.
#[repr(C)]
#[derive(Debug, Default, AsBytes, FromBytes)]
pub struct Stage1SignedCertificate {
    /// The unsiged certificate data.
    pub certificate: Stage1Certificate,
    /// The attestation report that acts as a signature for the certificate.
    pub attestation_report: AttestationReport,
}

/// The DICE data that will be passed to the next boot stage.
#[repr(C)]
#[derive(Debug, AsBytes, FromBytes)]
pub struct Stage1DiceData {
    /// The embedded certificate authority private key for the next stage.
    pub eca_private_key: [u8; 48],
    /// The signed certificate for the next stage's ECA key.
    pub signed_certificate: Stage1SignedCertificate,
}

impl Default for Stage1DiceData {
    fn default() -> Self {
        Self {
            eca_private_key: [0u8; 48],
            signed_certificate: Stage1SignedCertificate::default(),
        }
    }
}
