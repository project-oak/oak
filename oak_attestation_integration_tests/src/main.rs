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
//! Binary that's used to facilitate tests. It creates binary-encoded evidence,
//! endorsements, and reference values using the code current attestation code.
//!
//! The resulting outputs are stored as testdata. They can be used to validate
//! that newer versions of the verification library continue to be able to
//! verify older versions of these artifacts.

use oak_attestation_integration_tests::{Snapshot, SnapshotPath, create};

// Constants that define the measurements for evidence.
const SETUP_DATA_DIGEST: &[u8] = &[1u8; 32];
const KERNEL_MEASUREMENT: &[u8] = &[2u8; 32];
const RAM_DISK_DIGEST: &[u8] = &[3u8; 32];
const MEMORY_MAP_DIGEST: &[u8] = &[4u8; 32];
const ACPI_DIGEST: &[u8] = &[5u8; 32];
const KERNEL_CMDLINE: &str = "custom kernel command line";
const STAGE1_SYSTEM_IMAGE: &[u8] = &[6u8; 32];
const APPLICATION_IMAGE: &[u8] = &[7u8; 32];
const APPLICATION_CONFIG: &[u8] = &[8u8; 32];

#[tokio::main]
async fn main() -> anyhow::Result<()> {
    let (endorsed_evidence, reference_values) = {
        let stage0_digests = oak_proto_rust::oak::attestation::v1::Stage0Measurements {
            setup_data_digest: SETUP_DATA_DIGEST.to_vec(),
            kernel_measurement: KERNEL_MEASUREMENT.to_vec(),
            ram_disk_digest: RAM_DISK_DIGEST.to_vec(),
            memory_map_digest: MEMORY_MAP_DIGEST.to_vec(),
            acpi_digest: ACPI_DIGEST.to_vec(),
            kernel_cmdline: KERNEL_CMDLINE.to_string(),
        };
        create::oak_containers_standalone_endorsed_evidence_with_matching_reference_values(
            stage0_digests,
            STAGE1_SYSTEM_IMAGE,
            APPLICATION_IMAGE,
            APPLICATION_CONFIG.to_vec(),
        )
        .await
    };

    let snapshot = Snapshot { endorsed_evidence, reference_values };
    let mut most_recent_path = SnapshotPath::most_recent().await?;
    let previous_snapshot = Snapshot::read_from_path(&most_recent_path).await?;

    let new_properties = snapshot.assert_is_not_a_breaking_change(&previous_snapshot).await.expect("Found changes in attestation outputs, that may break verification for older versions of the attestation library. This usually happens when removing fields, or changing the contents of existing ones.");
    if new_properties.is_empty() {
        println!("No changes detected! Doing nothing.");
    } else {
        println!("Saving new snapshot, as new properties were added: {:?}", new_properties);
        let new_path = most_recent_path.next().expect("Failed to get next snapshot path");
        snapshot.write_to_path(&new_path).await?;
    }

    Ok(())
}
