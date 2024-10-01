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

// TODO: b/370445356 - Write tests that use the created testdata.

use chrono::Utc;
use oak_attestation_integration_test_utils::create_oak_containers_standalone_endorsed_evidence_with_matching_reference_values;
use oak_proto_rust::oak::{attestation::v1::ReferenceValues, session::v1::EndorsedEvidence};
use prost::Message;
use tokio::{fs::File, io::AsyncWriteExt};

mod snapshot;

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
        create_oak_containers_standalone_endorsed_evidence_with_matching_reference_values(
            stage0_digests,
            STAGE1_SYSTEM_IMAGE,
            APPLICATION_IMAGE,
            APPLICATION_CONFIG.to_vec(),
        )
        .await
    };

    let new_path = snapshot::SnapshotPath::next().await?;
    let snapshot = snapshot::Snapshot { endorsed_evidence, reference_values };
    // TODO: b/370445356 - Only save a new snapshot if it's different from the most
    // recent one.
    snapshot.write_to_path(&new_path).await?;

    Ok(())
}
