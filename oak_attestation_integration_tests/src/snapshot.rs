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

use std::path::{Path, PathBuf};

use chrono::{DateTime, Utc};
use oak_proto_rust::oak::{attestation::v1::ReferenceValues, session::v1::EndorsedEvidence};
use prost::Message;
use tokio::{
    fs::{File, ReadDir},
    io::AsyncWriteExt,
};

pub struct SnapshotPath {
    version: u16,
}

impl SnapshotPath {
    const TESTDATA_DIR: &'static str = "./oak_attestation_integration_tests/testdata/snapshots";
    const ENDORSED_EVIDENCE_FILE: &'static str = "endorsed_evidence.binarypb";
    const REFERENCE_VALUES_FILE: &'static str = "reference_values.binarypb";

    /// Returns the directory name for this snapshot.
    fn dirname(&self) -> PathBuf {
        Path::new(Self::TESTDATA_DIR).join(format!("{:05}", self.version))
    }

    fn version(&self) -> u16 {
        self.version
    }

    fn endorsed_evidence_path(&self) -> PathBuf {
        self.dirname().join(Self::ENDORSED_EVIDENCE_FILE)
    }

    fn reference_values_path(&self) -> PathBuf {
        self.dirname().join(Self::REFERENCE_VALUES_FILE)
    }

    /// Retrieves the most recent snapshot by finding the highest version number
    /// in the testdata directory.
    pub async fn most_recent() -> anyhow::Result<Self> {
        let mut entries = tokio::fs::read_dir(Self::TESTDATA_DIR)
            .await
            .map_err(|e| anyhow::anyhow!("Failed to read testdata directory: {}", e))?;
        let mut max_version = 0u16;
        while let Some(entry) = entries.next_entry().await? {
            if let Ok(file_name) = entry.file_name().into_string() {
                if let Ok(version) = file_name.parse::<u16>() {
                    max_version = max_version.max(version);
                }
            }
        }

        Ok(Self { version: max_version })
    }

    /// Creates a new SnapshotPath with a version number one higher than the
    /// most recent snapshot. This function is used to generate the next
    /// sequential snapshot.
    pub async fn next() -> anyhow::Result<Self> {
        let most_recent_snapshot = Self::most_recent().await?;
        Ok(Self { version: most_recent_snapshot.version() + 1 })
    }
}

pub struct Snapshot {
    pub endorsed_evidence: EndorsedEvidence,
    pub reference_values: ReferenceValues,
}

impl Snapshot {
    pub async fn read_from_path(path: &SnapshotPath) -> anyhow::Result<Self> {
        let endorsed_evidence_bytes = tokio::fs::read(path.endorsed_evidence_path())
            .await
            .map_err(|e| anyhow::anyhow!("Failed to read endorsed evidence file: {}", e))?;
        let endorsed_evidence = EndorsedEvidence::decode(endorsed_evidence_bytes.as_slice())
            .map_err(|e| anyhow::anyhow!("Failed to decode endorsed evidence: {}", e))?;

        let reference_values_bytes = tokio::fs::read(path.reference_values_path())
            .await
            .map_err(|e| anyhow::anyhow!("Failed to read reference values file: {}", e))?;
        let reference_values = ReferenceValues::decode(reference_values_bytes.as_slice())
            .map_err(|e| anyhow::anyhow!("Failed to decode reference values: {}", e))?;

        Ok(Self { endorsed_evidence, reference_values })
    }

    pub async fn write_to_path(&self, path: &SnapshotPath) -> anyhow::Result<()> {
        tokio::fs::create_dir_all(path.dirname()).await.map_err(|e| {
            anyhow::anyhow!("Failed to create directory {:?}: {}", path.dirname(), e)
        })?;

        let endorsed_evidence_path = path.endorsed_evidence_path();
        let reference_values_path = path.reference_values_path();

        let endorsed_evidence_bytes = self.endorsed_evidence.encode_to_vec();
        let reference_values_bytes = self.reference_values.encode_to_vec();

        tokio::fs::write(&endorsed_evidence_path, endorsed_evidence_bytes)
            .await
            .map_err(|e| anyhow::anyhow!("Failed to write endorsed evidence file: {}", e))?;
        tokio::fs::write(&reference_values_path, reference_values_bytes)
            .await
            .map_err(|e| anyhow::anyhow!("Failed to write reference values file: {}", e))?;

        Ok(())
    }
}
