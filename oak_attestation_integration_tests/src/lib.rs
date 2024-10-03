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

use anyhow::Context;
use oak_proto_rust::oak::{attestation::v1::ReferenceValues, session::v1::EndorsedEvidence};
use prost::Message;

pub struct SnapshotPath {
    version: u16,
}

impl SnapshotPath {
    const TESTDATA_DIR: &'static str = "./oak_attestation_integration_tests/testdata/snapshots";
    const ENDORSED_EVIDENCE_FILE: &'static str = "endorsed_evidence.binarypb";
    const REFERENCE_VALUES_FILE: &'static str = "reference_values.binarypb";

    /// Returns the directory name for this snapshot.
    pub fn dirname(&self) -> PathBuf {
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
}

impl Iterator for SnapshotPath {
    type Item = Self;

    fn next(&mut self) -> Option<Self::Item> {
        self.version = self.version.checked_add(1)?;
        Some(Self { version: self.version })
    }
}

impl DoubleEndedIterator for SnapshotPath {
    fn next_back(&mut self) -> Option<Self::Item> {
        self.version = self.version.checked_sub(1)?;
        Some(Self { version: self.version })
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

    /// Asserts that the current attestation outputs indicate no breaking
    /// changes.
    ///
    /// Effectively this simulates a client running an old version of the
    /// verification library encountering attestation outputs created by the
    /// current version of the attestation logic.
    ///
    /// This is hard to simulate directly so instead the current snapshot is
    /// compared to the previous one. It may only add properties, never
    /// change or removed any. The assumption is that since all the fields known
    /// to the older client remain the same, verification should still work.
    ///
    /// Returns a list of any newly added properties.
    pub async fn assert_is_not_a_breaking_change(
        &self,
        previous: &Self,
    ) -> anyhow::Result<Vec<String>> {
        // Utility to remove dynamic properties prior to comparing equality.
        fn remove_skipped_properties(value: &mut serde_json::Value, properties: &[&str]) {
            for field in properties {
                if let Some(current) = value.pointer_mut(field) {
                    *current = serde_json::Value::Null;
                }
            }
        }

        // TODO: b/370445356 - Instead of skipping these entirely, do a more
        // sophisticated equality check, e.g. by parsing the certificates and comparing
        // properties.
        const SKIPPED_DYNAMIC_PROPERTIES: &[&str] = &[
            "/evidence/applicationKeys/encryptionPublicKeyCertificate",
            "/evidence/applicationKeys/signingPublicKeyCertificate",
            "/evidence/layers/0/ecaCertificate",
            "/evidence/layers/1/ecaCertificate",
            "/evidence/rootLayer/ecaPublicKey",
            "/evidence/rootLayer/remoteAttestationReport",
        ];

        let (
            mut self_endorsed_evidence_json,
            previous_endorsed_evidence_json,
            mut self_reference_values_json,
            previous_reference_values_json,
        ) = tokio::try_join!(
            async {
                let mut json = oak_attestation_integration_test_utils::endorsed_evidence_as_json(
                    &self.endorsed_evidence,
                )
                .await?;
                remove_skipped_properties(&mut json, SKIPPED_DYNAMIC_PROPERTIES);
                Ok::<_, anyhow::Error>(json)
            },
            async {
                let mut json = oak_attestation_integration_test_utils::endorsed_evidence_as_json(
                    &previous.endorsed_evidence,
                )
                .await?;
                remove_skipped_properties(&mut json, SKIPPED_DYNAMIC_PROPERTIES);
                Ok::<_, anyhow::Error>(json)
            },
            async {
                let mut json = oak_attestation_integration_test_utils::reference_values_as_json(
                    &self.reference_values,
                )
                .await?;
                remove_skipped_properties(&mut json, SKIPPED_DYNAMIC_PROPERTIES);
                Ok::<_, anyhow::Error>(json)
            },
            async {
                let mut json = oak_attestation_integration_test_utils::reference_values_as_json(
                    &previous.reference_values,
                )
                .await?;
                remove_skipped_properties(&mut json, SKIPPED_DYNAMIC_PROPERTIES);
                Ok::<_, anyhow::Error>(json)
            }
        )?;

        /// Checks equality on shared properties between current and previous
        /// JSON values, and returns a list of new properties found in the
        /// current value.
        fn assert_existing_fields_unchanged_and_get_new_properties(
            mut current: serde_json::Value,
            previous: &serde_json::Value,
        ) -> anyhow::Result<Vec<String>> {
            let new_properties = oak_attestation_integration_test_utils::remove_new_properties(
                &mut current,
                previous,
                "",
            );

            let config = assert_json_diff::Config::new(assert_json_diff::CompareMode::Inclusive);
            assert_json_diff::assert_json_matches_no_panic(&current, previous, config)
                .map_err(anyhow::Error::msg)?;

            Ok(new_properties)
        }

        let mut new_properties = assert_existing_fields_unchanged_and_get_new_properties(
            self_endorsed_evidence_json,
            &previous_endorsed_evidence_json,
        )
        .context("Endorsed evidence mismatch")?;

        new_properties.extend(
            assert_existing_fields_unchanged_and_get_new_properties(
                self_reference_values_json,
                &previous_reference_values_json,
            )
            .context("Reference values mismatch")?,
        );

        Ok(new_properties)
    }
}
