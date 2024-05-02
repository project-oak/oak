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

#![feature(let_chains)]

extern crate alloc;

#[cfg(test)]
extern crate std;

use alloc::{format, string::String};

use anyhow::{Context, Result};
use oak_proto_rust::oak::{
    attestation::v1::{
        root_layer_data::Report, ApplicationLayerData, ApplicationLayerReferenceValues,
        KernelLayerData, KernelLayerReferenceValues, OakContainersData,
        OakContainersReferenceValues, OakRestrictedKernelData, OakRestrictedKernelReferenceValues,
        ReferenceValues, RootLayerData, RootLayerReferenceValues, SystemLayerData,
        SystemLayerReferenceValues,
    },
    RawDigest,
};
use sha2::{Digest, Sha256};
use zerocopy::{FromBytes, FromZeroes};

use crate::alloc::{borrow::ToOwned, string::ToString};

/// Provides human readable explanations for attestation data.
pub trait HumanReadableTitle {
    /// Concise title, eg. "Oak Containers Stack in a AMD SEV-SNP TEE".
    fn title(&self) -> Result<String, anyhow::Error>;
}

pub trait HumanReadableExplanation {
    /// Provides human readable explanations for a layer of an attestation data
    /// stack, including directions to map the attestation data to source code.
    fn description(&self) -> Result<String, anyhow::Error>;
}

// Adapt the JSON mapping of reference values to make it human readable.
fn make_reference_value_json_human_readable(value: &mut serde_json::Value) {
    fn modify_node(value: &mut serde_json::Value) {
        if let serde_json::Value::Object(map) = value {
            // Some referene values are nested under a value key. Remove
            // for human readability.
            if map.len() == 1
                && let Some(inner_value) = map.get_mut("value")
            {
                *value = inner_value.clone();
                return;
            }
            // Some messages nest digests twice. Once under a digest key that
            // holds an object, and then again under a digest key that holds an array.
            // Simplify by rmeoving the first nesting.
            if map.len() == 1
                && let Some(digests) = map.get_mut("digests")
                && matches!(digests, serde_json::Value::Object(_))
            {
                *value = digests.clone();
                return;
            }

            // Print digest hashes with hex encoding.
            if serde_json::from_value::<RawDigest>(serde_json::Value::Object(map.clone())).is_ok() {
                map.iter_mut().for_each(|(_key, hash_value)| {
                    // The proto3 JSON mapping spec uses base64 encoding.
                    let base64_encoded_hash =
                        hash_value.as_str().expect("validated as string in prior conditional");
                    let hash =
                        base64::decode(base64_encoded_hash).expect("invalid base64 digest hash");
                    *hash_value = serde_json::Value::String(hex::encode(hash));
                })
            };
        }
    }

    // Performs operation on every node in a potentially nested JSON tree.
    fn for_each_node<F>(value: &mut serde_json::Value, operator: &F)
    where
        F: Fn(&mut serde_json::Value),
    {
        operator(value);
        match value {
            serde_json::Value::Object(map) => {
                map.iter_mut().for_each(|(_, v)| for_each_node(v, operator))
            }
            serde_json::Value::Array(arr) => {
                arr.iter_mut().for_each(|v| for_each_node(v, operator))
            }
            _ => {}
        }
    }

    // Reference values are usually a nested set of Json nodes. Visit each one
    // and simplify it if needed.
    for_each_node(value, &modify_node);
}

fn get_tee_name(tee_report: &Report) -> &'static str {
    match tee_report {
        Report::SevSnp(_) => "AMD SEV-SNP",
        Report::Tdx(_) => "Intel TDX",
        Report::Fake(_) => "UNSAFE FAKE",
    }
}

impl HumanReadableTitle for ReferenceValues {
    fn title(&self) -> Result<String, anyhow::Error> {
        match &self.r#type {
            Some(
                oak_proto_rust::oak::attestation::v1::reference_values::Type::OakRestrictedKernel(
                    _value,
                ),
            ) => Ok("Reference values for the Oak Restricted Kernel stack".to_owned()),
            Some(oak_proto_rust::oak::attestation::v1::reference_values::Type::OakContainers(
                _value,
            )) => Ok("Reference values for the Oak Containers stack".to_owned()),
            _ => Ok("Unrecognized reference values".to_owned()),
        }
    }
}

impl HumanReadableExplanation for ReferenceValues {
    fn description(&self) -> Result<String, anyhow::Error> {
        let mut json_representation = serde_json::to_value(self).map_err(anyhow::Error::msg)?;
        make_reference_value_json_human_readable(&mut json_representation);
        serde_json::to_string_pretty(&json_representation).map_err(anyhow::Error::msg)
    }
}

impl HumanReadableTitle for OakRestrictedKernelData {
    fn title(&self) -> Result<String, anyhow::Error> {
        let tee_report = self
            .root_layer
            .as_ref()
            .context("unexpectedly unset root_layer proto field")?
            .report
            .as_ref()
            .context("unexpectedly unset report proto field")?;
        let tee_name = get_tee_name(tee_report);
        Ok(format!("Oak Restricted Kernel Stack in a {} TEE", tee_name))
    }
}

impl HumanReadableTitle for OakRestrictedKernelReferenceValues {
    fn title(&self) -> Result<String, anyhow::Error> {
        Ok("Oak Restricted Kernel Stack".to_owned())
    }
}

impl HumanReadableTitle for OakContainersData {
    fn title(&self) -> Result<String, anyhow::Error> {
        let tee_report = self
            .root_layer
            .clone()
            .context("unexpectedly unset root_layer proto field")?
            .report
            .clone()
            .context("unexpectedly unset report proto field")?;
        let tee_name = get_tee_name(&tee_report);
        Ok(format!("Evidence of the Oak Conatiners Stack in a {} TEE", tee_name))
    }
}

impl HumanReadableTitle for OakContainersReferenceValues {
    fn title(&self) -> Result<String, anyhow::Error> {
        Ok("Oak Conatiners Stack".to_owned())
    }
}

impl HumanReadableTitle for RootLayerData {
    fn title(&self) -> Result<String, anyhow::Error> {
        Ok("Root Layer".to_string())
    }
}

impl HumanReadableExplanation for RootLayerData {
    fn description(&self) -> Result<String, anyhow::Error> {
        match self.report.as_ref().context("unexpectedly unset report proto field")? {
            Report::SevSnp(report) => {
                let initial_memory_sha256_digest =
                    SNPInitialMemoryMeasurement::try_from(report.initial_measurement.as_slice())?;
                Ok(format!(
                    "Firmware [Digest]: {}
{}
Firmware [Provenances]: {}",
                    initial_memory_sha256_digest.display_hash(),
                    initial_memory_sha256_digest.display_hash_explaination(),
                    initial_memory_sha256_digest.provenance_link()
                ))
            }
            _ => Err(anyhow::Error::msg(
                "human readable description not yet implemented for this type of TEE",
            )),
        }
    }
}

impl HumanReadableTitle for RootLayerReferenceValues {
    fn title(&self) -> Result<String, anyhow::Error> {
        Ok("Root Layer".to_string())
    }
}

impl HumanReadableExplanation for RootLayerReferenceValues {
    fn description(&self) -> Result<String, anyhow::Error> {
        let mut json_representation = serde_json::to_value(self).map_err(anyhow::Error::msg)?;
        make_reference_value_json_human_readable(&mut json_representation);
        serde_json::to_string_pretty(&json_representation).map_err(anyhow::Error::msg)
    }
}

impl HumanReadableTitle for KernelLayerData {
    fn title(&self) -> Result<String, anyhow::Error> {
        Ok("Kernel Layer".to_string())
    }
}

impl HumanReadableExplanation for KernelLayerData {
    fn description(&self) -> Result<String, anyhow::Error> {
        let kernel_image_digest: ArtifactDigestSha2_256 = self
            .kernel_image
            .as_ref()
            .context("unexpectedly unset kernel_image proto field")
            .and_then(|digest| {
                ArtifactDigestSha2_256::try_from(digest).map_err(anyhow::Error::from)
            })?;

        let bz_image_description = format!(
            "Kernel Image [Digest]: {}
Kernel Setup Data [Digest]: {}",
            kernel_image_digest.display_hash(),
            ArtifactDigestSha2_256::try_from(
                self.kernel_setup_data
                    .as_ref()
                    .context("unexpectedly unset kernel_setup_data proto field")?
            )?
            .display_hash(),
        );
        let kernel_commandline = format!(
            "Kernel Command Line [String]: {}",
            self.kernel_raw_cmd_line
                .as_ref()
                .context("unexpectedly unset kernel_raw_cmd_line proto field")?,
        );
        let init_ram_fs_digest: ArtifactDigestSha2_256 = self
            .init_ram_fs
            .as_ref()
            .context("unexpectedly unset init_ram_fs proto field")
            .and_then(|digest| {
                ArtifactDigestSha2_256::try_from(digest).map_err(anyhow::Error::from)
            })?;
        let initial_ramdisk_description =
            format!("Initial RAM Disk [Digest]: {}", init_ram_fs_digest.display_hash());

        Ok(format!(
            "{}
Kernel Image/Setup-Data [Provenances]: {}
{}
{}
Inital RAM Disk [Provenances]: {}",
            bz_image_description,
            kernel_image_digest.provenance_link(),
            kernel_commandline,
            initial_ramdisk_description,
            init_ram_fs_digest.provenance_link()
        ))
    }
}

impl HumanReadableTitle for KernelLayerReferenceValues {
    fn title(&self) -> Result<String, anyhow::Error> {
        Ok("Kernel Layer".to_string())
    }
}

impl HumanReadableExplanation for KernelLayerReferenceValues {
    fn description(&self) -> Result<String, anyhow::Error> {
        let mut json_representation = serde_json::to_value(self).map_err(anyhow::Error::msg)?;
        make_reference_value_json_human_readable(&mut json_representation);
        serde_json::to_string_pretty(&json_representation).map_err(anyhow::Error::msg)
    }
}

impl HumanReadableTitle for SystemLayerData {
    fn title(&self) -> Result<String, anyhow::Error> {
        Ok("System Layer".to_string())
    }
}

impl HumanReadableExplanation for SystemLayerData {
    fn description(&self) -> Result<String, anyhow::Error> {
        let system_image_digest = self
            .system_image
            .as_ref()
            .context("unexpectedly unset system_image proto field")
            .and_then(|digest| {
                ArtifactDigestSha2_256::try_from(digest).map_err(anyhow::Error::from)
            })?;
        Ok(format!(
            "System Image [Digest]: {}
System Image [Provenances]: {}",
            system_image_digest.display_hash(),
            system_image_digest.provenance_link(),
        ))
    }
}

impl HumanReadableTitle for SystemLayerReferenceValues {
    fn title(&self) -> Result<String, anyhow::Error> {
        Ok("System Layer".to_string())
    }
}

impl HumanReadableExplanation for SystemLayerReferenceValues {
    fn description(&self) -> Result<String, anyhow::Error> {
        let mut json_representation = serde_json::to_value(self).map_err(anyhow::Error::msg)?;
        make_reference_value_json_human_readable(&mut json_representation);
        serde_json::to_string_pretty(&json_representation).map_err(anyhow::Error::msg)
    }
}

impl HumanReadableTitle for ApplicationLayerData {
    fn title(&self) -> Result<String, anyhow::Error> {
        Ok("Application Layer".to_string())
    }
}

impl HumanReadableExplanation for ApplicationLayerData {
    fn description(&self) -> Result<String, anyhow::Error> {
        let digests = {
            let binary_digest =
                self.binary.as_ref().context("unexpectedly unset binary proto field").and_then(
                    |digest| ArtifactDigestSha2_256::try_from(digest).map_err(anyhow::Error::from),
                )?;

            // Restricted Kernel Applications do not use a config, no digest is included in
            // the.
            if let Ok(config_digest) =
                self.config.as_ref().context("unexpectedly unset config proto field").and_then(
                    |digest| ArtifactDigestSha2_256::try_from(digest).map_err(anyhow::Error::from),
                )
            {
                format!(
                    "Binary [Digest]: {}
Binary [Provenances]: {}
Config [Digest]: {}
Config [Provenances]: {}",
                    binary_digest.display_hash(),
                    binary_digest.provenance_link(),
                    config_digest.display_hash(),
                    config_digest.provenance_link()
                )
            } else {
                format!(
                    "Binary [Digest]: {}
Binary [Provenances]: {}",
                    binary_digest.display_hash(),
                    binary_digest.provenance_link(),
                )
            }
        };

        Ok(digests)
    }
}

impl HumanReadableTitle for ApplicationLayerReferenceValues {
    fn title(&self) -> Result<String, anyhow::Error> {
        Ok("Application Layer".to_string())
    }
}

impl HumanReadableExplanation for ApplicationLayerReferenceValues {
    fn description(&self) -> Result<String, anyhow::Error> {
        let mut json_representation = serde_json::to_value(self).map_err(anyhow::Error::msg)?;
        make_reference_value_json_human_readable(&mut json_representation);
        serde_json::to_string_pretty(&json_representation).map_err(anyhow::Error::msg)
    }
}

trait OakDigestDisplay {
    /// String of the hash in the following format: [alg]:[hash]. The algorithm
    /// descripter follows fieldnames of the proto-message: oak.RawDigest
    /// struct.
    fn display_hash(&self) -> String;

    fn provenance_link(&self) -> String;
}

/// Convience struct that maintains type safety determinig the length of the
/// underlying slice. Provides consistent methods for creating and printing the
/// data.
#[derive(FromBytes, FromZeroes)]
struct ArtifactDigestSha2_256(pub [u8; 32]);

impl TryFrom<&RawDigest> for ArtifactDigestSha2_256 {
    type Error = anyhow::Error;

    fn try_from(value: &RawDigest) -> Result<Self, Self::Error> {
        match value.sha2_256.as_slice() {
            [] => Err(anyhow::Error::msg("no sha2_256 hash found")),
            _ => value.sha2_256.as_slice().try_into(),
        }
    }
}

impl TryFrom<&[u8]> for ArtifactDigestSha2_256 {
    type Error = anyhow::Error;

    fn try_from(slice: &[u8]) -> Result<Self, Self::Error> {
        ArtifactDigestSha2_256::read_from(slice).context("unexpected length of measurement")
    }
}

impl OakDigestDisplay for ArtifactDigestSha2_256 {
    // # TODO: b/335458726 - Stop permitting unexported code once mod is completed.
    #[allow(dead_code)]
    fn provenance_link(&self) -> String {
        format!("https://search.sigstore.dev/?hash={}", hex::encode(self.0))
    }
    fn display_hash(&self) -> String {
        format!("SHA2-256:{}", hex::encode(self.0.as_slice()))
    }
}

/// Convience struct that maintains type safety determinig the length of the
/// underlying slice. Provides consistent methods for creating and printing the
/// data.
#[derive(FromZeroes, FromBytes)]
struct SNPInitialMemoryMeasurement([u8; 48]);

impl SNPInitialMemoryMeasurement {
    fn sha2_256(&self) -> ArtifactDigestSha2_256 {
        Sha256::digest(self.0).as_slice().try_into().expect("sha256 digest to have expected length")
    }
    /// Print a hash in the following format: [alg]:[hash]. The algorithm
    /// descripter follows fieldnames of the proto-message: oak.RawDigest
    /// struct.
    fn display_hash_explaination(&self) -> String {
        format!(
            "ⓘ The firmware attestation digest is the SHA2-256 hash of the SHA2-384 hash of the initial memory state taken by the AMD SoC. The original SHA2-384 hash of the initial memory is: SHA2-384:{}.",
            { hex::encode(self.0.as_slice()) }
        )
    }
}

impl OakDigestDisplay for SNPInitialMemoryMeasurement {
    fn display_hash(&self) -> String {
        self.sha2_256().display_hash()
    }

    fn provenance_link(&self) -> String {
        format!("https://search.sigstore.dev/?hash={}", hex::encode(self.sha2_256().0))
    }
}

impl TryFrom<&[u8]> for SNPInitialMemoryMeasurement {
    type Error = anyhow::Error;

    fn try_from(slice: &[u8]) -> Result<Self, Self::Error> {
        SNPInitialMemoryMeasurement::read_from(slice).context("unexpected length of measurement")
    }
}
