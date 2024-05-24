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
use base64::{prelude::BASE64_STANDARD, Engine as _};
use oak_proto_rust::oak::{
    attestation::v1::{
        root_layer_data::Report, ApplicationLayerData, ApplicationLayerReferenceValues,
        ContainerLayerData, ContainerLayerReferenceValues, KernelLayerData,
        KernelLayerReferenceValues, OakContainersData, OakContainersReferenceValues,
        OakRestrictedKernelData, OakRestrictedKernelReferenceValues, ReferenceValues,
        RootLayerData, RootLayerReferenceValues, SystemLayerData, SystemLayerReferenceValues,
    },
    RawDigest,
};
use sha2::{Digest, Sha256};
use zerocopy::{FromBytes, FromZeroes};

use crate::alloc::{borrow::ToOwned, string::ToString};

const AMD_SEV_SNP_TITLE: &str = "AMD SEV-SNP";
const INTEL_TDX_TITLE: &str = "Intel TDX";
const INSECURE_TEE_TITLE: &str = "FAKE INSECURE";

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

fn reencode_base64_value_as_hex(
    value: &serde_yaml::Value,
) -> Result<serde_yaml::Value, anyhow::Error> {
    let base64_encoded = value.as_str().context("expected value to be a string string")?;
    let bytes = BASE64_STANDARD
        .decode(base64_encoded)
        .map_err(anyhow::Error::msg)
        .context("invalid base64")?;
    let hex_encoded = hex::encode(bytes);
    Ok(serde_yaml::Value::String(hex_encoded))
}

fn reencode_digests_as_hex(value: &mut serde_yaml::Value) {
    if serde_yaml::from_value::<RawDigest>(value.clone()).is_ok() {
        value.as_mapping_mut().expect("expected rawdigest to be a map").iter_mut().for_each(
            |(_key, hash_value)| {
                // The proto3 JSON mapping spec uses base64 encoding.
                *hash_value = reencode_base64_value_as_hex(hash_value)
                    .expect("failed to reencode base64 digest bytes as hex");
            },
        );
    };
}

// Performs operation on every node in a potentially nested YAML tree.
fn walk_nodes<F>(
    value: &mut serde_yaml::Value,
    operator: &F, // F is borrowed as otherwise the code encounters the recurision limit.
) where
    F: Fn(&mut serde_yaml::Value),
{
    operator(value);
    match value {
        serde_yaml::Value::Mapping(map) => {
            map.iter_mut().for_each(|(_, v)| walk_nodes(v, operator))
        }
        serde_yaml::Value::Sequence(arr) => arr.iter_mut().for_each(|v| walk_nodes(v, operator)),
        _ => {}
    }
}

// Adapt the YAML mapping of evidence to make it human readable.
fn make_evidence_human_readable(value: &mut serde_yaml::Value) {
    walk_nodes(value, &reencode_digests_as_hex);
}

// Adapt the YAML mapping of reference values to make it human readable.
fn make_reference_values_human_readable(value: &mut serde_yaml::Value) {
    fn modify_node(value: &mut serde_yaml::Value) {
        if let serde_yaml::Value::Mapping(map) = value {
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
                && matches!(digests, serde_yaml::Value::Mapping(_))
            {
                *value = digests.clone();
                return;
            }
        }

        reencode_digests_as_hex(value)
    }

    // Reference values are usually a nested set of YAML nodes. Visit each one
    // and simplify it if needed.
    walk_nodes(value, &modify_node);
}

fn get_tee_name_from_root_layer_evidence(
    root_layer: &RootLayerData,
) -> Result<&'static str, anyhow::Error> {
    match root_layer.report.as_ref().context("unexpectedly unset report proto field")? {
        Report::SevSnp(_) => Ok(AMD_SEV_SNP_TITLE),
        Report::Tdx(_) => Ok(INTEL_TDX_TITLE),
        Report::Fake(_) => Ok(INSECURE_TEE_TITLE),
    }
}

fn get_tee_name_from_root_layer_reference_values(
    root_layer_reference_values: &RootLayerReferenceValues,
) -> Result<String, anyhow::Error> {
    match root_layer_reference_values {
        RootLayerReferenceValues { insecure: Some(_), .. } => Ok(INSECURE_TEE_TITLE.to_owned()),
        RootLayerReferenceValues { amd_sev: Some(_), intel_tdx: Some(_), insecure: None } => {
            Ok(format!("{} or {}", AMD_SEV_SNP_TITLE, INTEL_TDX_TITLE))
        }
        RootLayerReferenceValues { amd_sev: None, intel_tdx: Some(_), insecure: None } => {
            Ok(INTEL_TDX_TITLE.to_owned())
        }
        RootLayerReferenceValues { amd_sev: Some(_), intel_tdx: None, insecure: None } => {
            Ok(AMD_SEV_SNP_TITLE.to_owned())
        }
        RootLayerReferenceValues { amd_sev: None, intel_tdx: None, insecure: None } => {
            Err(anyhow::Error::msg("no TEE value found in the reference values"))
        }
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
        let mut yaml_representation = serde_yaml::to_value(self).map_err(anyhow::Error::msg)?;
        make_reference_values_human_readable(&mut yaml_representation);
        serde_yaml::to_string(&yaml_representation).map_err(anyhow::Error::msg)
    }
}

impl HumanReadableTitle for OakRestrictedKernelData {
    fn title(&self) -> Result<String, anyhow::Error> {
        let root_layer =
            self.root_layer.clone().context("unexpectedly unset root_layer proto field")?;
        let tee_name = get_tee_name_from_root_layer_evidence(&root_layer)?;
        Ok(format!("Oak Restricted Kernel Stack in a {} TEE", tee_name))
    }
}

impl HumanReadableTitle for OakRestrictedKernelReferenceValues {
    fn title(&self) -> Result<String, anyhow::Error> {
        let root_layer =
            self.root_layer.as_ref().context("unexpectedly unset root_layer proto field")?;
        let tee_name = get_tee_name_from_root_layer_reference_values(root_layer)?;
        Ok(format!("Oak Restricted Kernel Stack in a {} TEE", tee_name))
    }
}

impl HumanReadableTitle for OakContainersData {
    fn title(&self) -> Result<String, anyhow::Error> {
        let root_layer =
            self.root_layer.clone().context("unexpectedly unset root_layer proto field")?;
        let tee_name = get_tee_name_from_root_layer_evidence(&root_layer)?;
        Ok(format!("Oak Containers Stack in a {} TEE", tee_name))
    }
}

impl HumanReadableTitle for OakContainersReferenceValues {
    fn title(&self) -> Result<String, anyhow::Error> {
        let root_layer =
            self.root_layer.as_ref().context("unexpectedly unset root_layer proto field")?;
        let tee_name = get_tee_name_from_root_layer_reference_values(root_layer)?;
        Ok(format!("Oak Containers Stack in a {} TEE", tee_name))
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
                let tee_name = get_tee_name_from_root_layer_evidence(self)?;
                let initial_memory_sha256_digest =
                    SNPInitialMemoryMeasurement::try_from(report.initial_measurement.as_slice())?;
                let firmware_provenace_link = initial_memory_sha256_digest.provenance_link();
                let firmware_hash_explaination =
                    initial_memory_sha256_digest.display_hash_explaination();
                let yaml_string = {
                    let mut yaml_representation =
                        serde_yaml::to_value(self).map_err(anyhow::Error::msg)?;
                    make_evidence_human_readable(&mut yaml_representation);
                    serde_yaml::to_string(&yaml_representation).map_err(anyhow::Error::msg)?
                };
                Ok(format!(
                    "The attestation is rooted in an {tee_name} TEE.

Attestations identifying the firmware captured in the evidence can be found here:
{firmware_provenace_link}

{firmware_hash_explaination}

The evidence describing this layer is outlined below.

{yaml_string}"
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
        let mut yaml_representation = serde_yaml::to_value(self).map_err(anyhow::Error::msg)?;
        make_reference_values_human_readable(&mut yaml_representation);
        serde_yaml::to_string(&yaml_representation).map_err(anyhow::Error::msg)
    }
}

impl HumanReadableTitle for KernelLayerData {
    fn title(&self) -> Result<String, anyhow::Error> {
        Ok("Kernel Layer".to_string())
    }
}

impl HumanReadableExplanation for KernelLayerData {
    fn description(&self) -> Result<String, anyhow::Error> {
        let kernel_provenance_link = {
            let kernel_image_digest: ArtifactDigestSha2_256 = self
                .kernel_image
                .as_ref()
                .context("unexpectedly unset kernel_image proto field")
                .and_then(|digest| {
                    ArtifactDigestSha2_256::try_from(digest).map_err(anyhow::Error::from)
                })?;
            kernel_image_digest.provenance_link()
        };
        let initial_ramdisk_provenance_link = {
            let init_ram_fs_digest: ArtifactDigestSha2_256 = self
                .init_ram_fs
                .as_ref()
                .context("unexpectedly unset init_ram_fs proto field")
                .and_then(|digest| {
                    ArtifactDigestSha2_256::try_from(digest).map_err(anyhow::Error::from)
                })?;
            init_ram_fs_digest.provenance_link()
        };
        let yaml_string = {
            let mut yaml_representation = serde_yaml::to_value(self).map_err(anyhow::Error::msg)?;
            make_evidence_human_readable(&mut yaml_representation);
            serde_yaml::to_string(&yaml_representation).map_err(anyhow::Error::msg)?
        };

        Ok(format!(
"Attestations identifying the binaries captured in the evidence in this layer can be found as outlined below.
Kernel: {kernel_provenance_link}
Initial Ramdisk: {initial_ramdisk_provenance_link}

The evidence describing the kernel layer is outlined below.

{yaml_string}"
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
        let mut yaml_representation = serde_yaml::to_value(self).map_err(anyhow::Error::msg)?;
        make_reference_values_human_readable(&mut yaml_representation);
        serde_yaml::to_string(&yaml_representation).map_err(anyhow::Error::msg)
    }
}

impl HumanReadableTitle for SystemLayerData {
    fn title(&self) -> Result<String, anyhow::Error> {
        Ok("System Layer".to_string())
    }
}

impl HumanReadableExplanation for SystemLayerData {
    fn description(&self) -> Result<String, anyhow::Error> {
        let system_image_provenance_link = {
            let system_image_digest = self
                .system_image
                .as_ref()
                .context("unexpectedly unset system_image proto field")
                .and_then(|digest| {
                    ArtifactDigestSha2_256::try_from(digest).map_err(anyhow::Error::from)
                })?;
            system_image_digest.provenance_link()
        };
        let yaml_string = {
            let mut yaml_representation = serde_yaml::to_value(self).map_err(anyhow::Error::msg)?;
            make_evidence_human_readable(&mut yaml_representation);
            serde_yaml::to_string(&yaml_representation).map_err(anyhow::Error::msg)?
        };
        Ok(format!(
            "Attestations identifying the system image captured in the evidence can be found here: {system_image_provenance_link}

The evidence describing this layer is outlined below.

{yaml_string}"
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
        let mut yaml_representation = serde_yaml::to_value(self).map_err(anyhow::Error::msg)?;
        make_reference_values_human_readable(&mut yaml_representation);
        serde_yaml::to_string(&yaml_representation).map_err(anyhow::Error::msg)
    }
}

impl HumanReadableTitle for ApplicationLayerData {
    fn title(&self) -> Result<String, anyhow::Error> {
        Ok("Application Layer".to_string())
    }
}

impl HumanReadableExplanation for ApplicationLayerData {
    fn description(&self) -> Result<String, anyhow::Error> {
        let yaml_string = {
            let mut yaml_representation = serde_yaml::to_value(self).map_err(anyhow::Error::msg)?;
            make_evidence_human_readable(&mut yaml_representation);
            serde_yaml::to_string(&yaml_representation).map_err(anyhow::Error::msg)?
        };
        Ok(format!(
            "The evidence describing the application is outlined below.

{yaml_string}"
        ))
    }
}

impl HumanReadableTitle for ApplicationLayerReferenceValues {
    fn title(&self) -> Result<String, anyhow::Error> {
        Ok("Application Layer".to_string())
    }
}

impl HumanReadableExplanation for ApplicationLayerReferenceValues {
    fn description(&self) -> Result<String, anyhow::Error> {
        let mut yaml_representation = serde_yaml::to_value(self).map_err(anyhow::Error::msg)?;
        make_reference_values_human_readable(&mut yaml_representation);
        serde_yaml::to_string(&yaml_representation).map_err(anyhow::Error::msg)
    }
}

impl HumanReadableTitle for ContainerLayerData {
    fn title(&self) -> Result<String, anyhow::Error> {
        Ok("Container Layer".to_string())
    }
}

impl HumanReadableExplanation for ContainerLayerData {
    fn description(&self) -> Result<String, anyhow::Error> {
        let yaml_string = {
            let mut yaml_representation = serde_yaml::to_value(self).map_err(anyhow::Error::msg)?;
            make_evidence_human_readable(&mut yaml_representation);
            serde_yaml::to_string(&yaml_representation).map_err(anyhow::Error::msg)?
        };
        Ok(format!(
            "The evidence describing the application is outlined below.

{yaml_string}"
        ))
    }
}

impl HumanReadableTitle for ContainerLayerReferenceValues {
    fn title(&self) -> Result<String, anyhow::Error> {
        Ok("Container Layer".to_string())
    }
}

impl HumanReadableExplanation for ContainerLayerReferenceValues {
    fn description(&self) -> Result<String, anyhow::Error> {
        let mut yaml_representation = serde_yaml::to_value(self).map_err(anyhow::Error::msg)?;
        make_reference_values_human_readable(&mut yaml_representation);
        serde_yaml::to_string(&yaml_representation).map_err(anyhow::Error::msg)
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
            "ⓘ The firmware attestation digest is the SHA2-256 hash of the SHA2-384 hash of the initial memory state taken by the AMD SoC. The original SHA2-384 hash of the initial memory is: SHA2-384:{}; it is listed as the 'initial_measurement' in the evidence of this layer.",
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
