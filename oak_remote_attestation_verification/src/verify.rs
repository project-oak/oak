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

//! Provides top-level verification based on evidence, endorsments and reference values.

use crate::proto::oak::attestation::v1::{
    endorsements, reference_values, CbEndorsements, CbReferenceValues, Endorsements, Evidence,
    OakContainersEndorsements, OakContainersReferenceValues, OakRestrictedKernelEndorsements,
    OakRestrictedKernelReferenceValues, ReferenceValues,
};

/// Verifies entire setup by forwarding to individual setup types.
pub fn verify(
    evidence: &Evidence,
    endorsements: &Endorsements,
    reference_values: &ReferenceValues,
) -> anyhow::Result<()> {
    verify_certificate_chain(evidence)?;

    match (
        endorsements.r#type.as_ref(),
        reference_values.r#type.as_ref(),
    ) {
        (
            Some(endorsements::Type::OakRestrictedKernel(ends)),
            Some(reference_values::Type::OakRestrictedKernel(rvs)),
        ) => verify_oak_restricted_kernel(evidence, &ends, &rvs),
        (
            Some(endorsements::Type::OakContainers(ends)),
            Some(reference_values::Type::OakContainers(rvs)),
        ) => verify_oak_containers(evidence, &ends, &rvs),
        (Some(endorsements::Type::Cb(ends)), Some(reference_values::Type::Cb(rvs))) => {
            verify_cb(evidence, &ends, &rvs)
        }
        (None, None) => anyhow::bail!("Endorsements and reference values both empty"),
        (None, Some(_)) => anyhow::bail!("Endorsements are empty"),
        (Some(_), None) => anyhow::bail!("Reference values are empty"),
        (Some(_), Some(_)) => anyhow::bail!("Mismatch between endorsements and reference values"),
    }
}

fn verify_certificate_chain(_evidence: &Evidence) -> anyhow::Result<()> {
    Ok(())
}

fn verify_oak_restricted_kernel(
    _evidence: &Evidence,
    _endorsements: &OakRestrictedKernelEndorsements,
    _reference_values: &OakRestrictedKernelReferenceValues,
) -> anyhow::Result<()> {
    Ok(())
}

fn verify_oak_containers(
    _evidence: &Evidence,
    _endorsements: &OakContainersEndorsements,
    _reference_values: &OakContainersReferenceValues,
) -> anyhow::Result<()> {
    Ok(())
}

fn verify_cb(
    _evidence: &Evidence,
    _endorsements: &CbEndorsements,
    _reference_values: &CbReferenceValues,
) -> anyhow::Result<()> {
    todo!()
}
