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

use alloc::{
    collections::BTreeMap,
    string::{String, ToString},
    vec::Vec,
};

use anyhow::Context;
use oak_attestation_verification_types::policy::Policy;
use oak_proto_rust::oak::{
    attestation::v1::{
        ContainerEndorsement, ContainerLayerData, ContainerLayerReferenceValues,
        EventAttestationResults,
    },
    Variant,
};

use crate::{
    compare::compare_container_layer_measurement_digests,
    expect::acquire_container_event_expected_values,
    policy::{ENCRYPTION_PUBLIC_KEY_ID, SESSION_BINDING_PUBLIC_KEY_ID, SIGNING_PUBLIC_KEY_ID},
    util::decode_event_proto,
};

pub struct ContainerPolicy {
    reference_values: ContainerLayerReferenceValues,
}

impl ContainerPolicy {
    pub fn new(reference_values: &ContainerLayerReferenceValues) -> Self {
        Self { reference_values: reference_values.clone() }
    }
}

// We have to use [`Policy<[u8], Variant>`] instead of [`EventPolicy`], because
// Rust doesn't yet support implementing trait aliases.
// <https://github.com/rust-lang/rfcs/blob/master/text/1733-trait-alias.md>
impl Policy<[u8], Variant> for ContainerPolicy {
    fn verify(
        &self,
        encoded_event: &[u8],
        encoded_endorsement: &Variant,
        milliseconds_since_epoch: i64,
    ) -> anyhow::Result<EventAttestationResults> {
        let event = decode_event_proto::<ContainerLayerData>(
            "type.googleapis.com/oak.attestation.v1.ContainerLayerData",
            encoded_event,
        )?;
        let endorsement: ContainerEndorsement =
            encoded_endorsement.try_into().map_err(anyhow::Error::msg)?;

        let expected_values = acquire_container_event_expected_values(
            milliseconds_since_epoch,
            Some(&endorsement),
            &self.reference_values,
        )
        .context("couldn't verify container endorsements")?;

        compare_container_layer_measurement_digests(&event, &expected_values)
            .context("couldn't verify container event")?;

        let artifacts = [
            (ENCRYPTION_PUBLIC_KEY_ID.to_string(), event.encryption_public_key.to_vec()),
            (SIGNING_PUBLIC_KEY_ID.to_string(), event.signing_public_key.to_vec()),
            (SESSION_BINDING_PUBLIC_KEY_ID.to_string(), event.session_binding_public_key.to_vec()),
        ]
        .into_iter()
        .collect::<BTreeMap<String, Vec<u8>>>();

        // TODO: b/356631062 - Return detailed attestation results.
        Ok(EventAttestationResults { artifacts })
    }
}
