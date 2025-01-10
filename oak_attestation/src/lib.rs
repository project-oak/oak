//
// Copyright 2022 The Project Oak Authors
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

#![no_std]

extern crate alloc;

use dice::LayerData;
use oak_proto_rust::oak::attestation::v1::Evidence;
use p256::ecdsa::VerifyingKey;

pub mod dice;

/// Deprecated trait that allow for explicitly adding application keys to the
/// attestation evidence.
#[deprecated = "Use application keys from the event log."]
pub trait ApplicationKeysAttester {
    // TODO: b/368030563 - Remove this trait once all client library instances use
    // the applications keys from the event log.

    /// Adds certificates representing the application keys to the attestation
    /// evidence.
    //
    /// This is an outdated approach that has been replaced by adding the
    /// applications keys to the event log. It is only retained for
    /// compatibility while some client deployments still expect this format.
    fn add_application_keys(
        self,
        layer_data: LayerData,
        kem_public_key: &[u8],
        verifying_key: &VerifyingKey,
        group_kem_public_key: Option<&[u8]>,
        group_verifying_key: Option<&VerifyingKey>,
    ) -> anyhow::Result<Evidence>;
}
