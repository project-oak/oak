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

use anyhow::Context;
use oak_proto_rust::oak::crypto::v1::Signature;

pub trait Verifier {
    fn verify(&self, message: &[u8], signature: &Signature) -> anyhow::Result<()>;
}

impl Verifier for p256::ecdsa::VerifyingKey {
    fn verify(&self, message: &[u8], signature: &Signature) -> anyhow::Result<()> {
        let parsed_signature = p256::ecdsa::Signature::from_slice(&signature.signature)
            .map_err(anyhow::Error::msg)
            .context("could not parse signature")?;
        <p256::ecdsa::VerifyingKey as p256::ecdsa::signature::Verifier<
            p256::ecdsa::Signature,
        >>::verify(self, message, &parsed_signature).map_err(anyhow::Error::msg)
    }
}

#[allow(unused)]
struct VerifierKeyHandle {
    inner: p256::ecdsa::VerifyingKey,
}

impl Verifier for VerifierKeyHandle {
    fn verify(&self, message: &[u8], signature: &Signature) -> anyhow::Result<()> {
        self.inner.verify(message, signature)
    }
}
