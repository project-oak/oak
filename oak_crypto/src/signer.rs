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

use oak_proto_rust::oak::crypto::v1::Signature;

pub trait Signer {
    fn sign(&self, message: &[u8]) -> Signature;
}

impl Signer for p256::ecdsa::SigningKey {
    fn sign(&self, message: &[u8]) -> Signature {
        let signature = <p256::ecdsa::SigningKey as p256::ecdsa::signature::Signer<
            p256::ecdsa::Signature,
        >>::sign(self, message)
        .to_vec();
        Signature { signature }
    }
}
