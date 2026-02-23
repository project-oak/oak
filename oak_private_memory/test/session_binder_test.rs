//
// Copyright 2026 The Project Oak Authors
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

use async_trait::async_trait;
use oak_session::session_binding::SessionBinder;
use private_memory_server_lib::session_binder::{OrchestratorSessionBinder, OrchestratorSigner};
use prost::Message;
use sealed_memory_rust_proto::oak::private_memory::SessionBinding;

struct MockOrchestratorSigner;

#[async_trait]
impl OrchestratorSigner for MockOrchestratorSigner {
    async fn sign(&mut self, message: &[u8]) -> anyhow::Result<Vec<u8>> {
        // Just return the message prefixed with "signed-"
        let mut signed = b"signed-".to_vec();
        signed.extend_from_slice(message);
        Ok(signed)
    }
}

#[tokio::test]
async fn test_orchestrator_session_binder() {
    let mock_client = MockOrchestratorSigner;
    let binder =
        OrchestratorSessionBinder::create(mock_client).await.expect("failed to create binder");

    let bound_data = b"handshake-transcript";
    let binding_bytes = binder.bind(bound_data);

    let binding =
        SessionBinding::decode(binding_bytes.as_slice()).expect("failed to decode binding");

    assert!(!binding.signature.is_empty());
    assert!(!binding.public_key.is_empty());
    assert!(binding.public_key_signature.starts_with(b"signed-"));
    assert_eq!(binding.public_key_signature, [b"signed-", binding.public_key.as_slice()].concat());
}
