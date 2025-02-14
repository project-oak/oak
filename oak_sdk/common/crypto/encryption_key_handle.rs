//
// Copyright 2025 The Project Oak Authors
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

use oak_crypto::{
    encryption_key::{AsyncEncryptionKeyHandle, EncryptionKey},
    hpke::RecipientContext,
};

/// A simple AsyncEncryptionKeyHandle that generates a new key based on a static
/// key provided at creation.
pub struct StaticEncryptionKeyHandle {
    encryption_key: EncryptionKey,
}

impl StaticEncryptionKeyHandle {
    pub fn new(encryption_key: EncryptionKey) -> Self {
        Self { encryption_key }
    }
}

#[async_trait::async_trait]
impl AsyncEncryptionKeyHandle for StaticEncryptionKeyHandle {
    async fn generate_recipient_context(
        &self,
        encapsulated_public_key: &[u8],
    ) -> anyhow::Result<RecipientContext> {
        self.encryption_key.generate_recipient_context(encapsulated_public_key).await
    }
}
