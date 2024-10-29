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

use anyhow::Context;
use oak_proto_rust::oak::session::v1::{PlaintextMessage, SessionRequest, SessionResponse};
use oak_session::{ProtocolEngine, ServerSession, Session};

/// These session helpers should eventually move into the SDK.
pub trait ServerSessionHelpers {
    fn decrypt_request(&mut self, session_request: &SessionRequest) -> anyhow::Result<Vec<u8>>;
    fn encrypt_response(&mut self, response: &[u8]) -> anyhow::Result<SessionResponse>;
    fn init_session(
        &mut self,
        session_request: &SessionRequest,
    ) -> anyhow::Result<Option<SessionResponse>>;
}

impl ServerSessionHelpers for ServerSession {
    fn decrypt_request(&mut self, session_request: &SessionRequest) -> anyhow::Result<Vec<u8>> {
        self.put_incoming_message(session_request).context("failed to put request")?;
        Ok(self
            .read()
            .context("failed to read decrypted message")?
            .ok_or_else(|| anyhow::anyhow!("empty plaintext response"))?
            .plaintext)
    }

    fn encrypt_response(&mut self, response: &[u8]) -> anyhow::Result<SessionResponse> {
        self.write(&PlaintextMessage { plaintext: response.to_vec() })
            .context("failed to write response")?;
        self.get_outgoing_message()
            .context("failed get get encrypted response")?
            .ok_or_else(|| anyhow::anyhow!("empty encrypted response"))
    }

    fn init_session(
        &mut self,
        session_request: &SessionRequest,
    ) -> anyhow::Result<Option<SessionResponse>> {
        self.put_incoming_message(session_request).context("failed to put request")?;
        self.get_outgoing_message().context("failed to get outgoing messge")
    }
}
