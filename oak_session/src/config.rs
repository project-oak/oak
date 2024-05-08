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

use crate::attestation::{AttestationVerifier, Attester};

#[derive(Default)]
pub struct SessionConfig<'a> {
    self_attester: Option<&'a dyn Attester>,
    peer_verifier: Option<&'a dyn AttestationVerifier>,
}

impl<'a> SessionConfig<'a> {
    pub fn builder() -> SessionConfigBuilder<'a> {
        SessionConfigBuilder::default()
    }
}

#[derive(Default)]
pub struct SessionConfigBuilder<'a> {
    config: SessionConfig<'a>,
}

impl<'a> SessionConfigBuilder<'a> {
    pub fn set_self_attester(mut self, self_attester: &'a dyn Attester) -> Self {
        if self.config.self_attester.is_none() {
            self.config.self_attester = Some(self_attester);
        } else {
            panic!("self attester has already been set");
        }
        self
    }

    pub fn set_peer_verifier(mut self, peer_verifier: &'a dyn AttestationVerifier) -> Self {
        if self.config.peer_verifier.is_none() {
            self.config.peer_verifier = Some(peer_verifier);
        } else {
            panic!("peer verifier has already been set");
        }
        self
    }

    pub fn build(self) -> SessionConfig<'a> {
        self.config
    }
}
