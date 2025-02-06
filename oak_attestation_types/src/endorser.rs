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

use oak_proto_rust::oak::attestation::v1::{Endorsements, Evidence};

/// Trait that provides the ability to read attestation endorsements.
///
/// <https://datatracker.ietf.org/doc/html/rfc9334#name-endorser-reference-value-pr>
#[cfg_attr(test, automock)]
pub trait Endorser: Send + Sync {
    /// Generate an endorsement.
    ///
    /// Evidence argument is optional since it may be required for endorsement
    /// generation in some use-cases.
    fn endorse(&self, evidence: Option<&Evidence>) -> anyhow::Result<Endorsements>;
}

/// A SimpleEndorser simply quotes the evidence that it is built with.
// #[derive(Clone)]
pub struct SimpleEndorser {
    endorsements: Endorsements,
}

impl SimpleEndorser {
    pub fn new(endorsements: Endorsements) -> Self {
        Self { endorsements }
    }
}
impl Endorser for SimpleEndorser {
    fn endorse(&self, _evidence: Option<&Evidence>) -> anyhow::Result<Endorsements> {
        Ok(self.endorsements.clone())
    }
}
