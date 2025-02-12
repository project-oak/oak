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
//

use oak_attestation_types::endorser::Endorser;
use oak_proto_rust::oak::attestation::v1::{Endorsements, Evidence};

/// A simple [`Endorser`] instance that provides a single unchanging endorsement
/// set, regardless of the provided evidence.
pub struct StaticEndorser {
    endorsements: Endorsements,
}

impl StaticEndorser {
    /// Create a new instance that always returns the provided [`Endorsements`].
    pub fn new(endorsements: Endorsements) -> Self {
        Self { endorsements }
    }
}
impl Endorser for StaticEndorser {
    /// Returns the [`Endorsements`] provided at construction.
    ///
    /// The `evidence` argument is ignored.
    fn endorse(&self, _evidence: Option<&Evidence>) -> anyhow::Result<Endorsements> {
        Ok(self.endorsements.clone())
    }
}
