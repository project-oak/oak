//
// Copyright 2021 The Project Oak Authors
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

use crate::proto::AttestationReport;

// TODO(#2842): Generate the remote attestation report from hardware.
const TEST_TEE_MEASUREMENT: &str = "Test TEE measurement";

impl AttestationReport {
    /// Placeholder function for collecting TEE measurement of remotely attested TEEs.
    pub fn new(data: &[u8]) -> Self {
        Self {
            measurement: TEST_TEE_MEASUREMENT.as_bytes().to_vec(),
            data: data.to_vec(),
            ..Default::default()
        }
    }
}
