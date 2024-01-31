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

use zeroize::Zeroize;

use crate::oak::attestation::v1::DiceData;

impl Drop for DiceData {
    fn drop(&mut self) {
        // Zero out the ECA private key if it was set.
        if let Some(certificate_authority) = &mut self.certificate_authority {
            certificate_authority.eca_private_key.zeroize();
        }
    }
}
