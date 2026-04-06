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

use alloc::{string::ToString, vec::Vec};

/// Calculates the Pre-Authentication Encoding (PAE) for a PES confirmation.
///
/// The PAE is a canonical byte string used to ensure that the signer and
/// verifier are looking at the exact same data.
pub fn calculate(
    endorsement_bytes: &[u8],
    endorser_key_der: &[u8],
    endorser_signature: &[u8],
    entry_id: &str,
) -> Vec<u8> {
    let mut pae = Vec::new();
    pae.extend_from_slice(b"PES");

    pae.extend_from_slice(&encode(endorsement_bytes));
    pae.extend_from_slice(&encode(endorser_key_der));
    pae.extend_from_slice(&encode(endorser_signature));
    pae.extend_from_slice(&encode(entry_id.as_bytes()));

    pae
}

/// Implements the length-prefixed encoding: SP + LEN(obj) + SP + obj
fn encode(obj: &[u8]) -> Vec<u8> {
    let mut encoded = Vec::new();
    encoded.push(b' ');
    encoded.extend_from_slice(obj.len().to_string().as_bytes());
    encoded.push(b' ');
    encoded.extend_from_slice(obj);
    encoded
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_encode() {
        assert_eq!(encode(b"foo"), b" 3 foo");
        assert_eq!(encode(b""), b" 0 ");
        assert_eq!(encode(&[1, 2, 3]), b" 3 \x01\x02\x03");
    }

    #[test]
    fn test_calculate_pae() {
        let endorsement = b"stmt";
        let key = b"key";
        let sig = b"sig";
        let entry_id = "id";

        let pae = calculate(endorsement, key, sig, entry_id);

        // Expected: "PES" + " 4 stmt" + " 3 key" + " 3 sig" + " 2 id"
        let expected = b"PES 4 stmt 3 key 3 sig 2 id";
        assert_eq!(pae, expected);
    }
}
