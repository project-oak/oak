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

use hkdf::Hkdf;
use hmac::{Hmac, Mac};
use sha2::Sha256;

// Define the length for the derived Key Encryption Key (KEK).
// 32 bytes = 256 bits, a common size for keys.
const KEK_LENGTH: usize = 32;

/// Derives a Key Encryption Key (KEK) using HKDF.
///
/// # Arguments
/// * `user_secret` - The master secret for the user.
/// * `kek_version` - An integer version for the key, used as 'info' in HKDF.
/// * `salt` - A salt value for HKDF.
///
/// # Returns
/// A byte array representing the derived KEK.
pub fn derive_kek(user_secret: &[u8], kek_version: i32, salt: &[u8]) -> Vec<u8> {
    let info_bytes = kek_version.to_be_bytes();
    let hk = Hkdf::<Sha256>::new(Some(&info_bytes), user_secret);

    let mut okm = vec![0u8; KEK_LENGTH];

    hk.expand(salt, &mut okm).expect("Failed to expand HKDF; OKM length should be valid.");

    okm
}

/// Derives a Private Memory User ID (pm_uid) using HMAC-SHA-256.
///
/// # Arguments
/// * `user_secret` - The master secret for the user.
///
/// # Returns
/// The string representation of the derived pm_uid.
pub fn derive_pm_uid(user_secret: &[u8]) -> String {
    let mut mac = Hmac::<Sha256>::new_from_slice(user_secret)
        .expect("Failed to create HMAC instance; user_secret should be a valid key.");

    mac.update(b"sealed_memory");
    // Encode to hex.
    hex::encode(mac.finalize().into_bytes())
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_derive_pm_uid() {
        let user_secret = b"this_is_a_test_secret_for_pm_uid";
        let pm_uid = derive_pm_uid(user_secret);
        let expected_pm_uid = "04f91762ea6f39f8c05eafc6e010bc53bd3fbbe5a3ad3c195b6f6c2a7567d409";
        assert_eq!(pm_uid.len(), 64);
        assert_eq!(pm_uid, expected_pm_uid);
    }

    #[test]
    fn test_derive_key() {
        let user_secret = b"this_is_a_test_secret_for_kek";
        let kek_version = 0;
        let salt = b"this_is_a_random_salt_value"; // In practice, this should be random

        // Ground truth for the expected KEK.
        let kek = derive_kek(user_secret, kek_version, salt);
        let expected_kek = b"07e74310625314a3c780305ddc89907091abcec1bf2a537117017a2b8cd43fab";
        assert_eq!(kek.len(), KEK_LENGTH);
        assert_eq!(kek, hex::decode(expected_kek).unwrap());

        // Deriving with a different version should produce a different key
        let kek_v1 = derive_kek(user_secret, 1, salt);
        assert_ne!(kek, kek_v1, "KEKs from different versions should not match");

        // Deriving with a different salt should produce a different key
        let salt_v2 = b"another_random_salt_value";
        let kek_s2 = derive_kek(user_secret, kek_version, salt_v2);
        assert_ne!(kek, kek_s2, "KEKs from different salts should not match");
    }
}
