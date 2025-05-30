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
/// A `Vec<u8>` containing the derived KEK.
pub fn derive_kek(user_secret: &[u8], kek_version: i32, salt: &[u8]) -> Vec<u8> {
    let hk = Hkdf::<Sha256>::new(Some(salt), user_secret);

    let mut okm = vec![0u8; KEK_LENGTH];

    let info_bytes = kek_version.to_be_bytes();

    hk.expand(&info_bytes, &mut okm).expect("Failed to expand HKDF; OKM length should be valid.");

    okm
}

/// Derives a Private Memory User ID (pm_uid) using HMAC-SHA-256.
///
/// # Arguments
/// * `user_secret` - The master secret for the user.
///
/// # Returns
/// A `Vec<u8>` containing the derived pm_uid.
pub fn derive_pm_uid(user_secret: &[u8]) -> Vec<u8> {
    let mut mac = Hmac::<Sha256>::new_from_slice(user_secret)
        .expect("Failed to create HMAC instance; user_secret should be a valid key.");

    mac.update(b"sealed_memory");

    mac.finalize().into_bytes().to_vec()
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_derive_pm_uid() {
        let user_secret = b"this_is_a_test_secret_for_pm_uid";
        let pm_uid = derive_pm_uid(user_secret);
        let expected_pm_uid = b"04f91762ea6f39f8c05eafc6e010bc53bd3fbbe5a3ad3c195b6f6c2a7567d409";
        println!("Derived PM UID (hex): {}", hex::encode(&pm_uid));
        assert_eq!(pm_uid.len(), 32);
        let expected_pm_uid = hex::decode(expected_pm_uid).unwrap();
        assert_eq!(pm_uid, expected_pm_uid);
    }

    #[test]
    fn test_derive_key() {
        let user_secret = b"this_is_a_test_secret_for_kek";
        let kek_version = 0;
        let salt = b"this_is_a_random_salt_value"; // In practice, this should be random

        let kek = derive_kek(user_secret, kek_version, salt);
        println!("Derived KEK (hex): {}", hex::encode(&kek));
        assert_eq!(kek.len(), KEK_LENGTH);

        // Deriving with a different version should produce a different key
        let kek_v1 = derive_kek(user_secret, 1, salt);
        assert_ne!(kek, kek_v1, "KEKs from different versions should not match");

        // Deriving with a different salt should produce a different key
        let salt_v2 = b"another_random_salt_value";
        let kek_s2 = derive_kek(user_secret, kek_version, salt_v2);
        assert_ne!(kek, kek_s2, "KEKs from different salts should not match");
    }
}
