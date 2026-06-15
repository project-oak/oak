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

use aes_gcm_siv::{
    Aes256GcmSiv, Key, Nonce,
    aead::{Aead, AeadCore, KeyInit, OsRng, Payload},
};
use anyhow::{Error, anyhow};

pub fn generate_nonce() -> Vec<u8> {
    Aes256GcmSiv::generate_nonce(&mut OsRng).to_vec()
}

/// Encrypts `message` with AES-256-GCM-SIV.
///
/// `aad` (Associated Authenticated Data) is authenticated but not encrypted.
/// Pass the blob identifier or other binding metadata here to prevent
/// ciphertext substitution attacks. Use `b""` when no binding is needed.
pub fn encrypt(key: &[u8], nonce: &[u8], message: &[u8], aad: &[u8]) -> Result<Vec<u8>, Error> {
    let key = Key::<Aes256GcmSiv>::from_slice(key);
    let cipher = Aes256GcmSiv::new(key);
    let payload = Payload { msg: message, aad };
    cipher.encrypt(Nonce::from_slice(nonce), payload).map_err(|x| anyhow!("{}", x))
}

/// Decrypts `message` with AES-256-GCM-SIV.
///
/// `aad` must match the associated data supplied during encryption, otherwise
/// the authentication tag check will fail. This binds the ciphertext to its
/// storage identity and prevents blob-swapping by an untrusted database.
pub fn decrypt(key: &[u8], nonce: &[u8], message: &[u8], aad: &[u8]) -> Result<Vec<u8>, Error> {
    let key = Key::<Aes256GcmSiv>::from_slice(key);
    let cipher = Aes256GcmSiv::new(key);
    let payload = Payload { msg: message, aad };
    cipher.decrypt(Nonce::from_slice(nonce), payload).map_err(|x| anyhow!("{}", x))
}

#[cfg(test)]
mod tests {
    use super::*;

    const TEST_KEY: [u8; 32] = [0x42; 32];

    #[test]
    fn encrypt_decrypt_roundtrip_with_aad() {
        let nonce = generate_nonce();
        let plaintext = b"secret memory content";
        let aad = b"blob-id-12345";

        let ciphertext = encrypt(&TEST_KEY, &nonce, plaintext, aad).unwrap();
        let decrypted = decrypt(&TEST_KEY, &nonce, &ciphertext, aad).unwrap();
        assert_eq!(decrypted, plaintext);
    }

    #[test]
    fn encrypt_decrypt_roundtrip_empty_aad() {
        let nonce = generate_nonce();
        let plaintext = b"secret memory content";

        let ciphertext = encrypt(&TEST_KEY, &nonce, plaintext, b"").unwrap();
        let decrypted = decrypt(&TEST_KEY, &nonce, &ciphertext, b"").unwrap();
        assert_eq!(decrypted, plaintext);
    }

    #[test]
    fn decrypt_fails_with_wrong_aad() {
        let nonce = generate_nonce();
        let plaintext = b"secret memory content";

        let ciphertext = encrypt(&TEST_KEY, &nonce, plaintext, b"blob-id-12345").unwrap();
        assert!(decrypt(&TEST_KEY, &nonce, &ciphertext, b"blob-id-99999").is_err());
    }

    #[test]
    fn decrypt_with_aad_fails_when_encrypted_without_aad() {
        let nonce = generate_nonce();
        let plaintext = b"secret memory content";

        // Legacy blob: encrypted with empty AAD.
        let ciphertext = encrypt(&TEST_KEY, &nonce, plaintext, b"").unwrap();
        // Attempting to decrypt with a blob-id AAD must fail.
        assert!(decrypt(&TEST_KEY, &nonce, &ciphertext, b"blob-id-12345").is_err());
    }

    #[test]
    fn decrypt_without_aad_fails_when_encrypted_with_aad() {
        let nonce = generate_nonce();
        let plaintext = b"secret memory content";

        let ciphertext = encrypt(&TEST_KEY, &nonce, plaintext, b"blob-id-12345").unwrap();
        // Stripping AAD must fail — prevents downgrade.
        assert!(decrypt(&TEST_KEY, &nonce, &ciphertext, b"").is_err());
    }

    /// Core security property: swapping ciphertext between two blob IDs is
    /// detected by the authentication tag.
    #[test]
    fn blob_swap_prevented_by_aad() {
        let nonce_a = generate_nonce();
        let nonce_b = generate_nonce();
        let blob_id_a = b"blob-a";
        let blob_id_b = b"blob-b";

        let ct_a = encrypt(&TEST_KEY, &nonce_a, b"health data", blob_id_a).unwrap();
        let ct_b = encrypt(&TEST_KEY, &nonce_b, b"email config", blob_id_b).unwrap();

        // Swap: decrypt blob A's ciphertext with blob B's ID → must fail.
        assert!(decrypt(&TEST_KEY, &nonce_a, &ct_a, blob_id_b).is_err());
        assert!(decrypt(&TEST_KEY, &nonce_b, &ct_b, blob_id_a).is_err());

        // Correct AADs still work.
        assert_eq!(decrypt(&TEST_KEY, &nonce_a, &ct_a, blob_id_a).unwrap(), b"health data");
        assert_eq!(decrypt(&TEST_KEY, &nonce_b, &ct_b, blob_id_b).unwrap(), b"email config");
    }

    /// Validates the decrypt_blob fallback path: a legacy blob (empty AAD)
    /// fails the primary AAD-bound attempt but succeeds on the empty-AAD
    /// fallback.
    #[test]
    fn legacy_fallback_decrypt_succeeds() {
        let nonce = generate_nonce();
        let plaintext = b"legacy memory content";
        let blob_id = b"blob-id-12345";

        // Legacy blob encrypted with empty AAD.
        let ciphertext = encrypt(&TEST_KEY, &nonce, plaintext, b"").unwrap();

        // Primary attempt with blob_id AAD fails.
        assert!(decrypt(&TEST_KEY, &nonce, &ciphertext, blob_id).is_err());

        // Fallback with empty AAD succeeds.
        let fallback = decrypt(&TEST_KEY, &nonce, &ciphertext, b"").unwrap();
        assert_eq!(fallback, plaintext);
    }

    /// A blob encrypted with AAD decrypts on the primary attempt and does
    /// not need the fallback path.
    #[test]
    fn new_format_does_not_need_fallback() {
        let nonce = generate_nonce();
        let plaintext = b"new format memory";
        let blob_id = b"blob-id-12345";

        let ciphertext = encrypt(&TEST_KEY, &nonce, plaintext, blob_id).unwrap();
        assert_eq!(decrypt(&TEST_KEY, &nonce, &ciphertext, blob_id).unwrap(), plaintext);
    }
}
