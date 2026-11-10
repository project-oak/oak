//
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

use anyhow::Context;
use encryption::{decrypt, encrypt, generate_nonce};
use rand::Rng;
use sealed_memory_rust_proto::prelude::v1::*;
use zeroize::Zeroizing;

pub(crate) const DEK_LENGTH_BYTES: usize = 32;

pub(crate) fn generate_dek() -> Zeroizing<Vec<u8>> {
    let mut dek = Zeroizing::new(vec![0u8; DEK_LENGTH_BYTES]);
    rand::rng().fill(dek.as_mut_slice());
    dek
}

pub(crate) fn wrap_dek(dek: &[u8], kek: &[u8]) -> anyhow::Result<EncryptedDataBlob> {
    let nonce = generate_nonce();
    let data = encrypt(kek, &nonce, dek, b"").context("encrypting DEK with KEK")?;
    Ok(EncryptedDataBlob { nonce, data })
}

pub(crate) fn unwrap_dek(
    wrapped_dek: &EncryptedDataBlob,
    kek: &[u8],
) -> anyhow::Result<Zeroizing<Vec<u8>>> {
    let decrypted = decrypt(kek, &wrapped_dek.nonce, &wrapped_dek.data, b"")
        .context("decrypting wrapped DEK with KEK")?;
    Ok(Zeroizing::new(decrypted))
}

pub(crate) fn create_plain_text_user_info(
    key_derivation_info: Option<KeyDerivationInfo>,
    wrapped_dek: EncryptedDataBlob,
) -> PlainTextUserInfo {
    PlainTextUserInfo {
        key_derivation_info,
        wrapped_dek: Some(WrappedDataEncryptionKey { wrapped_key: Some(wrapped_dek) }),
    }
}

pub(crate) fn wrapped_dek(
    plain_text_info: &PlainTextUserInfo,
) -> anyhow::Result<&EncryptedDataBlob> {
    plain_text_info
        .wrapped_dek
        .as_ref()
        .context("missing wrapped_dek")?
        .wrapped_key
        .as_ref()
        .context("missing wrapped_dek")
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_generate_and_wrap_unwrap_dek() {
        let kek = vec![0x42u8; 32];
        let dek = generate_dek();
        assert_eq!(dek.len(), DEK_LENGTH_BYTES);

        let wrapped = wrap_dek(&dek, &kek).expect("wrap failed");
        let unwrapped = unwrap_dek(&wrapped, &kek).expect("unwrap failed");
        assert_eq!(*dek, *unwrapped);
    }

    #[test]
    fn test_plain_text_user_info_roundtrip() {
        let kek = vec![0x42u8; 32];
        let dek = generate_dek();
        let wrapped = wrap_dek(&dek, &kek).expect("wrap failed");

        let key_derivation_info =
            KeyDerivationInfo { kek_version: 1, kek_salt: b"test_salt".to_vec() };

        let user_info = create_plain_text_user_info(Some(key_derivation_info.clone()), wrapped);
        assert_eq!(user_info.key_derivation_info, Some(key_derivation_info));

        let unwrapped = unwrap_dek(wrapped_dek(&user_info).expect("extract failed"), &kek)
            .expect("unwrap failed");
        assert_eq!(*dek, *unwrapped);
    }

    #[test]
    fn test_unwrap_with_wrong_kek_fails() {
        let kek = vec![0x42u8; 32];
        let wrong_kek = vec![0x43u8; 32];
        let dek = generate_dek();
        let wrapped = wrap_dek(&dek, &kek).expect("wrap failed");
        assert!(unwrap_dek(&wrapped, &wrong_kek).is_err());
    }

    #[test]
    fn test_wrapped_dek_missing_is_an_error() {
        let info = PlainTextUserInfo { key_derivation_info: None, wrapped_dek: None };
        assert!(wrapped_dek(&info).is_err());
    }
}
