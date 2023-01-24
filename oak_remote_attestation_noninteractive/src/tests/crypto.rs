//
// Copyright 2023 The Project Oak Authors
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

use crate::crypto::{
    ClientCryptoProvider, EnclaveCryptoProvider, serialize_public_key, deserialize_public_key,
    HYBRID_ENCRYPTION_SCHEME, SYMMETRIC_ENCRYPTION_SCHEME
};
use assert_matches::assert_matches;

const TEST_REQUEST: [u8; 5] = [0, 1, 2, 3, 4];
const TEST_RESPONSE: [u8; 5] = [5, 6, 7, 8, 9];

#[test]
fn test_serialize_deserialize_public_key() {
    tink_hybrid::init();
    let private_key = tink_core::keyset::Handle::new(
        &HYBRID_ENCRYPTION_SCHEME()
    ).expect("couldn't create private key");
    let public_key = private_key.public().expect("couldn't get public key");

    let result = serialize_public_key(&public_key);
    assert_matches!(result, Ok(_));
    let serialized_public_key = result.unwrap();

    let result = deserialize_public_key(&serialized_public_key);
    assert_matches!(result, Ok(_));
}

#[test]
fn test_serialize_deserialize_symmetric_key() {
    tink_hybrid::init();
    let symmetric_key = tink_core::keyset::Handle::new(
        &SYMMETRIC_ENCRYPTION_SCHEME()
    ).expect("couldn't create symmetric key");

    let result = serialize_public_key(&symmetric_key);
    assert_matches!(result, Ok(_));
    let serialized_symmetric_key = result.unwrap();

    let result = deserialize_public_key(&serialized_symmetric_key);
    assert_matches!(result, Ok(_));
}

#[test]
fn test_create_client_crypto_provider() {
    tink_hybrid::init();
    let result = EnclaveCryptoProvider::create();
    assert!(result.is_ok());
    let enclave_crypto_provider = result.unwrap();

    let result = enclave_crypto_provider.get_public_key();
    assert!(result.is_ok());
    let public_key = result.unwrap();

    let result = ClientCryptoProvider::create(&public_key);
    assert!(result.is_ok());
}


#[test]
fn test_hybrid_encryption() {
    tink_hybrid::init();
    let enclave_crypto_provider = EnclaveCryptoProvider::create().unwrap();
    let public_key = enclave_crypto_provider.get_public_key().unwrap();
    let client_crypto_provider = ClientCryptoProvider::create(&public_key).unwrap();

    let client_encryptor = client_crypto_provider.get_encryptor();
    let encrypted_request = client_encryptor
}

// fn main() {
//     let client_encryptor = ClientEncryptor::new(enclave_public_key);

//     let (encrypted_request, decryptor) = encryptor
//         .encrypt(request_body)
//         .context("couldn't encrypt request")?;
//     let encrypted_response = self
//         .transport
//         .invoke(encrypted_request)
//         .context("couldn't send request")?;
//     let response = decryptor
//         .decrypt(encrypted_response)
//         .context("couldn't decrypt response")?;
//     Ok(response)
// }

