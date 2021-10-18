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

use crate::{
    crypto::{
        KEY_AGREEMENT_ALGORITHM_KEY_LENGTH, NONCE_LENGTH, SIGNATURE_LENGTH,
        SIGNING_ALGORITHM_KEY_LENGTH,
    },
    message::{
        deserialize_message, ClientHello, ClientIdentity, Deserializable, EncryptedData,
        MessageWrapper, Serializable, ServerIdentity, CLIENT_HELLO_HEADER, CLIENT_IDENTITY_HEADER,
        MAXIMUM_MESSAGE_SIZE, REPLAY_PROTECTION_ARRAY_LENGTH, SERVER_IDENTITY_HEADER,
    },
};
use anyhow::{anyhow, Context};
use assert_matches::assert_matches;
use quickcheck::{quickcheck, TestResult};

pub const INVALID_MESSAGE_HEADER: u8 = 5;
const INVALID_PROTOCOL_VERSION: u8 = 2;

/// Creates a zero initialized array.
fn default_array<T, const L: usize>() -> [T; L]
where
    T: std::marker::Copy + std::default::Default,
{
    [Default::default(); L]
}

/// Converts slices to arrays (expands with zeroes).
fn to_array<T, const L: usize>(input: &[T]) -> anyhow::Result<[T; L]>
where
    T: std::marker::Copy + std::default::Default,
{
    if input.len() <= L {
        // `Default` is only implemented for a limited number of array sizes.
        // https://doc.rust-lang.org/std/primitive.array.html#impl-Default
        let mut result: [T; L] = default_array();
        result[..input.len()].copy_from_slice(&input[..input.len()]);
        Ok(result)
    } else {
        Err(anyhow!(
            "Maximum input length exceeded, maximum {}, found {}",
            L,
            input.len()
        ))
    }
}

fn test_serialize_template<M: Serializable + Deserializable + PartialEq>(
    message: &M,
) -> anyhow::Result<bool> {
    let serialized_message = message.serialize().context("Couldn't serialize message")?;
    let deserialized_message =
        M::deserialize(&serialized_message).context("Couldn't deserialize message")?;
    Ok(*message == deserialized_message)
}

#[test]
fn test_serialize_client_hello() {
    fn property(random: Vec<u8>) -> TestResult {
        if random.len() > REPLAY_PROTECTION_ARRAY_LENGTH {
            return TestResult::discard();
        }
        let client_hello = ClientHello::new(to_array(&random).unwrap());
        let result = test_serialize_template(&client_hello);
        assert!(result.is_ok());
        TestResult::from_bool(result.unwrap())
    }
    // `quickcheck` creates multiple random inputs for the `property` function and checks if it
    // fails.
    // `quickcheck` requires `Testable` to be implemented:
    // https://github.com/BurntSushi/quickcheck/blob/defde6fb0ce20b0c8c4e672aa9ae821f7d1f5b38/src/tester.rs#L386-L394
    quickcheck(property as fn(Vec<u8>) -> TestResult);
}

#[test]
fn test_serialize_server_identity() {
    fn property(
        ephemeral_public_key: Vec<u8>,
        random: Vec<u8>,
        transcript_signature: Vec<u8>,
        signing_public_key: Vec<u8>,
        attestation_info: Vec<u8>,
        additional_info: Vec<u8>,
    ) -> TestResult {
        if ephemeral_public_key.len() > KEY_AGREEMENT_ALGORITHM_KEY_LENGTH
            || random.len() > REPLAY_PROTECTION_ARRAY_LENGTH
            || transcript_signature.len() > SIGNATURE_LENGTH
            || signing_public_key.len() > SIGNING_ALGORITHM_KEY_LENGTH
        {
            return TestResult::discard();
        }
        let mut server_identity = ServerIdentity::new(
            to_array(&ephemeral_public_key).unwrap(),
            to_array(&random).unwrap(),
            to_array(&signing_public_key).unwrap(),
            attestation_info,
            additional_info,
        );
        assert_eq!(server_identity.transcript_signature, default_array());

        let transcript_signature_array = to_array(&transcript_signature).unwrap();
        server_identity.set_transcript_signature(&transcript_signature_array);
        assert_eq!(
            server_identity.transcript_signature,
            transcript_signature_array
        );

        let result = test_serialize_template(&server_identity);
        assert!(result.is_ok());

        server_identity.clear_transcript_signature();
        assert_eq!(server_identity.transcript_signature, default_array());

        let result = test_serialize_template(&server_identity);
        assert!(result.is_ok());
        TestResult::from_bool(result.unwrap())
    }
    quickcheck(property as fn(Vec<u8>, Vec<u8>, Vec<u8>, Vec<u8>, Vec<u8>, Vec<u8>) -> TestResult);
}

#[test]
fn test_serialize_client_identity() {
    fn property(
        ephemeral_public_key: Vec<u8>,
        transcript_signature: Vec<u8>,
        signing_public_key: Vec<u8>,
        attestation_info: Vec<u8>,
    ) -> TestResult {
        if ephemeral_public_key.len() > KEY_AGREEMENT_ALGORITHM_KEY_LENGTH
            || transcript_signature.len() > SIGNATURE_LENGTH
            || signing_public_key.len() > SIGNING_ALGORITHM_KEY_LENGTH
        {
            return TestResult::discard();
        }
        let mut client_identity = ClientIdentity::new(
            to_array(&ephemeral_public_key).unwrap(),
            to_array(&signing_public_key).unwrap(),
            attestation_info,
        );
        assert_eq!(client_identity.transcript_signature, default_array(),);

        let transcript_signature_array = to_array(&transcript_signature).unwrap();
        client_identity.set_transcript_signature(&transcript_signature_array);
        assert_eq!(
            client_identity.transcript_signature,
            transcript_signature_array
        );

        let result = test_serialize_template(&client_identity);
        assert!(result.is_ok());

        client_identity.clear_transcript_signature();
        assert_eq!(client_identity.transcript_signature, default_array());

        TestResult::from_bool(result.unwrap())
    }
    quickcheck(property as fn(Vec<u8>, Vec<u8>, Vec<u8>, Vec<u8>) -> TestResult);
}

#[test]
fn test_serialize_encrypted_data() {
    fn property(nonce: Vec<u8>, data: Vec<u8>) -> TestResult {
        if nonce.len() > NONCE_LENGTH {
            return TestResult::discard();
        }
        let encrypted_data = EncryptedData::new(to_array(&nonce).unwrap(), data);
        let result = test_serialize_template(&encrypted_data);
        assert!(result.is_ok());
        TestResult::from_bool(result.unwrap())
    }
    quickcheck(property as fn(Vec<u8>, Vec<u8>) -> TestResult);
}

#[test]
fn test_deserialize_message() {
    let client_hello = ClientHello::new(default_array());
    let deserialized_client_hello = deserialize_message(&client_hello.serialize().unwrap());
    assert_matches!(deserialized_client_hello, Ok(_));
    assert_eq!(
        deserialized_client_hello.unwrap(),
        MessageWrapper::ClientHello(client_hello)
    );

    let server_identity = ServerIdentity::new(
        default_array(),
        default_array(),
        default_array(),
        vec![],
        vec![],
    );
    let deserialized_server_identity = deserialize_message(&server_identity.serialize().unwrap());
    assert_matches!(deserialized_server_identity, Ok(_));
    assert_eq!(
        deserialized_server_identity.unwrap(),
        MessageWrapper::ServerIdentity(server_identity)
    );

    let client_identity = ClientIdentity::new(default_array(), default_array(), vec![]);
    let deserialized_client_identity = deserialize_message(&client_identity.serialize().unwrap());
    assert_matches!(deserialized_client_identity, Ok(_));
    assert_eq!(
        deserialized_client_identity.unwrap(),
        MessageWrapper::ClientIdentity(client_identity)
    );

    let encrypted_data = EncryptedData::new(default_array(), vec![]);
    let deserialized_encrypted_data = deserialize_message(&encrypted_data.serialize().unwrap());
    assert_matches!(deserialized_encrypted_data, Ok(_));
    assert_eq!(
        deserialized_encrypted_data.unwrap(),
        MessageWrapper::EncryptedData(encrypted_data)
    );

    let invalid_message = vec![INVALID_MESSAGE_HEADER];
    let deserialized_invalid_message = deserialize_message(&invalid_message);
    assert_matches!(deserialized_invalid_message, Err(_));

    let big_client_hello = [CLIENT_HELLO_HEADER; MAXIMUM_MESSAGE_SIZE + 1];
    let deserialized_big_client_hello = deserialize_message(&big_client_hello);
    assert_matches!(deserialized_big_client_hello, Err(_));

    let big_server_identity = [SERVER_IDENTITY_HEADER; MAXIMUM_MESSAGE_SIZE + 1];
    let deserialized_big_server_identity = deserialize_message(&big_server_identity);
    assert_matches!(deserialized_big_server_identity, Err(_));

    let mut invalid_server_identity = [SERVER_IDENTITY_HEADER; MAXIMUM_MESSAGE_SIZE];
    invalid_server_identity[1] = INVALID_PROTOCOL_VERSION;
    let deserialized_invalid_server_identity = deserialize_message(&invalid_server_identity);
    assert_matches!(deserialized_invalid_server_identity, Err(_));

    let big_client_identity = [CLIENT_IDENTITY_HEADER; MAXIMUM_MESSAGE_SIZE + 1];
    let deserialized_big_client_identity = deserialize_message(&big_client_identity);
    assert_matches!(deserialized_big_client_identity, Err(_));

    let big_encrypted_data =
        EncryptedData::new([0; NONCE_LENGTH], vec![0; MAXIMUM_MESSAGE_SIZE + 1])
            .serialize()
            .unwrap();
    let deserialized_big_encrypted_data = deserialize_message(&big_encrypted_data);
    assert_matches!(deserialized_big_encrypted_data, Ok(_));
}
