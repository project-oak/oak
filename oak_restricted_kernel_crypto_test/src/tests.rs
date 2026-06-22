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

//! Integration test exercising AEAD crypto operations inside a Restricted
//! Kernel enclave against Wycheproof test vectors.
//!
//! The test launches a Restricted Kernel VM running an enclave app that
//! implements the [`service::oak::crypto_test::Aead`] micro_rpc service,
//! then sends encrypt/decrypt requests for each test vector and verifies
//! that the results match.
//!
//! The test sends **all** vectors to the enclave app, including those with
//! parameter combinations that the current implementation may not support
//! (e.g. non-96-bit nonces). When the enclave app returns
//! [`micro_rpc::StatusCode::Unimplemented`], the vector is counted as
//! "skipped". This keeps the test generic: a different enclave app that
//! supports wider parameter ranges will automatically exercise more vectors.
//!
//! # Wycheproof test vector format
//!
//! The JSON structure is documented at
//! <https://github.com/google/wycheproof/blob/master/doc/files.md>.

use oak_file_utils::data_path;
use oak_launcher_utils::launcher;
use service::oak::crypto_test::{
    AeadAsyncClient, AeadDecryptRequest, AeadEncryptRequest, AeadEncryptResponse,
};

mod wycheproof;

use wycheproof::{AeadTestFile, TestResult};

/// Launches the enclave app and returns an AEAD async client connected to it.
///
/// Also returns the guest instance handle — the caller must keep it alive
/// for the duration of the test, since dropping it kills the QEMU process.
async fn launch_aead_enclave() -> (
    Box<dyn oak_launcher_utils::launcher::GuestInstance>,
    AeadAsyncClient<oak_launcher_utils::channel::ConnectorHandle>,
) {
    let enclave_app_path = data_path("oak_restricted_kernel_crypto_test/enclave_app/enclave_app");
    let orchestrator_path = data_path("enclave_apps/oak_orchestrator/oak_orchestrator");
    let kernel = data_path(
        "oak_restricted_kernel_wrapper/oak_restricted_kernel_wrapper_virtio_console_channel_bin",
    );
    let bios = data_path("stage0_bin/stage0_bin");

    let params = launcher::Params {
        kernel,
        vmm_binary: which::which("qemu-system-x86_64").unwrap(),
        app_binary: Some(enclave_app_path),
        bios_binary: bios,
        gdb: None,
        initrd: orchestrator_path,
        memory_size: Some("256M".to_string()),
        pci_passthrough: None,
        initial_data_version: launcher::InitialDataVersion::V1,
        communication_channel: launcher::CommunicationChannel::VirtioConsole,
        vm_type: launcher::VmType::Default,
    };

    let (guest_instance, connector_handle) =
        launcher::launch(params).await.expect("launching enclave");

    (guest_instance, AeadAsyncClient::new(connector_handle))
}

/// Returns `true` if `status` indicates that the enclave app does not support
/// the requested parameter combination.
fn is_unimplemented(status: &micro_rpc::Status) -> bool {
    status.code == micro_rpc::StatusCode::Unimplemented
}

/// The outcome of exercising a single test vector against the enclave.
enum ExerciseOutcome {
    /// The vector was exercised and validated as correct (encryption matched
    /// expected output, decryption round-tripped successfully).
    Valid,
    /// The vector was exercised and the enclave correctly rejected the
    /// tampered input.
    Invalid,
    /// The enclave does not support the requested parameter combination
    /// ([`micro_rpc::StatusCode::Unimplemented`]).
    Unsupported,
    /// The vector has [`TestResult::Acceptable`] result and was
    /// intentionally skipped (may pass or fail depending on the
    /// implementation).
    Acceptable,
}

/// A decoded AEAD test vector ready for exercising against an enclave.
struct AeadTestVector {
    /// Unique test case identifier from the Wycheproof suite.
    tc_id: u32,
    /// Encryption key.
    key: Vec<u8>,
    /// Initialization vector / nonce.
    nonce: Vec<u8>,
    /// Additional authenticated data.
    aad: Vec<u8>,
    /// Plaintext to encrypt (for valid vectors) or the original plaintext
    /// that produced the ciphertext (for verification).
    plaintext: Vec<u8>,
    /// Expected ciphertext (without the authentication tag).
    ciphertext: Vec<u8>,
    /// Expected authentication tag.
    tag: Vec<u8>,
    /// Whether the vector is valid, invalid, or acceptable, determining
    /// the exercise strategy.
    result: TestResult,
}

impl AeadTestVector {
    /// Parses a raw Wycheproof test case, hex-decoding all byte fields.
    fn parse(tc: &wycheproof::AeadTestVector) -> Self {
        Self {
            tc_id: tc.tc_id,
            key: hex::decode(&tc.key).expect("decoding key hex"),
            nonce: hex::decode(&tc.iv).expect("decoding nonce hex"),
            aad: hex::decode(&tc.aad).expect("decoding aad hex"),
            plaintext: hex::decode(&tc.msg).expect("decoding plaintext hex"),
            ciphertext: hex::decode(&tc.ct).expect("decoding ciphertext hex"),
            tag: hex::decode(&tc.tag).expect("decoding tag hex"),
            result: tc.result,
        }
    }

    /// Exercises this test vector against the enclave, returning the outcome.
    ///
    /// Dispatches to the appropriate strategy based on the [`TestResult`]:
    /// valid vectors are encrypted and round-tripped, invalid vectors are
    /// verified to fail, and acceptable vectors are skipped.
    async fn exercise(
        &self,
        client: &mut AeadAsyncClient<oak_launcher_utils::channel::ConnectorHandle>,
    ) -> ExerciseOutcome {
        match self.result {
            TestResult::Valid => self.exercise_valid(client).await,
            TestResult::Invalid => self.exercise_invalid(client).await,
            // Acceptable vectors may pass or fail depending on the
            // implementation; skip them to avoid false negatives.
            TestResult::Acceptable => ExerciseOutcome::Acceptable,
        }
    }

    /// Encrypts the plaintext, verifies it matches expected ciphertext and
    /// tag, then decrypts and verifies the round-trip.
    async fn exercise_valid(
        &self,
        client: &mut AeadAsyncClient<oak_launcher_utils::channel::ConnectorHandle>,
    ) -> ExerciseOutcome {
        let tc_id = self.tc_id;

        let encrypt_request = AeadEncryptRequest {
            key: self.key.clone(),
            nonce: self.nonce.clone(),
            plaintext: self.plaintext.clone(),
            aad: self.aad.clone(),
        };
        let encrypt_result = client
            .encrypt(&encrypt_request)
            .await
            .unwrap_or_else(|e| panic!("tc {tc_id}: encrypt transport error: {e}"));

        let encrypt_response: AeadEncryptResponse = match encrypt_result {
            Ok(response) => response,
            Err(status) if is_unimplemented(&status) => return ExerciseOutcome::Unsupported,
            Err(status) => panic!("tc {tc_id}: encrypt rpc error: {status}"),
        };

        assert_eq!(encrypt_response.ciphertext, self.ciphertext, "tc {tc_id}: ciphertext mismatch");
        assert_eq!(encrypt_response.tag, self.tag, "tc {tc_id}: tag mismatch");

        let decrypt_request = AeadDecryptRequest {
            key: self.key.clone(),
            nonce: self.nonce.clone(),
            ciphertext: self.ciphertext.clone(),
            aad: self.aad.clone(),
            tag: self.tag.clone(),
        };
        let decrypt_response = client
            .decrypt(&decrypt_request)
            .await
            .unwrap_or_else(|e| panic!("tc {tc_id}: decrypt transport error: {e}"))
            .unwrap_or_else(|e| panic!("tc {tc_id}: decrypt rpc error: {e}"));

        assert_eq!(
            decrypt_response.plaintext, self.plaintext,
            "tc {tc_id}: decrypted plaintext mismatch"
        );
        ExerciseOutcome::Valid
    }

    /// Attempts to decrypt with the given (presumably tampered) inputs and
    /// asserts that the operation fails.
    async fn exercise_invalid(
        &self,
        client: &mut AeadAsyncClient<oak_launcher_utils::channel::ConnectorHandle>,
    ) -> ExerciseOutcome {
        let tc_id = self.tc_id;

        let decrypt_request = AeadDecryptRequest {
            key: self.key.clone(),
            nonce: self.nonce.clone(),
            ciphertext: self.ciphertext.clone(),
            aad: self.aad.clone(),
            tag: self.tag.clone(),
        };
        let result = client
            .decrypt(&decrypt_request)
            .await
            .unwrap_or_else(|e| panic!("tc {tc_id}: decrypt transport error: {e}"));

        match result {
            Ok(_) => panic!(
                "tc {tc_id}: expected decryption to fail for invalid test vector, but it succeeded"
            ),
            // Any error — including Unimplemented — is a correct rejection
            // of an invalid vector.
            Err(_) => ExerciseOutcome::Invalid,
        }
    }
}

#[tokio::test(flavor = "multi_thread", worker_threads = 3)]
async fn test_wycheproof_aead_vectors() {
    let test_vectors_path = data_path("third_party/wycheproof/testvectors_v1/aes_gcm_test.json");
    let test_file_json = std::fs::read_to_string(&test_vectors_path).unwrap_or_else(|e| {
        panic!("reading test vectors from {}: {e}", test_vectors_path.display())
    });
    let test_file: AeadTestFile =
        serde_json::from_str(&test_file_json).expect("parsing test vector JSON");

    let (_guest_instance, mut client) = launch_aead_enclave().await;

    let mut valid_count = 0u32;
    let mut invalid_count = 0u32;
    let mut unsupported_count = 0u32;
    let mut acceptable_count = 0u32;

    for group in &test_file.test_groups {
        let mut group_valid = 0u32;
        let mut group_invalid = 0u32;
        let mut group_unsupported = 0u32;
        let mut group_acceptable = 0u32;

        for tc in &group.tests {
            match AeadTestVector::parse(tc).exercise(&mut client).await {
                ExerciseOutcome::Valid => group_valid += 1,
                ExerciseOutcome::Invalid => group_invalid += 1,
                ExerciseOutcome::Unsupported => group_unsupported += 1,
                ExerciseOutcome::Acceptable => group_acceptable += 1,
            }
        }

        eprintln!(
            "  key={}b iv={}b tag={}b: {group_valid} valid, {group_invalid} invalid, \
             {group_unsupported} unsupported, {group_acceptable} acceptable",
            group.key_size, group.iv_size, group.tag_size
        );

        valid_count += group_valid;
        invalid_count += group_invalid;
        unsupported_count += group_unsupported;
        acceptable_count += group_acceptable;
    }

    eprintln!(
        "Wycheproof AEAD test complete: {valid_count} valid, {invalid_count} invalid, \
         {unsupported_count} unsupported, {acceptable_count} acceptable"
    );
    assert!(valid_count > 0, "expected at least one valid test vector");
    assert!(invalid_count > 0, "expected at least one invalid test vector");
}
