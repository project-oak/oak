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

//! Integration test exercising AEAD and ML-KEM crypto operations inside a
//! Restricted Kernel enclave against Wycheproof test vectors.
//!
//! The test launches a Restricted Kernel VM running an enclave app that
//! implements the [`service::oak::crypto_test::Crypto`] micro_rpc service,
//! then sends encrypt/decrypt and ML-KEM requests for each test vector and
//! verifies that the results match.
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
use oak_launcher_utils::{channel::ConnectorHandle, launcher};
use service::oak::crypto_test::{
    AeadDecryptRequest, AeadEncryptRequest, AeadEncryptResponse, CryptoAsyncClient,
};

mod mlkem_wycheproof;
mod wycheproof;

use wycheproof::{AeadTestFile, TestResult};

/// Convenience alias for the unified crypto client bound to the launcher's
/// transport. A single enclave backs every AEAD and ML-KEM operation.
type CryptoClient = CryptoAsyncClient<ConnectorHandle>;

/// Launches the enclave app and returns a raw connector handle to it.
///
/// Also returns the guest instance handle — the caller must keep it alive
/// for the duration of the test, since dropping it kills the QEMU process.
///
/// The returned [`ConnectorHandle`] is cheaply cloneable, so a single enclave
/// can back one or more [`CryptoClient`]s.
async fn launch_enclave() -> (Box<dyn oak_launcher_utils::launcher::GuestInstance>, ConnectorHandle)
{
    let enclave_app_path = data_path(env!("ENCLAVE_APP_PATH"));
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

    launcher::launch(params).await.expect("launching enclave")
}

/// Launches the enclave app and returns a crypto async client connected to it.
///
/// See [`launch_enclave`] for the lifetime requirements of the returned guest.
async fn launch_crypto_enclave()
-> (Box<dyn oak_launcher_utils::launcher::GuestInstance>, CryptoClient) {
    let (guest_instance, connector_handle) = launch_enclave().await;
    (guest_instance, CryptoClient::new(connector_handle))
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

/// Running tallies of test-vector outcomes, shared across every Wycheproof
/// vector family.
#[derive(Default)]
struct Counts {
    valid: u32,
    invalid: u32,
    unsupported: u32,
    acceptable: u32,
}

impl Counts {
    /// Folds a single outcome into the tally.
    fn record(&mut self, outcome: ExerciseOutcome) {
        match outcome {
            ExerciseOutcome::Valid => self.valid += 1,
            ExerciseOutcome::Invalid => self.invalid += 1,
            ExerciseOutcome::Unsupported => self.unsupported += 1,
            ExerciseOutcome::Acceptable => self.acceptable += 1,
        }
    }

    /// Adds another set of tallies into this one.
    fn add(&mut self, other: &Counts) {
        self.valid += other.valid;
        self.invalid += other.invalid;
        self.unsupported += other.unsupported;
        self.acceptable += other.acceptable;
    }
}

impl core::fmt::Display for Counts {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        write!(
            f,
            "{} valid, {} invalid, {} unsupported, {} acceptable",
            self.valid, self.invalid, self.unsupported, self.acceptable
        )
    }
}

/// A single Wycheproof test vector that knows how to exercise itself against
/// the enclave.
///
/// Each vector family (AEAD, ML-KEM, …) implements this trait so that the
/// generic [`run_cases`] runner can drive any Wycheproof suite uniformly. To
/// support a new kind of test vector, add a type implementing `Exercise` and
/// feed its vectors to [`run_cases`].
trait Exercise {
    /// Runs this vector against `client`, returning the outcome.
    async fn exercise(&self, client: &mut CryptoClient) -> ExerciseOutcome;
}

/// Reads and parses a Wycheproof JSON file from the test data directory.
///
/// The path is resolved relative to `third_party/wycheproof/testvectors_v1`.
fn load_test_file<T: serde::de::DeserializeOwned>(filename: &str) -> T {
    let path = data_path(format!("third_party/wycheproof/testvectors_v1/{filename}"));
    let json = std::fs::read_to_string(&path)
        .unwrap_or_else(|e| panic!("reading test vectors from {}: {e}", path.display()));
    serde_json::from_str(&json).unwrap_or_else(|e| panic!("parsing {filename}: {e}"))
}

/// Exercises every case against the enclave, logs a one-line summary prefixed
/// with `label`, and returns the tallied outcomes.
async fn run_cases(
    client: &mut CryptoClient,
    label: &str,
    cases: impl IntoIterator<Item = impl Exercise>,
) -> Counts {
    let mut counts = Counts::default();
    for case in cases {
        counts.record(case.exercise(client).await);
    }
    eprintln!("  {label}: {counts}");
    counts
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

    /// Encrypts the plaintext, verifies it matches expected ciphertext and
    /// tag, then decrypts and verifies the round-trip.
    async fn exercise_valid(&self, client: &mut CryptoClient) -> ExerciseOutcome {
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
    async fn exercise_invalid(&self, client: &mut CryptoClient) -> ExerciseOutcome {
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

impl Exercise for AeadTestVector {
    /// Dispatches to the appropriate strategy based on the [`TestResult`]:
    /// valid vectors are encrypted and round-tripped, invalid vectors are
    /// verified to fail, and acceptable vectors are skipped.
    async fn exercise(&self, client: &mut CryptoClient) -> ExerciseOutcome {
        match self.result {
            TestResult::Valid => self.exercise_valid(client).await,
            TestResult::Invalid => self.exercise_invalid(client).await,
            // Acceptable vectors may pass or fail depending on the
            // implementation; skip them to avoid false negatives.
            TestResult::Acceptable => ExerciseOutcome::Acceptable,
        }
    }
}

#[tokio::test(flavor = "multi_thread", worker_threads = 3)]
async fn test_wycheproof_aead_vectors() {
    // Both tests in this binary may try to initialize the logger; ignore a
    // double init.
    let _ = env_logger::try_init();

    let test_file: AeadTestFile = load_test_file("aes_gcm_test.json");
    let (_guest_instance, mut client) = launch_crypto_enclave().await;

    let mut totals = Counts::default();
    for group in &test_file.test_groups {
        let label =
            format!("key={}b iv={}b tag={}b", group.key_size, group.iv_size, group.tag_size);
        let vectors = group.tests.iter().map(AeadTestVector::parse);
        totals.add(&run_cases(&mut client, &label, vectors).await);
    }

    eprintln!("Wycheproof AEAD test complete: {totals}");
    assert!(totals.valid > 0, "expected at least one valid test vector");
    assert!(totals.invalid > 0, "expected at least one invalid test vector");
}

// ---------------------------------------------------------------------------
// ML-KEM (FIPS 203) Wycheproof tests
// ---------------------------------------------------------------------------

use service::oak::crypto_test::{
    MlKemDecapsulateFromSeedRequest, MlKemDecapsulateResponse, MlKemKeyGenRequest,
};

/// The ML-KEM operation exercised by a given Wycheproof vector family.
#[derive(Clone, Copy)]
enum MlKemOp {
    /// `mlkem_*_test.json`: regenerate the key from a seed, then decapsulate
    /// the ciphertext and compare the shared secret against `K`.
    DecapsulateFromSeed,
    /// `mlkem_*_keygen_seed_test.json`: regenerate the key from a seed and
    /// compare the encapsulation (and, if returned, decapsulation) key.
    KeyGen,
}

/// Returns `true` when the enclave under test is the BoringSSL-based app, which
/// (unlike the aes-gcm app) is expected to actually exercise ML-KEM vectors.
fn boringssl_enclave() -> bool {
    env!("ENCLAVE_APP_PATH").contains("boringssl")
}

/// Maps a Wycheproof `parameterSet` string to its numeric security parameter.
fn parse_parameter_set(parameter_set: &str) -> u32 {
    match parameter_set {
        "ML-KEM-512" => 512,
        "ML-KEM-768" => 768,
        "ML-KEM-1024" => 1024,
        other => panic!("unknown ML-KEM parameter set: {other}"),
    }
}

/// Hex-decodes a Wycheproof byte field, panicking with context on failure.
fn decode_hex(value: &str, field: &str) -> Vec<u8> {
    hex::decode(value).unwrap_or_else(|e| panic!("decoding {field} hex: {e}"))
}

/// Interprets a decapsulation RPC result (which returns a shared secret)
/// against the vector's expected outcome.
///
/// Used by [`MlKemOp::DecapsulateFromSeed`] to compare the returned shared
/// secret against `K`.
fn check_shared_secret(
    tc_id: u32,
    result: TestResult,
    rpc_result: Result<MlKemDecapsulateResponse, micro_rpc::Status>,
    expected: &[u8],
) -> ExerciseOutcome {
    match result {
        TestResult::Valid => match rpc_result {
            Ok(response) => {
                assert_eq!(response.shared_secret, expected, "tc {tc_id}: shared secret mismatch");
                ExerciseOutcome::Valid
            }
            Err(status) if is_unimplemented(&status) => ExerciseOutcome::Unsupported,
            Err(status) => panic!("tc {tc_id}: decapsulation rpc error: {status}"),
        },
        TestResult::Invalid => match rpc_result {
            Err(status) if is_unimplemented(&status) => ExerciseOutcome::Unsupported,
            // Any (non-Unimplemented) error is a correct rejection.
            Err(_) => ExerciseOutcome::Invalid,
            // A returned shared secret is only acceptable if it differs from the
            // (incorrect) expected value — e.g. an implicit-rejection secret.
            Ok(response) => {
                assert_ne!(
                    response.shared_secret, expected,
                    "tc {tc_id}: expected decapsulation to reject invalid vector, but it produced \
                     the expected shared secret"
                );
                ExerciseOutcome::Invalid
            }
        },
        TestResult::Acceptable => ExerciseOutcome::Acceptable,
    }
}

/// Exercises a single ML-KEM vector against the enclave for the given
/// operation.
async fn exercise_mlkem(
    client: &mut CryptoClient,
    op: MlKemOp,
    parameter_set: u32,
    tc: &mlkem_wycheproof::MlKemTestVector,
) -> ExerciseOutcome {
    let tc_id = tc.tc_id;
    match op {
        MlKemOp::DecapsulateFromSeed => {
            let request = MlKemDecapsulateFromSeedRequest {
                parameter_set,
                seed: decode_hex(&tc.seed, "seed"),
                ciphertext: decode_hex(&tc.c, "ciphertext"),
            };
            let rpc_result = client.decapsulate_from_seed(&request).await.unwrap_or_else(|e| {
                panic!("tc {tc_id}: decapsulate_from_seed transport error: {e}")
            });
            check_shared_secret(tc_id, tc.result, rpc_result, &decode_hex(&tc.shared_secret, "K"))
        }
        MlKemOp::KeyGen => {
            let expected_ek = decode_hex(&tc.ek, "ek");
            let expected_dk = decode_hex(&tc.dk, "dk");
            let request = MlKemKeyGenRequest { parameter_set, seed: decode_hex(&tc.seed, "seed") };
            let rpc_result = client
                .key_gen(&request)
                .await
                .unwrap_or_else(|e| panic!("tc {tc_id}: key_gen transport error: {e}"));
            match tc.result {
                TestResult::Valid => match rpc_result {
                    Ok(response) => {
                        assert_eq!(response.ek, expected_ek, "tc {tc_id}: ek mismatch");
                        // An empty `dk` means the enclave cannot serialize the
                        // decapsulation key, so we only check it when present.
                        if !response.dk.is_empty() {
                            assert_eq!(response.dk, expected_dk, "tc {tc_id}: dk mismatch");
                        }
                        ExerciseOutcome::Valid
                    }
                    Err(status) if is_unimplemented(&status) => ExerciseOutcome::Unsupported,
                    Err(status) => panic!("tc {tc_id}: key_gen rpc error: {status}"),
                },
                TestResult::Invalid => match rpc_result {
                    Err(status) if is_unimplemented(&status) => ExerciseOutcome::Unsupported,
                    Err(_) => ExerciseOutcome::Invalid,
                    Ok(response) => {
                        assert_ne!(
                            response.ek, expected_ek,
                            "tc {tc_id}: expected key generation to reject invalid vector"
                        );
                        ExerciseOutcome::Invalid
                    }
                },
                TestResult::Acceptable => ExerciseOutcome::Acceptable,
            }
        }
    }
}

/// An ML-KEM test vector bound to the operation and parameter set with which it
/// should be exercised.
struct MlKemCase<'a> {
    op: MlKemOp,
    parameter_set: u32,
    tc: &'a mlkem_wycheproof::MlKemTestVector,
}

impl Exercise for MlKemCase<'_> {
    async fn exercise(&self, client: &mut CryptoClient) -> ExerciseOutcome {
        exercise_mlkem(client, self.op, self.parameter_set, self.tc).await
    }
}

#[tokio::test(flavor = "multi_thread", worker_threads = 3)]
async fn test_wycheproof_mlkem_vectors() {
    // The AEAD test may also initialize the logger; ignore a double init.
    let _ = env_logger::try_init();

    let (_guest_instance, mut client) = launch_crypto_enclave().await;

    let mut totals = Counts::default();
    // Decapsulation and key generation from a seed are exercised for ML-KEM-768
    // and -1024; BoringSSL's public API does not expose ML-KEM-512.
    for parameter_set in [768u32, 1024] {
        let files = [
            (MlKemOp::DecapsulateFromSeed, format!("mlkem_{parameter_set}_test.json")),
            (MlKemOp::KeyGen, format!("mlkem_{parameter_set}_keygen_seed_test.json")),
        ];
        for (op, filename) in files {
            let file: mlkem_wycheproof::MlKemTestFile = load_test_file(&filename);
            let cases = file.test_groups.iter().flat_map(|group| {
                let parameter_set = parse_parameter_set(&group.parameter_set);
                group.tests.iter().map(move |tc| MlKemCase { op, parameter_set, tc })
            });
            totals.add(&run_cases(&mut client, &filename, cases).await);
        }
    }

    eprintln!("Wycheproof ML-KEM test complete: {totals}");

    // Per-vector assertions above enforce correctness for every outcome. For the
    // BoringSSL enclave app we additionally require that ML-KEM is actually being
    // exercised; the aes-gcm app legitimately reports everything as unsupported.
    if boringssl_enclave() {
        assert!(totals.valid > 0, "expected BoringSSL to validate some ML-KEM vectors");
        assert!(totals.invalid > 0, "expected BoringSSL to reject some invalid ML-KEM vectors");
    }
}
