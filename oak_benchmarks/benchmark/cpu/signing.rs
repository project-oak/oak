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

//! ECDSA P-256 signing and verification benchmark.
//!
//! Models the cryptographic oracle workload, a small high-assurance service
//! that holds a private key and signs on behalf of clients.
//!
//! Signing uses RFC 6979 deterministic nonces, so no entropy source is needed
//! and the two platforms can be checked for bit-identical signatures. See
//! <https://www.rfc-editor.org/rfc/rfc6979>. The key is derived from the
//! benchmark seed; that is a test fixture, not a secure key generation
//! procedure.

use alloc::vec::Vec;

use p256::ecdsa::{Signature, SigningKey, VerifyingKey, signature::Verifier};

use super::CpuBenchmark;
use crate::{
    BenchmarkError, BenchmarkResult, CHECKSUM_INIT, checksum_update, generate_benchmark_data,
    timer::BenchmarkTimer,
};

/// Size of the message that gets signed, in bytes.
///
/// Fixed at 32 bytes because ECDSA signs a digest-sized value; the cost is
/// dominated by the scalar multiplication, not by message length.
pub const MESSAGE_SIZE: usize = 32;

/// Number of distinct messages cycled through during the benchmark.
///
/// Using several messages rather than one prevents any caching of intermediate
/// values from flattering the result, while keeping setup cheap.
const NUM_MESSAGES: usize = 64;

/// Operation performed by the signing benchmark.
#[derive(Debug, Clone, Copy)]
pub enum SigningMode {
    /// Produce a signature over a message.
    Sign,
    /// Verify a previously produced signature.
    Verify,
}

/// ECDSA P-256 benchmark.
pub struct SigningBenchmark {
    signing_key: SigningKey,
    verifying_key: VerifyingKey,
    messages: Vec<[u8; MESSAGE_SIZE]>,
    /// Signatures matching `messages`, precomputed for the verify path.
    signatures: Vec<Signature>,
}

impl SigningBenchmark {
    /// Create a new signing benchmark with a deterministic key and messages.
    pub fn new(seed: u64) -> Result<Self, BenchmarkError> {
        // Derive a private scalar deterministically from the seed. Rejection
        // sampling keeps trying until the bytes form a valid P-256 scalar,
        // which is overwhelmingly likely on the first attempt.
        let mut key_bytes = [0u8; 32];
        let mut attempt = 0u64;
        let signing_key = loop {
            generate_benchmark_data(&mut key_bytes, seed.wrapping_add(attempt));
            if let Ok(key) = SigningKey::from_slice(&key_bytes) {
                break key;
            }
            attempt += 1;
            if attempt > 1000 {
                return Err(BenchmarkError::CryptoFailure);
            }
        };
        let verifying_key = *signing_key.verifying_key();

        let mut messages = Vec::with_capacity(NUM_MESSAGES);
        for i in 0..NUM_MESSAGES {
            let mut msg = [0u8; MESSAGE_SIZE];
            generate_benchmark_data(&mut msg, seed.wrapping_add(0x1000 + i as u64));
            messages.push(msg);
        }

        // Precompute signatures so the verify benchmark does not pay for
        // signing inside the timed region.
        let mut signatures = Vec::with_capacity(NUM_MESSAGES);
        for msg in &messages {
            let sig: Signature = sign_message(&signing_key, msg);
            signatures.push(sig);
        }

        Ok(Self { signing_key, verifying_key, messages, signatures })
    }

    /// Run the benchmark for the requested mode.
    pub fn run<T: BenchmarkTimer>(
        &self,
        mode: SigningMode,
        iterations: u32,
        warmup_iterations: u32,
    ) -> Result<BenchmarkResult, BenchmarkError> {
        if iterations == 0 {
            return Err(BenchmarkError::InvalidParameter);
        }
        match mode {
            SigningMode::Sign => Ok(self.run_sign::<T>(iterations, warmup_iterations)),
            SigningMode::Verify => self.run_verify::<T>(iterations, warmup_iterations),
        }
    }

    fn run_sign<T: BenchmarkTimer>(
        &self,
        iterations: u32,
        warmup_iterations: u32,
    ) -> BenchmarkResult {
        let mut warmup_checksum = CHECKSUM_INIT;
        for i in 0..warmup_iterations as usize {
            let msg = &self.messages[i % NUM_MESSAGES];
            let sig = sign_message(&self.signing_key, msg);
            warmup_checksum = checksum_update(warmup_checksum, &sig.to_bytes());
        }
        core::hint::black_box(warmup_checksum);

        let mut checksum = CHECKSUM_INIT;
        let timer = T::start();

        for i in 0..iterations as usize {
            let msg = &self.messages[i % NUM_MESSAGES];
            let sig = sign_message(&self.signing_key, core::hint::black_box(msg));
            checksum = checksum_update(checksum, &sig.to_bytes());
        }

        let timing = timer.stop();
        let bytes_processed = iterations as u64 * MESSAGE_SIZE as u64;
        BenchmarkResult::new(timing, iterations, bytes_processed, checksum)
    }

    fn run_verify<T: BenchmarkTimer>(
        &self,
        iterations: u32,
        warmup_iterations: u32,
    ) -> Result<BenchmarkResult, BenchmarkError> {
        let mut warmup_ok = 0u64;
        for i in 0..warmup_iterations as usize {
            let idx = i % NUM_MESSAGES;
            if self.verifying_key.verify(&self.messages[idx], &self.signatures[idx]).is_ok() {
                warmup_ok += 1;
            }
        }
        core::hint::black_box(warmup_ok);

        let mut verified = 0u64;
        let timer = T::start();

        for i in 0..iterations as usize {
            let idx = i % NUM_MESSAGES;
            let msg = core::hint::black_box(&self.messages[idx]);
            if self.verifying_key.verify(msg, &self.signatures[idx]).is_ok() {
                verified += 1;
            }
        }

        let timing = timer.stop();

        // Every signature was produced by the matching key, so all must
        // verify. If any failed, the measurement is meaningless because the
        // fast-reject path is far cheaper than a full verification.
        if verified != iterations as u64 {
            return Err(BenchmarkError::CryptoFailure);
        }

        let bytes_processed = iterations as u64 * MESSAGE_SIZE as u64;
        // Checksum over the signature set makes the verify path comparable
        // across platforms in the same way as the other benchmarks.
        let mut checksum = CHECKSUM_INIT;
        for sig in &self.signatures {
            checksum = checksum_update(checksum, &sig.to_bytes());
        }
        Ok(BenchmarkResult::new(timing, iterations, bytes_processed, checksum))
    }
}

/// Sign a message with RFC 6979 deterministic nonce generation.
#[inline]
fn sign_message(key: &SigningKey, msg: &[u8]) -> Signature {
    use p256::ecdsa::signature::Signer;
    key.sign(msg)
}

impl CpuBenchmark for SigningBenchmark {
    fn max_data_size(&self) -> usize {
        MESSAGE_SIZE
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn signatures_are_deterministic() {
        let a = SigningBenchmark::new(42).expect("constructing benchmark");
        let b = SigningBenchmark::new(42).expect("constructing benchmark");
        assert_eq!(a.signatures[0].to_bytes(), b.signatures[0].to_bytes());
    }

    #[test]
    fn different_seeds_give_different_keys() {
        let a = SigningBenchmark::new(1).expect("constructing benchmark");
        let b = SigningBenchmark::new(2).expect("constructing benchmark");
        assert_ne!(
            a.verifying_key.to_encoded_point(false).as_bytes(),
            b.verifying_key.to_encoded_point(false).as_bytes()
        );
    }

    #[test]
    fn precomputed_signatures_verify() {
        let bench = SigningBenchmark::new(7).expect("constructing benchmark");
        for (msg, sig) in bench.messages.iter().zip(bench.signatures.iter()) {
            assert!(bench.verifying_key.verify(msg, sig).is_ok());
        }
    }

    #[test]
    fn sign_and_verify_produce_stable_checksums() {
        let bench = SigningBenchmark::new(9).expect("constructing benchmark");
        let first = bench.run::<crate::timer::NativeTimer>(SigningMode::Sign, 8, 0).unwrap();
        let second = bench.run::<crate::timer::NativeTimer>(SigningMode::Sign, 8, 0).unwrap();
        assert_eq!(first.checksum, second.checksum);

        let verify = bench.run::<crate::timer::NativeTimer>(SigningMode::Verify, 8, 0).unwrap();
        assert_eq!(verify.iterations_completed, 8);
    }

    #[test]
    fn zero_iterations_is_rejected() {
        let bench = SigningBenchmark::new(3).expect("constructing benchmark");
        assert_eq!(
            bench.run::<crate::timer::NativeTimer>(SigningMode::Sign, 0, 0).unwrap_err(),
            BenchmarkError::InvalidParameter
        );
    }
}
