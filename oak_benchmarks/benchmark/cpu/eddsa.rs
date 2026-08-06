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

//! Ed25519 signing and verification benchmark.
//!
//! The companion to [`signing`](super::signing), which measures ECDSA over
//! P-256. The two primitives differ by roughly an order of magnitude, so if the
//! enclave tracks the baseline on both, throughput is set by the choice of
//! primitive rather than the choice of kernel.
//!
//! Ed25519 derives its nonce from the key and the message, so signatures are
//! deterministic and the two platforms can be checked for bit-identical output.
//! See RFC 8032 section 5.1.6,
//! <https://www.rfc-editor.org/rfc/rfc8032#section-5.1.6>.
//!
//! Verification uses [`VerifyingKey::verify_strict`], which also rejects public
//! keys and `R` values of small order. The permissive `verify` is measurably
//! cheaper, so these figures are not comparable with Ed25519 benchmarks that do
//! not say which they used. See
//! <https://docs.rs/ed25519-dalek/2/ed25519_dalek/struct.VerifyingKey.html#method.verify_strict>.
//!
//! The key is derived from the benchmark seed; that is a test fixture, not a
//! secure key generation procedure.

use alloc::vec::Vec;

use ed25519_dalek::{Signature, Signer, SigningKey, VerifyingKey};

use super::CpuBenchmark;
use crate::{
    BenchmarkError, BenchmarkResult, CHECKSUM_INIT, checksum_update, generate_benchmark_data,
    timer::BenchmarkTimer,
};

/// Size of the message that gets signed, in bytes.
///
/// Ed25519 hashes the whole message internally rather than accepting a
/// pre-computed digest, but at 32 bytes the cost is still dominated by the
/// scalar multiplication. Matching [`super::signing::MESSAGE_SIZE`] keeps the
/// two signing benchmarks directly comparable.
pub const MESSAGE_SIZE: usize = 32;

/// Number of distinct messages cycled through during the benchmark.
///
/// Using several messages rather than one prevents any caching of intermediate
/// values from flattering the result, while keeping setup cheap.
const NUM_MESSAGES: usize = 64;

/// Operation performed by the Ed25519 benchmark.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum EddsaMode {
    /// Produce a signature over a message.
    Sign,
    /// Verify a previously produced signature, with strict checks.
    Verify,
}

/// Ed25519 benchmark.
pub struct EddsaBenchmark {
    signing_key: SigningKey,
    verifying_key: VerifyingKey,
    messages: Vec<[u8; MESSAGE_SIZE]>,
    /// Signatures matching `messages`, precomputed for the verify path.
    signatures: Vec<Signature>,
}

impl EddsaBenchmark {
    /// Create a new Ed25519 benchmark with a deterministic key and messages.
    ///
    /// Unlike P-256, every 32-byte string is a valid Ed25519 secret key, so no
    /// rejection sampling is needed and construction cannot fail on the key.
    pub fn new(seed: u64) -> Self {
        let mut key_bytes = [0u8; 32];
        generate_benchmark_data(&mut key_bytes, seed);
        let signing_key = SigningKey::from_bytes(&key_bytes);
        let verifying_key = signing_key.verifying_key();

        let mut messages = Vec::with_capacity(NUM_MESSAGES);
        for i in 0..NUM_MESSAGES {
            let mut msg = [0u8; MESSAGE_SIZE];
            generate_benchmark_data(&mut msg, seed.wrapping_add(0x2000 + i as u64));
            messages.push(msg);
        }

        // Precompute signatures so the verify benchmark does not pay for
        // signing inside the timed region.
        let mut signatures = Vec::with_capacity(NUM_MESSAGES);
        for msg in &messages {
            signatures.push(signing_key.sign(msg));
        }

        Self { signing_key, verifying_key, messages, signatures }
    }

    /// Run the benchmark for the requested mode.
    pub fn run<T: BenchmarkTimer>(
        &self,
        mode: EddsaMode,
        iterations: u32,
        warmup_iterations: u32,
    ) -> Result<BenchmarkResult, BenchmarkError> {
        if iterations == 0 {
            return Err(BenchmarkError::InvalidParameter);
        }
        match mode {
            EddsaMode::Sign => Ok(self.run_sign::<T>(iterations, warmup_iterations)),
            EddsaMode::Verify => self.run_verify::<T>(iterations, warmup_iterations),
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
            let sig = self.signing_key.sign(msg);
            warmup_checksum = checksum_update(warmup_checksum, &sig.to_bytes());
        }
        core::hint::black_box(warmup_checksum);

        let mut checksum = CHECKSUM_INIT;
        let timer = T::start();

        for i in 0..iterations as usize {
            let msg = core::hint::black_box(&self.messages[i % NUM_MESSAGES]);
            let sig = self.signing_key.sign(msg);
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
            if self.verifying_key.verify_strict(&self.messages[idx], &self.signatures[idx]).is_ok()
            {
                warmup_ok += 1;
            }
        }
        core::hint::black_box(warmup_ok);

        let mut verified = 0u64;
        let timer = T::start();

        for i in 0..iterations as usize {
            let idx = i % NUM_MESSAGES;
            let msg = core::hint::black_box(&self.messages[idx]);
            if self.verifying_key.verify_strict(msg, &self.signatures[idx]).is_ok() {
                verified += 1;
            }
        }

        let timing = timer.stop();

        // Every signature was produced by the matching key, so all must
        // verify. If any failed, the measurement is meaningless because the
        // reject path is far cheaper than a full verification.
        if verified != iterations as u64 {
            return Err(BenchmarkError::CryptoFailure);
        }

        let bytes_processed = iterations as u64 * MESSAGE_SIZE as u64;
        let mut checksum = CHECKSUM_INIT;
        for sig in &self.signatures {
            checksum = checksum_update(checksum, &sig.to_bytes());
        }
        Ok(BenchmarkResult::new(timing, iterations, bytes_processed, checksum))
    }
}

impl CpuBenchmark for EddsaBenchmark {
    fn max_data_size(&self) -> usize {
        MESSAGE_SIZE
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn signatures_are_deterministic() {
        let a = EddsaBenchmark::new(42);
        let b = EddsaBenchmark::new(42);
        assert_eq!(a.signatures[0].to_bytes(), b.signatures[0].to_bytes());
    }

    #[test]
    fn different_seeds_give_different_keys() {
        let a = EddsaBenchmark::new(1);
        let b = EddsaBenchmark::new(2);
        assert_ne!(a.verifying_key.to_bytes(), b.verifying_key.to_bytes());
    }

    #[test]
    fn precomputed_signatures_verify_strictly() {
        let bench = EddsaBenchmark::new(7);
        for (msg, sig) in bench.messages.iter().zip(bench.signatures.iter()) {
            assert!(bench.verifying_key.verify_strict(msg, sig).is_ok());
        }
    }

    /// A signature must not verify against a message it was not made over,
    /// otherwise the verify benchmark could be taking the reject path.
    #[test]
    fn signatures_do_not_verify_against_other_messages() {
        let bench = EddsaBenchmark::new(11);
        assert!(
            bench.verifying_key.verify_strict(&bench.messages[1], &bench.signatures[0]).is_err()
        );
    }

    #[test]
    fn sign_and_verify_produce_stable_checksums() {
        let bench = EddsaBenchmark::new(9);
        let first = bench.run::<crate::timer::NativeTimer>(EddsaMode::Sign, 8, 0).unwrap();
        let second = bench.run::<crate::timer::NativeTimer>(EddsaMode::Sign, 8, 0).unwrap();
        assert_eq!(first.checksum, second.checksum);

        let verify = bench.run::<crate::timer::NativeTimer>(EddsaMode::Verify, 8, 0).unwrap();
        assert_eq!(verify.iterations_completed, 8);
    }

    #[test]
    fn zero_iterations_is_rejected() {
        let bench = EddsaBenchmark::new(3);
        assert_eq!(
            bench.run::<crate::timer::NativeTimer>(EddsaMode::Sign, 0, 0).unwrap_err(),
            BenchmarkError::InvalidParameter
        );
    }
}
