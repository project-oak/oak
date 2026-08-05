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

//! AES-256-GCM authenticated encryption benchmark.
//!
//! Stands in for the record-layer cost of an encrypted session without pulling
//! in a transport. Seal is the sender-side cost, open the receiver-side cost
//! including the constant-time tag comparison.
//!
//! Performance here is dominated by AES-NI and PCLMULQDQ, and the enclave
//! target `x86_64-unknown-none` cannot detect those at runtime, so it depends
//! on statically enabled target features. Check [`super::CpuFeatures`] on both
//! sides; if they disagree, the comparison measures two implementations rather
//! than the Restricted Kernel.

use alloc::{vec, vec::Vec};

use aes_gcm::{
    Aes256Gcm, Key, Nonce,
    aead::{Aead, KeyInit, Payload},
};

use super::CpuBenchmark;
use crate::{
    BenchmarkError, BenchmarkResult, CHECKSUM_INIT, checksum_update, fold_sample,
    generate_benchmark_data, timer::BenchmarkTimer,
};

/// Maximum plaintext size (1 MB), matching the hashing benchmark.
pub const MAX_DATA_SIZE: usize = 1024 * 1024;

/// AES-256-GCM nonce length in bytes.
const NONCE_LEN: usize = 12;

/// Direction of the AEAD operation.
#[derive(Debug, Clone, Copy)]
pub enum AeadMode {
    /// Encrypt and authenticate.
    Seal,
    /// Decrypt and verify.
    Open,
}

/// AES-256-GCM benchmark.
pub struct AeadBenchmark {
    cipher: Aes256Gcm,
    plaintext: Vec<u8>,
    /// Ciphertext of `plaintext[..data_size]`, rebuilt when `data_size`
    /// changes so the open path never pays for encryption while timed.
    ciphertext: Vec<u8>,
    /// Size the cached `ciphertext` corresponds to.
    cached_size: usize,
    nonce: [u8; NONCE_LEN],
}

impl AeadBenchmark {
    /// Create a new AEAD benchmark with a deterministic key and plaintext.
    ///
    /// The key is derived from the benchmark seed. This is a fixture, not a
    /// secure key derivation, and must never protect real data.
    pub fn new(seed: u64) -> Self {
        let mut key_bytes = [0u8; 32];
        generate_benchmark_data(&mut key_bytes, seed);
        let key = Key::<Aes256Gcm>::from_slice(&key_bytes);
        let cipher = Aes256Gcm::new(key);

        let mut plaintext = vec![0u8; MAX_DATA_SIZE];
        generate_benchmark_data(&mut plaintext, seed.wrapping_add(1));

        let mut nonce = [0u8; NONCE_LEN];
        generate_benchmark_data(&mut nonce, seed.wrapping_add(2));

        Self { cipher, plaintext, ciphertext: Vec::new(), cached_size: usize::MAX, nonce }
    }

    /// Ensure `self.ciphertext` holds the encryption of `plaintext[..size]`.
    ///
    /// Called outside the timed region.
    fn ensure_ciphertext(&mut self, size: usize) -> Result<(), BenchmarkError> {
        if self.cached_size == size {
            return Ok(());
        }
        let nonce = Nonce::from_slice(&self.nonce);
        let ct = self
            .cipher
            .encrypt(nonce, Payload { msg: &self.plaintext[..size], aad: &[] })
            .map_err(|_| BenchmarkError::CryptoFailure)?;
        self.ciphertext = ct;
        self.cached_size = size;
        Ok(())
    }

    /// Run the benchmark for the requested mode.
    pub fn run<T: BenchmarkTimer>(
        &mut self,
        mode: AeadMode,
        data_size: usize,
        iterations: u32,
        warmup_iterations: u32,
    ) -> Result<BenchmarkResult, BenchmarkError> {
        if data_size > MAX_DATA_SIZE {
            return Err(BenchmarkError::DataSizeTooLarge);
        }
        if iterations == 0 {
            return Err(BenchmarkError::InvalidParameter);
        }
        self.ensure_ciphertext(data_size)?;

        match mode {
            AeadMode::Seal => self.run_seal::<T>(data_size, iterations, warmup_iterations),
            AeadMode::Open => self.run_open::<T>(data_size, iterations, warmup_iterations),
        }
    }

    fn run_seal<T: BenchmarkTimer>(
        &self,
        data_size: usize,
        iterations: u32,
        warmup_iterations: u32,
    ) -> Result<BenchmarkResult, BenchmarkError> {
        let nonce = Nonce::from_slice(&self.nonce);
        let msg = &self.plaintext[..data_size];

        let mut warmup_acc = CHECKSUM_INIT;
        for _ in 0..warmup_iterations {
            let ct = self
                .cipher
                .encrypt(nonce, Payload { msg, aad: &[] })
                .map_err(|_| BenchmarkError::CryptoFailure)?;
            warmup_acc = fold_sample(warmup_acc, core::hint::black_box(ct.as_slice()));
        }
        core::hint::black_box(warmup_acc);

        let mut acc = CHECKSUM_INIT;
        let timer = T::start();

        for _ in 0..iterations {
            let ct = self
                .cipher
                .encrypt(nonce, Payload { msg: core::hint::black_box(msg), aad: &[] })
                .map_err(|_| BenchmarkError::CryptoFailure)?;
            // `black_box` on the whole slice forces the optimiser to treat every
            // ciphertext byte as observed; `fold_sample` is only a cheap carried
            // value. See `fold_sample` for why the real checksum waits.
            acc = fold_sample(acc, core::hint::black_box(ct.as_slice()));
        }

        let timing = timer.stop();
        core::hint::black_box(acc);

        // Encryption is deterministic for a fixed key, nonce and message, so one
        // extra sealing outside the timed region reproduces exactly what the loop
        // computed. The result is independent of `iterations`, which lets the host
        // compare checksums across runs of differing length.
        let ct = self
            .cipher
            .encrypt(nonce, Payload { msg, aad: &[] })
            .map_err(|_| BenchmarkError::CryptoFailure)?;
        let checksum = checksum_update(CHECKSUM_INIT, &ct);

        let bytes_processed = data_size as u64 * iterations as u64;
        Ok(BenchmarkResult::new(timing, iterations, bytes_processed, checksum))
    }

    fn run_open<T: BenchmarkTimer>(
        &self,
        data_size: usize,
        iterations: u32,
        warmup_iterations: u32,
    ) -> Result<BenchmarkResult, BenchmarkError> {
        let nonce = Nonce::from_slice(&self.nonce);
        let ct = self.ciphertext.as_slice();

        let mut warmup_acc = CHECKSUM_INIT;
        for _ in 0..warmup_iterations {
            let pt = self
                .cipher
                .decrypt(nonce, Payload { msg: ct, aad: &[] })
                .map_err(|_| BenchmarkError::CryptoFailure)?;
            warmup_acc = fold_sample(warmup_acc, core::hint::black_box(pt.as_slice()));
        }
        core::hint::black_box(warmup_acc);

        let mut acc = CHECKSUM_INIT;
        let timer = T::start();

        for _ in 0..iterations {
            let pt = self
                .cipher
                .decrypt(nonce, Payload { msg: core::hint::black_box(ct), aad: &[] })
                .map_err(|_| BenchmarkError::CryptoFailure)?;
            // See the corresponding comment in `run_seal`. `decrypt` returning
            // `Ok` already proves the tag was checked, so this path really does
            // authenticate rather than short-circuit.
            acc = fold_sample(acc, core::hint::black_box(pt.as_slice()));
        }

        let timing = timer.stop();
        core::hint::black_box(acc);

        // One extra opening outside the timed region; see `run_seal`.
        let pt = self
            .cipher
            .decrypt(nonce, Payload { msg: ct, aad: &[] })
            .map_err(|_| BenchmarkError::CryptoFailure)?;
        let checksum = checksum_update(CHECKSUM_INIT, &pt);

        let bytes_processed = data_size as u64 * iterations as u64;
        Ok(BenchmarkResult::new(timing, iterations, bytes_processed, checksum))
    }
}

impl CpuBenchmark for AeadBenchmark {
    fn max_data_size(&self) -> usize {
        MAX_DATA_SIZE
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::timer::NativeTimer;

    #[test]
    fn seal_then_open_round_trips() {
        let mut bench = AeadBenchmark::new(11);
        bench.ensure_ciphertext(1024).expect("encrypting");
        let nonce = Nonce::from_slice(&bench.nonce);
        let pt = bench
            .cipher
            .decrypt(nonce, Payload { msg: &bench.ciphertext, aad: &[] })
            .expect("decrypting");
        assert_eq!(pt, &bench.plaintext[..1024]);
    }

    #[test]
    fn same_seed_gives_same_checksum() {
        let mut a = AeadBenchmark::new(5);
        let mut b = AeadBenchmark::new(5);
        let ra = a.run::<NativeTimer>(AeadMode::Seal, 512, 16, 0).unwrap();
        let rb = b.run::<NativeTimer>(AeadMode::Seal, 512, 16, 0).unwrap();
        assert_eq!(ra.checksum, rb.checksum);
    }

    #[test]
    fn different_seeds_give_different_checksums() {
        let mut a = AeadBenchmark::new(5);
        let mut b = AeadBenchmark::new(6);
        let ra = a.run::<NativeTimer>(AeadMode::Seal, 512, 16, 0).unwrap();
        let rb = b.run::<NativeTimer>(AeadMode::Seal, 512, 16, 0).unwrap();
        assert_ne!(ra.checksum, rb.checksum);
    }

    #[test]
    fn open_reports_full_plaintext_bytes() {
        let mut bench = AeadBenchmark::new(2);
        let r = bench.run::<NativeTimer>(AeadMode::Open, 4096, 4, 1).unwrap();
        assert_eq!(r.bytes_processed, 4096 * 4);
    }

    #[test]
    fn oversized_data_is_rejected() {
        let mut bench = AeadBenchmark::new(1);
        assert_eq!(
            bench.run::<NativeTimer>(AeadMode::Seal, MAX_DATA_SIZE + 1, 1, 0).unwrap_err(),
            BenchmarkError::DataSizeTooLarge
        );
    }
}
