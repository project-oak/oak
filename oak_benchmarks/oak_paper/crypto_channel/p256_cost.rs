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

//! Costs the P-256 primitives underneath a Noise handshake.
//!
//! The `Setup` figures in this crate compare an Oak Noise handshake against a
//! TLS one. That comparison is only interpretable if it is clear what the Noise
//! number is made of, and it turns out to be almost entirely elliptic-curve
//! scalar multiplication rather than anything specific to Noise: an NN
//! handshake performs four scalar multiplications in a serial chain -- client
//! key generation, then server key generation and `ee`, then client `ee` -- and
//! four times the figures below accounts for essentially all of the
//! transport-free handshake time reported by `//oak_session/benches:benches`.
//!
//! Run with:
//!
//! ```sh
//! bazel run -c opt //oak_benchmarks/oak_paper/crypto_channel:p256_cost -- --bench
//! ```
//!
//! See the README section "What the `Setup` comparison does not show".

use criterion::{Criterion, criterion_group, criterion_main};
use oak_crypto::noise_handshake::{P256Scalar, p256_scalar_mult};
use p256::ecdsa::{
    Signature, SigningKey, VerifyingKey,
    signature::{Signer, Verifier},
};
use rand_core::OsRng;

/// Key generation: draws a scalar and multiplies the generator by it.
fn bench_keygen(c: &mut Criterion) {
    c.bench_function("p256 keygen", |b| {
        b.iter(|| {
            let scalar = P256Scalar::generate();
            std::hint::black_box(scalar.compute_public_key())
        })
    });
}

/// The scalar draw alone, so it can be told apart from the multiplication.
fn bench_generate_only(c: &mut Criterion) {
    c.bench_function("p256 scalar generate", |b| {
        b.iter(|| std::hint::black_box(P256Scalar::generate()))
    });
}

/// The fixed-base multiplication alone.
///
/// Worth reading next to [`bench_ecdh`]: a fixed-base multiplication can use a
/// precomputed table for the generator and so should be materially cheaper than
/// the variable-base case. If the two come out equal, that optimisation is not
/// in effect.
fn bench_public_key_only(c: &mut Criterion) {
    let scalar = P256Scalar::generate();
    c.bench_function("p256 compute_public_key", |b| {
        b.iter(|| std::hint::black_box(scalar.compute_public_key()))
    });
}

/// ECDH: one variable-base scalar multiplication, the handshake's `ee`.
fn bench_ecdh(c: &mut Criterion) {
    let ours = P256Scalar::generate();
    let peer_public = P256Scalar::generate().compute_public_key();
    c.bench_function("p256 ecdh", |b| {
        b.iter(|| std::hint::black_box(p256_scalar_mult(&ours, &peer_public).unwrap()))
    });
}

/// ECDSA signing: what a server pays to bind one session to its attestation.
///
/// Oak's attested Noise signs the Noise handshake hash with the private half of
/// the binding key carried in its DICE evidence, exactly once per session.
fn bench_ecdsa_sign(c: &mut Criterion) {
    let signing_key = SigningKey::random(&mut OsRng);
    let message = [0u8; 32];
    c.bench_function("p256 ecdsa sign", |b| {
        b.iter(|| {
            let signature: Signature = signing_key.sign(&message);
            std::hint::black_box(signature)
        })
    });
}

/// ECDSA verification: what a client pays *per DICE layer certificate*, and
/// once more for the session binding signature.
///
/// This is the unit the attested-versus-unattested `Setup` difference is built
/// from: multiply by the number of certificates in the chain, add one for the
/// binding, and the remainder is parsing and policy evaluation.
fn bench_ecdsa_verify(c: &mut Criterion) {
    let signing_key = SigningKey::random(&mut OsRng);
    let verifying_key = VerifyingKey::from(&signing_key);
    let message = [0u8; 32];
    let signature: Signature = signing_key.sign(&message);
    // `verify` returns `Result<(), Error>`, so black-boxing its `unwrap()`
    // black-boxes a unit and is no barrier at all. Hand criterion the `Result`
    // instead, and check outside the loop that it is the success path being
    // timed.
    assert!(verifying_key.verify(&message, &signature).is_ok());
    c.bench_function("p256 ecdsa verify", |b| {
        b.iter(|| verifying_key.verify(&message, &signature))
    });
}

criterion_group!(
    benches,
    bench_keygen,
    bench_generate_only,
    bench_public_key_only,
    bench_ecdh,
    bench_ecdsa_sign,
    bench_ecdsa_verify
);
criterion_main!(benches);
