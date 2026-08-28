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

criterion_group!(benches, bench_keygen, bench_generate_only, bench_public_key_only, bench_ecdh);
criterion_main!(benches);
