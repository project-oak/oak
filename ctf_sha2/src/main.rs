// Copyright 2025 The Project Oak Authors
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

use rand::{rngs::StdRng, CryptoRng, RngCore, SeedableRng};
use sha2::{Digest, Sha512};

fn assert_crypto_rng<T: CryptoRng>(_rng: &T) {}

fn main() {
    // Initialize an empty byte array which will be filled with the secret flag.
    let mut flag = [0; 64];

    // We must use a cryptographically secure RNG.
    // See <https://rust-random.github.io/book/guide-gen.html#cryptographically-secure-pseudo-random-number-generator>.
    let mut rng = StdRng::from_entropy();
    // Assert the RNG implements the required marker trait, to make sure it is not
    // accidentally replaced with a non-cryptographically secure RNG.
    assert_crypto_rng(&rng);
    rng.fill_bytes(&mut flag);

    let mut hasher = Sha512::new();
    hasher.update(flag);
    let digest = hasher.finalize();

    eprintln!("{:x}", digest);
}
