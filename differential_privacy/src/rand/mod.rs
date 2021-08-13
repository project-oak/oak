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

//! Methods for generating random numbers from distributions useful for the differential privacy
//! library.
//!
//! Based on the upstream code at https://github.com/google/differential-privacy/blob/main/go/rand/rand.go
//! Note: this module diverges somewhat from the upstream Go code. This is done to better match the
//! default features of the `rand` crate and to support testing with fixed seeds.

use rand::{rngs::StdRng, thread_rng, RngCore, SeedableRng};

/// Wrapper for the actual random number generator.
pub struct Rand {
    /// The internal random number generator used for sampling the noise.
    rng: StdRng,
    /// Buffer of random bits for generating random boolean values.
    rand_bit_buf: u32,
    /// Current position inside the bit buffer.
    rand_bit_pos: usize,
}

impl Rand {
    pub fn new() -> crate::Result<Self> {
        Ok(Self::new_with_rng(StdRng::from_rng(thread_rng())?))
    }

    #[cfg(test)]
    pub fn new_for_test(rng: StdRng) -> Self {
        Self::new_with_rng(rng)
    }

    fn new_with_rng(rng: StdRng) -> Self {
        Self {
            rng,
            rand_bit_buf: 0,
            rand_bit_pos: usize::MAX,
        }
    }

    // Returns a uniformly random u64.
    pub fn u64(&mut self) -> u64 {
        self.rng.next_u64()
    }

    /// Returns +1.0 or -1.0 with equal probabilities.
    pub fn sign(&mut self) -> f64 {
        if self.boolean() {
            return 1.0;
        }
        return -1.0;
    }

    /// Returns true or false with equal probability.
    pub fn boolean(&mut self) -> bool {
        if self.rand_bit_pos > 31 {
            // Out of random bits.
            self.rand_bit_buf = self.rng.next_u32();
            self.rand_bit_pos = 0
        }
        let res = self.rand_bit_buf & (1 << self.rand_bit_pos) > 0;
        self.rand_bit_pos += 1;
        res
    }

    /// Returns an f64 from the interval (0,1] such that each float  in the interval is returned
    /// with positive probability and the resulting distribution simulates a continuous uniform
    /// distribution on (0, 1].
    ///
    /// See http://g/go-nuts/GndbDnHKHuw/VNSrkl9vBQAJ for details.
    pub fn uniform(&mut self) -> f64 {
        let i = self.u64() % (1 << 53);
        let r = (1.0 + (i as f64) / ((1 << 53) as f64)) / 2.0_f64.powf(self.geometric());
        // We want to avoid returning 0, since we're taking the log of the output.
        if r == 0.0 {
            return 1.0;
        }
        r
    }

    /// Returns an f64 that counts the number of Bernoulli trials until the first success for a
    /// success probability of 0.5.
    fn geometric(&mut self) -> f64 {
        // 1 plus the number of leading zeros from an infinite stream of random bits follows the
        // desired geometric distribution.
        let mut b = 1;
        let mut r = 0;
        while r == 0 {
            r = self.rng.next_u32();
            b += r.leading_zeros();
        }
        b as f64
    }
}
