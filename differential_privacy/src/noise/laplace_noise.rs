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

//! Based on the upstream code at https://github.com/google/differential-privacy/blob/main/go/noise/laplace_noise.go

use crate::{
    checks,
    noise::{secure_noise_math, Noise},
    rand::Rand,
};

/// The granularity paramter determines the resolution of the numerical noise that is
/// being generated relative to the L_inf sensitivity and privacy parameter epsilon.
/// More precisely, the granularity parameter corresponds to the value 2ᵏ described in
/// https://github.com/google/differential-privacy/blob/main/common_docs/Secure_Noise_Generation.pdf.
/// Larger values result in more fine grained noise, but increase the chance of
/// sampling inaccuracies due to overflows. The probability of an overflow is less
/// than 2⁻¹⁰⁰⁰, if the granularity parameter is set to a value of 2⁴⁰ or less and
/// the epsilon passed to addNoise is at least 2⁻⁵⁰.
///
/// This parameter should be a power of 2.
fn granularity_param() -> f64 {
    2.0_f64.powi(40)
}

// Noise instance that adds Laplace noise to its input. Its AddNoise* functions will fail if called
// with a non-zero delta.
//
// The Laplace noise is based on a geometric sampling mechanism that is robust against
// unintentional privacy leaks due to artifacts of floating point arithmetic. See
// https://github.com/google/differential-privacy/blob/main/common_docs/Secure_Noise_Generation.pdf
// for more information.
pub struct Laplace {
    rand: Rand,
}

impl Noise for Laplace {
    fn add_noise_f64(
        &mut self,
        x: f64,
        l_0_sensitivity: i64,
        l_inf_sensitivity: f64,
        epsilon: f64,
        delta: f64,
    ) -> crate::Result<f64> {
        check_args_laplace(
            "add_noise_f64 (Laplace)",
            l_0_sensitivity,
            l_inf_sensitivity,
            epsilon,
            delta,
        )?;
        Ok(self.add_laplace_f64(
            x,
            epsilon,
            l_inf_sensitivity * (l_0_sensitivity as f64), /* l_1_sensitivity */
        ))
    }

    fn add_noise_i64(
        &mut self,
        x: i64,
        l_0_sensitivity: i64,
        l_inf_sensitivity: i64,
        epsilon: f64,
        delta: f64,
    ) -> crate::Result<i64> {
        check_args_laplace(
            "add_noise_i64 (Laplace)",
            l_0_sensitivity,
            l_inf_sensitivity as f64,
            epsilon,
            delta,
        )?;
        Ok(self.add_laplace_i64(
            x,
            epsilon,
            l_inf_sensitivity * l_0_sensitivity, /* l_1_sensitivity */
        ))
    }
}

impl Laplace {
    pub fn new() -> crate::Result<Self> {
        Ok(Self { rand: Rand::new()? })
    }

    #[cfg(test)]
    pub fn new_for_test(rng: rand::rngs::StdRng) -> Self {
        Self {
            rand: Rand::new_with_rng(rng),
        }
    }

    /// Adds Laplace noise scaled to the given `epsilon` and `l_1_sensitivity` to specified f64.
    fn add_laplace_f64(&mut self, x: f64, epsilon: f64, l_1_sensitivity: f64) -> f64 {
        let granularity =
            secure_noise_math::ceil_power_of_two((l_1_sensitivity / epsilon) / granularity_param());
        let sample =
            self.two_sided_geometric(granularity * epsilon / (l_1_sensitivity + granularity));
        secure_noise_math::round_to_multiple_of_power_of_two(x, granularity)
            + (sample as f64) * granularity
    }

    /// Adds Laplace noise scaled to the given `epsilon` and `l_1_sensitivity` to specified i64.
    fn add_laplace_i64(&mut self, x: i64, epsilon: f64, l_1_sensitivity: i64) -> i64 {
        let granularity = secure_noise_math::ceil_power_of_two(
            ((l_1_sensitivity as f64) / epsilon) / granularity_param(),
        );
        let sample = self
            .two_sided_geometric(granularity * epsilon / (l_1_sensitivity as f64 + granularity));
        if granularity < 1.0 {
            return x + (((sample as f64) * granularity).round() as i64);
        }
        secure_noise_math::round_to_multiple(x, granularity as i64) + sample * (granularity as i64)
    }

    /// Draws a sample from a geometric distribution with parameter p = 1 - e^-λ.
    ///
    /// More precisely, it returns the number of Bernoulli trials until the first success where the
    /// success probability is p = 1 - e^-λ. The returned sample is truncated to the max i64
    /// value.
    ///
    /// Note that to ensure that a truncation happens with probability less than 10⁻⁶, λ must be
    /// greater than 2⁻⁵⁹.
    fn geometric(&mut self, lambda: f64) -> i64 {
        // Return truncated sample in the case that the sample exceeds the max i64.
        if self.rand.uniform() > -1.0 * (-1.0 * lambda * (i64::MAX as f64)).exp_m1() {
            return i64::MAX;
        }

        // Perform a binary search for the sample in the interval from 1 to max i64.
        // Each iteration splits the interval in two and randomly keeps either the
        // left or the right subinterval depending on the respective probability of
        // the sample being contained in them. The search ends once the interval only
        // contains a single sample.
        let mut left = 0; // Exclusive bound.
        let mut right = i64::MAX; // Inclusive bound.

        while left + 1 < right {
            // Compute a midpoint that divides the probability mass of the current interval
            // approximately evenly between the left and right subinterval. The resulting
            // midpoint will be less or equal to the arithmetic mean of the interval. This
            // reduces the expected number of iterations of the binary search compared to a
            // search that uses the arithmetic mean as a midpoint. The speed up is more
            // pronounced the higher the success probability p is.
            let mut mid = left
                - ((0.5_f64.ln() + (lambda * ((left - right) as f64)).exp().ln_1p()) / lambda)
                    .floor() as i64;
            // Ensure that mid is contained in the search interval. This is a safeguard to
            // account for potential mathematical inaccuracies due to finite precision arithmetic.
            if mid <= left {
                mid = left + 1
            } else if mid >= right {
                mid = right - 1
            }

            // Probability that the sample is at most mid, i.e.,
            //   q = Pr[X ≤ mid | left < X ≤ right]
            // where X denotes the sample. The value of q should be approximately one half.
            let q = (lambda * ((left - mid) as f64)).exp_m1()
                / (lambda * ((left - right) as f64)).exp_m1();
            if self.rand.uniform() <= q {
                right = mid
            } else {
                left = mid
            }
        }
        right
    }

    // Draws a sample from a geometric distribution that is
    // mirrored at 0. The non-negative part of the distribution's PDF matches
    // the PDF of a geometric distribution of parameter p = 1 - e^-λ that is
    // shifted to the left by 1 and scaled accordingly.
    fn two_sided_geometric(&mut self, lambda: f64) -> i64 {
        let mut sample = 0;
        let mut sign = -1;
        // Keep a sample of 0 only if the sign is positive. Otherwise, the
        // probability of 0 would be twice as high as it should be.
        while sample == 0 && sign == -1 {
            sample = self.geometric(lambda) - 1;
            sign = self.rand.sign() as i64;
        }
        sample * sign
    }
}

fn check_args_laplace(
    label: &str,
    l_0_sensitivity: i64,
    l_inf_sensitivity: f64,
    epsilon: f64,
    delta: f64,
) -> crate::Result<()> {
    checks::check_l_0_sensitivity(label, l_0_sensitivity)?;
    checks::check_l_inf_sensitivity(label, l_inf_sensitivity)?;
    checks::check_epsilon_very_strict(label, epsilon)?;
    checks::check_no_delta(label, delta)
}
