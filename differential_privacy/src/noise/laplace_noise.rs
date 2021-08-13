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
            rand: Rand::new_for_test(rng),
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

#[cfg(test)]
mod tests {
    use super::*;
    use rand::{rngs::StdRng, Rng, SeedableRng};

    // Tests based on upstream code at https://github.com/google/differential-privacy/blob/main/go/noise/gaussian_noise_test.go

    #[test]
    fn test_laplace_statistics() {
        let number_of_samples: usize = 125000;
        let ln3 = 3.0_f64.ln();
        // Use a fixed seed for the random number generator to avoid potential flakiness.
        let mut lap = Laplace::new_for_test(StdRng::seed_from_u64(0));

        #[derive(Debug)]
        struct TestCase {
            l_0_ensitivity: i64,
            l_inf_sensitivity: f64,
            epsilon: f64,
            mean: f64,
            variance: f64,
        }

        for tc in vec![
            TestCase {
                l_0_ensitivity: 1,
                l_inf_sensitivity: 1.0,
                epsilon: 1.0,
                mean: 0.0,
                variance: 2.0,
            },
            TestCase {
                l_0_ensitivity: 1,
                l_inf_sensitivity: 1.0,
                epsilon: ln3,
                mean: 0.0,
                variance: 2.0 / (ln3 * ln3),
            },
            TestCase {
                l_0_ensitivity: 1,
                l_inf_sensitivity: 1.0,
                epsilon: ln3,
                mean: 45941223.02107,
                variance: 2.0 / (ln3 * ln3),
            },
            TestCase {
                l_0_ensitivity: 1,
                l_inf_sensitivity: 1.0,
                epsilon: 2.0 * ln3,
                mean: 0.0,
                variance: 2.0 / (2.0 * ln3 * 2.0 * ln3),
            },
            TestCase {
                l_0_ensitivity: 1,
                l_inf_sensitivity: 2.0,
                epsilon: 2.0 * ln3,
                mean: 0.0,
                variance: 2.0 / (ln3 * ln3),
            },
            TestCase {
                l_0_ensitivity: 2,
                l_inf_sensitivity: 1.0,
                epsilon: 2.0 * ln3,
                mean: 0.0,
                variance: 2.0 / (ln3 * ln3),
            },
        ] {
            let mut noised_samples = vec![0.0_f64; number_of_samples];
            for sample in noised_samples.iter_mut().take(number_of_samples) {
                *sample = lap
                    .add_noise_f64(
                        tc.mean,
                        tc.l_0_ensitivity,
                        tc.l_inf_sensitivity,
                        tc.epsilon,
                        0.0,
                    )
                    .unwrap();
            }
            let sample_mean = statistical::mean(&noised_samples);
            let sample_variance = statistical::variance(&noised_samples, None);

            // Assuming that the Laplace samples have a mean of 0 and the specified variance of
            // tc.variance, sample_mean_float64 and sample_mean_i64 are approximately
            // Gaussian distributed with a mean of 0 and standard deviation of
            // sqrt(tc.variance⁻ / number_of_samples).
            //
            // The mean_error_tolerance is set to the 99.9995% quantile of the anticipated
            // distribution. Thus, the test falsely rejects with a probability of 10⁻⁵.
            let mean_error_tolerance =
                4.41717_f64 * (tc.variance / (number_of_samples as f64)).sqrt();
            // Assuming that the Laplace samples have the specified variance of tc.variance,
            // sample_variance_f64 and sample_variance_int64 are approximately Gaussian
            // distributed with a mean of tc.variance and a standard deviation of
            // sqrt(5) * tc.variance / sqrt(number_of_samples).
            //
            // The variance_error_tolerance is set to the 99.9995% quantile of the anticipated
            // distribution. Thus, the test falsely rejects with a probability of 10⁻⁵.
            let variance_error_tolerance =
                4.41717_f64 * 5.0_f64.sqrt() * tc.variance / (number_of_samples as f64).sqrt();

            assert!(
                (sample_mean - tc.mean).abs() < mean_error_tolerance,
                "f4 got mean = {}, want {} (parameters {:?})",
                sample_mean,
                tc.mean,
                tc
            );
            assert!(
                (sample_variance - tc.variance).abs() < variance_error_tolerance,
                "f64 got variance = {}, want {} (parameters {:?})",
                sample_variance,
                tc.variance,
                tc
            );
        }
    }

    #[test]
    #[allow(clippy::float_cmp)]
    fn test_add_laplace_f64_rounds_to_granularity() {
        let number_of_trials = 1000;
        // Use a fixed seed for the random number generators to avoid potential flakiness.
        let mut lap = Laplace::new_for_test(StdRng::seed_from_u64(0));
        let mut rng = StdRng::seed_from_u64(0);

        struct TestCase {
            epsilon: f64,
            l_1_sensitivity: f64,
            want_granularity: f64,
        }
        for tc in vec![
            TestCase {
                epsilon: 9.6e-7,
                l_1_sensitivity: 1.0,
                want_granularity: 1.0 / 1048576.0,
            },
            TestCase {
                epsilon: 4.7e-10,
                l_1_sensitivity: 1.0,
                want_granularity: 1.0 / 1024.0,
            },
            TestCase {
                epsilon: 1.5e-11,
                l_1_sensitivity: 1.0,
                want_granularity: 1.0 / 32.0,
            },
            TestCase {
                epsilon: 3.7e-12,
                l_1_sensitivity: 1.0,
                want_granularity: 1.0 / 4.0,
            },
            TestCase {
                epsilon: 1.9e-12,
                l_1_sensitivity: 1.0,
                want_granularity: 1.0 / 2.0,
            },
            TestCase {
                epsilon: 9.1e-13,
                l_1_sensitivity: 1.0,
                want_granularity: 1.0,
            },
            TestCase {
                epsilon: 4.6e-13,
                l_1_sensitivity: 1.0,
                want_granularity: 2.0,
            },
            TestCase {
                epsilon: 2.8e-13,
                l_1_sensitivity: 1.0,
                want_granularity: 4.0,
            },
            TestCase {
                epsilon: 2.9e-14,
                l_1_sensitivity: 1.0,
                want_granularity: 32.0,
            },
            TestCase {
                epsilon: 8.9e-16,
                l_1_sensitivity: 1.0,
                want_granularity: 1024.0,
            },
            TestCase {
                epsilon: 8.7e-19,
                l_1_sensitivity: 1.0,
                want_granularity: 1048576.0,
            },
        ] {
            for _ in 0..number_of_trials {
                // The input x of add_laplace_f64 can be arbitrary.
                let random: f64 = rng.sample(rand::distributions::Standard);
                let x = random * tc.want_granularity * 10.0 - tc.want_granularity * 5.0;
                let noised_x = lap.add_laplace_f64(x, tc.epsilon, tc.l_1_sensitivity);
                assert_eq!(
                    (noised_x / tc.want_granularity).round(),
                    noised_x / tc.want_granularity,
                    "Got noised x: {}, not a multiple of: {}",
                    noised_x,
                    tc.want_granularity
                );
            }
        }
    }

    #[test]
    fn test_add_laplace_i64_rounds_to_granularity() {
        let number_of_trials = 1000;
        // Use a fixed seed for the random number generators to avoid potential flakiness.
        let mut lap = Laplace::new_for_test(StdRng::seed_from_u64(0));
        let mut rng = crate::rand::Rand::new_for_test(StdRng::seed_from_u64(0));

        struct TestCase {
            epsilon: f64,
            l_1_sensitivity: i64,
            want_granularity: i64,
        }
        for tc in vec![
            TestCase {
                epsilon: 4.6e-13,
                l_1_sensitivity: 1,
                want_granularity: 2,
            },
            TestCase {
                epsilon: 2.8e-13,
                l_1_sensitivity: 1,
                want_granularity: 4,
            },
            TestCase {
                epsilon: 2.9e-14,
                l_1_sensitivity: 1,
                want_granularity: 32,
            },
            TestCase {
                epsilon: 8.9e-16,
                l_1_sensitivity: 1,
                want_granularity: 1024,
            },
            // Last upstream test case skipped as it causes an overflow on multiplication.
        ] {
            for _ in 0..number_of_trials {
                // The input x of add_laplace_i64 can be arbitrary but should cover all congruence
                // classes of the anticipated granularity.
                let x = rng.i63n(tc.want_granularity * 10) - tc.want_granularity * 5;
                let noised_x = lap.add_laplace_i64(x, tc.epsilon, tc.l_1_sensitivity);
                assert_eq!(
                    noised_x % tc.want_granularity,
                    0,
                    "Got noised x: {}, not devisible by: {}",
                    noised_x,
                    tc.want_granularity
                );
            }
        }
    }

    #[test]
    fn test_geometric_statistics() {
        let number_of_samples = 125000;
        let mut lap = Laplace::new_for_test(StdRng::seed_from_u64(0));

        #[derive(Debug)]
        struct TestCase {
            lambda: f64,
            mean: f64,
            std_dev: f64,
        }
        for tc in vec![
            TestCase {
                lambda: 0.1,
                mean: 10.50833,
                std_dev: 9.99583,
            },
            TestCase {
                lambda: 0.0001,
                mean: 10000.50001,
                std_dev: 9999.99999,
            },
            TestCase {
                lambda: 0.0000001,
                mean: 10000000.5,
                std_dev: 9999999.99999,
            },
        ] {
            let mut geometric_samples = vec![0.0_f64; number_of_samples];
            for sample in geometric_samples.iter_mut().take(number_of_samples) {
                *sample = lap.geometric(tc.lambda) as f64;
            }
            let sample_mean = statistical::mean(&geometric_samples);
            // Assuming that the geometric samples are distributed according to the specified
            // lambda, the sample_mean is approximately Gaussian distributed with a mean
            // of tc.mean and standard deviation of tc.std_dev /
            // sqrt(number_of_samples).
            //
            // The mean_error_tolerance is set to the 99.9995% quantile of the anticipated
            // distribution of sample_ean. Thus, the test falsely rejects with a
            // probability of 10⁻⁵.
            let mean_error_tolerance = 4.41717_f64 * tc.std_dev / (number_of_samples as f64).sqrt();
            assert!(
                (sample_mean - tc.mean).abs() < mean_error_tolerance,
                "got mean = {}, want {} (parameters {:?})",
                sample_mean,
                tc.mean,
                tc
            );
        }
    }

    #[test]
    fn test_laplace_i64_noise() {
        // Note: this last test is not from the upstream code. It is just an additional validation
        // of the structure of the noise to feel more confident that the port of `add_laplace_i64`
        // was accurate.
        //
        // Run many times and make sure the shape of the histogram looks roughly right.
        let iterations = 1_000_000;
        // Check the 0 bucket and 5 buckets either side.
        let offset = 5;
        // Bucket is allowed up to 3% above or below expected size.
        let margin = 0.03_f64;
        let epsilon = 1.0_f64;
        let beta = 1.0_f64 / epsilon;
        let l_1_sensitivity = 1i64;
        // Use a fixed seed for the random number generator to avoid potential flakiness.
        let mut laplace = Laplace::new_for_test(StdRng::seed_from_u64(0));
        // Calculate expected bucket counts using the cummulative distribution function.
        let expected: Vec<f64> = (-offset..=offset)
            .map(|index| {
                iterations as f64
                    * (laplace_cdf(beta, index as f64 + 0.5)
                        - laplace_cdf(beta, index as f64 - 0.5))
            })
            .collect();

        // Build a histogram of the actual noise.
        let mut histogram: Vec<usize> = (-offset..=offset).map(|_| 0).collect();
        for _ in 0..iterations {
            let noise = laplace.add_laplace_i64(0, epsilon, l_1_sensitivity);
            if (-offset..=offset).contains(&noise) {
                let index = (noise + offset) as usize;
                histogram[index] += 1;
            }
        }

        println!("Expected: {:?}", expected);
        println!("Actual: {:?}", histogram);
        let mut max_diff = 0.0;
        for (index, actual) in histogram.iter().enumerate() {
            let test = expected[index];
            let diff = (test - *actual as f64).abs() / test;
            assert!(diff >= 0.0 && diff <= margin);
            if diff > max_diff {
                max_diff = diff;
            }
        }
        println!("Maximum required margin: {}", max_diff);
    }

    fn laplace_cdf(beta: f64, x: f64) -> f64 {
        // We assume mu = 0.
        // See https://en.wikipedia.org/wiki/Laplace_distribution
        0.5 + 0.5 * x.signum() * (1.0 - (-x.abs() / beta).exp())
    }
}
