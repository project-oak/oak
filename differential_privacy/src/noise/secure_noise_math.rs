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

/// Returns the smallest power of 2 larger or equal to x. The  value of x must be a finite positive
/// number not greater than 2^1023. The result of this method is guaranteed to be an exact power of
/// 2.
pub fn ceil_power_of_two(x: f64) -> f64 {
    if x <= 0.0 || x.is_infinite() || x.is_nan() {
        return f64::NAN;
    }

    // The following bit masks are based on the bit layout of float64 values,
    // which according to the IEEE 754 standard is defined as "1*s 11*e 52*m"
    // where "s" is the sign bit, "e" are the exponent bits, and "m" are the
    // mantissa bits.
    let exponent_mask: u64 = 0x7ff0000000000000;
    let mantissa_mask: u64 = 0x000fffffffffffff;

    let bits = x.to_bits();
    let mantissa_bits = bits & mantissa_mask;

    // Since x is a finite positive number, x is a power of 2 if and only if
    // it has a mantissa of 0.
    if mantissa_bits == 0x0000000000000000 {
        return x;
    }

    let exponent_bits = bits & exponent_mask;
    let max_exponent_bits = f64::MAX.to_bits() & exponent_mask;

    if exponent_bits >= max_exponent_bits {
        // Input is too large.
        return f64::NAN;
    }

    // Increasing the exponent by 1 to get the next power of 2. This is done by
    // adding 0x0010000000000000 to the exponent bits, which will keep a mantissa
    // of all 0s.
    f64::from_bits(exponent_bits + 0x0010000000000000)
}

/// Returns a multiple of granularity that is closest to x. The value of granularity needs to be an
/// exact power of 2, otherwise the result might not be exact.
pub fn round_to_multiple_of_power_of_two(x: f64, granularity: f64) -> f64 {
    (x / granularity).round() * granularity
}

/// Returns a multiple of granularity that is closest to x. The result is exact.
pub fn round_to_multiple(x: i64, granularity: i64) -> i64 {
    let result = (x / granularity) * granularity;
    if x >= 0 {
        if x - result >= (result + granularity) - x {
            // round up
            return result + granularity;
        }
        // round down
        return result;
    }
    if x - (result - granularity) >= result - x {
        // round up
        return result;
    }
    // round down
    result - granularity
}

#[cfg(test)]
mod tests {
    use super::*;

    // Tests based on upstream code at https://github.com/google/differential-privacy/blob/main/go/noise/secure_noise_math_test.go

    #[test]
    fn test_ceil_power_of_two_input_is_not_in_domain() {
        for &x in &[
            0.0,
            -1.0,
            f64::NEG_INFINITY,
            f64::INFINITY,
            f64::NAN,
            f64::MAX,
            2.001_f64.powf(1023.0),
        ] {
            let got = ceil_power_of_two(x);
            assert!(got.is_nan(), "ceil_power_of_two({}) = {}, want NAN", x, got);
        }
    }

    #[test]
    #[allow(clippy::float_cmp)]
    fn test_ceil_power_of_two_input_is_power_of_two() {
        // Verify that ceil_power_of_two returns its input if the input is a power
        // of 2. The test is done exhaustively for all possible exponents of a
        // float64 value.
        for exponent in -1022..=1023 {
            let x = 2.0_f64.powf(exponent as f64);
            let got = ceil_power_of_two(x);
            let want = x;
            assert_eq!(
                got, want,
                "ceil_power_of_two({}) = {}, want {}",
                x, got, want
            );
        }
    }

    #[test]
    #[allow(clippy::float_cmp)]
    fn test_ceil_power_of_two_input_is_not_power_of_two() {
        // Verify that ceil_power_of_two returns the next power of two for inputs
        // that are different from a power of 2. The test is done exhaustively
        // for all possible exponents of a float64 value.
        for exponent in -1022..=-1 {
            let x = 2.001_f64.powf(exponent as f64);
            let got = ceil_power_of_two(x);
            let want = 2.0_f64.powf(exponent as f64);
            assert_eq!(
                got, want,
                "ceil_power_of_two({}) = {}, want {}",
                x, got, want
            );
        }
        let x = 0.99_f64;
        let got = ceil_power_of_two(x);
        let want = 1.0_f64;
        assert_eq!(
            got, want,
            "ceil_power_of_two({}) = {}, want {}",
            x, got, want
        );
        for exponent in 1..=1022 {
            let x = 2.001_f64.powf(exponent as f64);
            let got = ceil_power_of_two(x);
            let want = 2.0_f64.powf((exponent + 1) as f64);
            assert_eq!(
                got, want,
                "ceil_power_of_two({}) = {}, want {}",
                x, got, want
            );
        }
    }

    #[test]
    fn test_round_to_multiple_granularity_is_one() {
        // Verify that round_to_multiple returns x if granularity is 1.
        for &x in &[0, 1, -1, 2, -2, 648391, -648391] {
            let got = round_to_multiple(x, 1);
            assert_eq!(got, x, "round_to_multiple({}, 1) = {}, want {}", x, got, x,);
        }
    }

    #[test]
    fn test_round_to_multiple_x_is_even() {
        struct TestCase {
            x: i64,
            granularity: i64,
            want: i64,
        }
        for tc in vec![
            TestCase {
                x: 0,
                granularity: 4,
                want: 0,
            },
            TestCase {
                x: 1,
                granularity: 4,
                want: 0,
            },
            TestCase {
                x: 2,
                granularity: 4,
                want: 4,
            },
            TestCase {
                x: 3,
                granularity: 4,
                want: 4,
            },
            TestCase {
                x: 4,
                granularity: 4,
                want: 4,
            },
            TestCase {
                x: -1,
                granularity: 4,
                want: 0,
            },
            TestCase {
                x: -2,
                granularity: 4,
                want: 0,
            },
            TestCase {
                x: -3,
                granularity: 4,
                want: -4,
            },
            TestCase {
                x: -4,
                granularity: 4,
                want: -4,
            },
            TestCase {
                x: 648389,
                granularity: 4,
                want: 648388,
            },
            TestCase {
                x: 648390,
                granularity: 4,
                want: 648392,
            },
            TestCase {
                x: 648391,
                granularity: 4,
                want: 648392,
            },
            TestCase {
                x: 648392,
                granularity: 4,
                want: 648392,
            },
            TestCase {
                x: -648389,
                granularity: 4,
                want: -648388,
            },
            TestCase {
                x: -648390,
                granularity: 4,
                want: -648388,
            },
            TestCase {
                x: -648391,
                granularity: 4,
                want: -648392,
            },
            TestCase {
                x: -648392,
                granularity: 4,
                want: -648392,
            },
        ] {
            let got = round_to_multiple(tc.x, tc.granularity);
            assert_eq!(
                got, tc.want,
                "round_to_multiple({}, {}) = {}, want {}",
                tc.x, tc.granularity, got, tc.want,
            );
        }
    }

    #[test]
    fn test_round_to_multiple_x_is_odd() {
        struct TestCase {
            x: i64,
            granularity: i64,
            want: i64,
        }
        for tc in vec![
            TestCase {
                x: 0,
                granularity: 3,
                want: 0,
            },
            TestCase {
                x: 1,
                granularity: 3,
                want: 0,
            },
            TestCase {
                x: 2,
                granularity: 3,
                want: 3,
            },
            TestCase {
                x: 3,
                granularity: 3,
                want: 3,
            },
            TestCase {
                x: -1,
                granularity: 3,
                want: 0,
            },
            TestCase {
                x: -2,
                granularity: 3,
                want: -3,
            },
            TestCase {
                x: -3,
                granularity: 3,
                want: -3,
            },
            TestCase {
                x: 648391,
                granularity: 3,
                want: 648390,
            },
            TestCase {
                x: 648392,
                granularity: 3,
                want: 648393,
            },
            TestCase {
                x: 648393,
                granularity: 3,
                want: 648393,
            },
            TestCase {
                x: -648391,
                granularity: 3,
                want: -648390,
            },
            TestCase {
                x: -648392,
                granularity: 3,
                want: -648393,
            },
            TestCase {
                x: -648393,
                granularity: 3,
                want: -648393,
            },
        ] {
            let got = round_to_multiple(tc.x, tc.granularity);
            assert_eq!(
                got, tc.want,
                "round_to_multiple({}, {}) = {}, want {}",
                tc.x, tc.granularity, got, tc.want,
            );
        }
    }

    #[test]
    #[allow(clippy::float_cmp)]
    fn test_round_to_multiple_of_power_of_two_x_is_a_multiple() {
        // Verify that round_to_multiple_of_power_of_two returns x if x is a
        // multiple of granularity.
        struct TestCase {
            x: f64,
            granularity: f64,
            want: f64,
        }
        for tc in vec![
            TestCase {
                x: 0.0,
                granularity: 0.5,
                want: 0.0,
            },
            TestCase {
                x: 0.125,
                granularity: 0.125,
                want: 0.125,
            },
            TestCase {
                x: -0.125,
                granularity: 0.125,
                want: -0.125,
            },
            TestCase {
                x: 16512.0,
                granularity: 1.0,
                want: 16512.0,
            },
            TestCase {
                x: -16512.0,
                granularity: 1.0,
                want: -16512.0,
            },
            TestCase {
                x: 3936.0,
                granularity: 32.0,
                want: 3936.0,
            },
            TestCase {
                x: -3936.0,
                granularity: 32.0,
                want: -3936.0,
            },
            TestCase {
                x: 7.9990234375,
                granularity: 0.0009765625,
                want: 7.9990234375,
            },
            TestCase {
                x: -7.9990234375,
                granularity: 0.0009765625,
                want: -7.9990234375,
            },
            TestCase {
                x: i64::MAX as f64,
                granularity: 0.125,
                want: i64::MAX as f64,
            },
            TestCase {
                x: i64::MIN as f64,
                granularity: 0.125,
                want: i64::MIN as f64,
            },
        ] {
            let got = round_to_multiple_of_power_of_two(tc.x, tc.granularity);
            assert_eq!(
                got, tc.want,
                "round_to_multiple_of_power_of_two({}, {}) = {}, want {}",
                tc.x, tc.granularity, got, tc.want,
            );
        }
    }

    #[test]
    #[allow(clippy::float_cmp)]
    fn test_round_to_multiple_of_power_of_two_x_is_not_a_multiple() {
        // Verify that round_to_multiple_of_power_of_two returns the next closest
        // multiple of granularity if x is not already a multiple.
        struct TestCase {
            x: f64,
            granularity: f64,
            want: f64,
        }
        for tc in vec![
            TestCase {
                x: 0.124,
                granularity: 0.125,
                want: 0.125,
            },
            TestCase {
                x: -0.124,
                granularity: 0.125,
                want: -0.125,
            },
            TestCase {
                x: 0.126,
                granularity: 0.125,
                want: 0.125,
            },
            TestCase {
                x: -0.126,
                granularity: 0.125,
                want: -0.125,
            },
            TestCase {
                x: 16512.499,
                granularity: 1.0,
                want: 16512.0,
            },
            TestCase {
                x: -16512.499,
                granularity: 1.0,
                want: -16512.0,
            },
            TestCase {
                x: 16511.501,
                granularity: 1.0,
                want: 16512.0,
            },
            TestCase {
                x: -16511.501,
                granularity: 1.0,
                want: -16512.0,
            },
            TestCase {
                x: 3920.3257,
                granularity: 32.0,
                want: 3936.0,
            },
            TestCase {
                x: -3920.3257,
                granularity: 32.0,
                want: -3936.0,
            },
            TestCase {
                x: 3951.7654,
                granularity: 32.0,
                want: 3936.0,
            },
            TestCase {
                x: -3951.7654,
                granularity: 32.0,
                want: -3936.0,
            },
            TestCase {
                x: 7.9990232355,
                granularity: 0.0009765625,
                want: 7.9990234375,
            },
            TestCase {
                x: -7.9990232355,
                granularity: 0.0009765625,
                want: -7.9990234375,
            },
            TestCase {
                x: 7.9990514315,
                granularity: 0.0009765625,
                want: 7.9990234375,
            },
            TestCase {
                x: -7.9990514315,
                granularity: 0.0009765625,
                want: -7.9990234375,
            },
        ] {
            let got = round_to_multiple_of_power_of_two(tc.x, tc.granularity);
            assert_eq!(
                got, tc.want,
                "round_to_multiple_of_power_of_two({}, {}) = {}, want {}",
                tc.x, tc.granularity, got, tc.want,
            );
        }
    }
}
