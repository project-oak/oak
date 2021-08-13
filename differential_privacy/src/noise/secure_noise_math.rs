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
