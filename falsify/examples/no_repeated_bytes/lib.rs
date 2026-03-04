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

//! Example falsify claim: "the input contains no repeated consecutive bytes."
//!
//! - `Intact` when all adjacent bytes differ (e.g. `[1, 2, 3]`).
//! - `Falsified` when any two consecutive bytes are equal (e.g. `[1, 1, 3]`).
//!
//! This is a trivially falsifiable claim useful for testing the falsify_wasm
//! runner.

/// Claim: the input contains no repeated consecutive bytes.
pub struct NoRepeatedBytes;

impl falsify::Claim for NoRepeatedBytes {
    fn evaluate(&self, input: &[u8]) -> Result<falsify::Evaluation, Box<dyn core::error::Error>> {
        for window in input.windows(2) {
            if window[0] == window[1] {
                return Ok(falsify::Evaluation::Falsified);
            }
        }
        Ok(falsify::Evaluation::Intact)
    }
}

#[cfg(test)]
mod tests {
    use falsify::Claim;

    use super::*;

    #[test]
    fn empty_input_is_intact() {
        assert_eq!(NoRepeatedBytes.evaluate(b"").unwrap(), falsify::Evaluation::Intact);
    }

    #[test]
    fn single_byte_is_intact() {
        assert_eq!(NoRepeatedBytes.evaluate(b"a").unwrap(), falsify::Evaluation::Intact);
    }

    #[test]
    fn distinct_bytes_are_intact() {
        assert_eq!(NoRepeatedBytes.evaluate(b"abcd").unwrap(), falsify::Evaluation::Intact);
    }

    #[test]
    fn repeated_bytes_falsify() {
        assert_eq!(NoRepeatedBytes.evaluate(b"aab").unwrap(), falsify::Evaluation::Falsified);
    }

    #[test]
    fn repeated_at_end_falsifies() {
        assert_eq!(NoRepeatedBytes.evaluate(b"abb").unwrap(), falsify::Evaluation::Falsified);
    }
}
