//
// Copyright 2020 The Project Oak Authors
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

use std::mem::replace;

/// Represents a data structure with a single associative binary operation (`combine`)
/// and an `identity` element.
/// https://en.wikipedia.org/wiki/Monoid
pub trait Monoid {
    fn identity() -> Self;
    fn combine(&self, other: &Self) -> Self;
}

/// Generic data structure that combines data values and counts the number of provided data samples.
/// It can also reveal an aggregated value only when there are enough data samples
/// (more or equal to `sample_threshold`).
pub struct ThresholdAggregator<T: Monoid> {
    /// Current aggregated value.
    current_value: T,
    /// Number of contributed data samples.
    sample_count: u64,
    /// The minimal number of samples (inclusive) that must be collected before revealing the
    /// aggregation.
    sample_threshold: u64,
}

impl<T: Monoid> ThresholdAggregator<T> {
    pub fn new(threshold: u64) -> Self {
        ThresholdAggregator {
            current_value: Monoid::identity(),
            sample_count: 0,
            sample_threshold: threshold,
        }
    }

    /// Combines a new sample with the current aggregated value.
    pub fn submit(&mut self, sample: &T) {
        self.current_value = self.current_value.combine(sample);
        self.sample_count += 1;
    }

    /// Returns the current aggregated value if the number of collected samples is at least
    /// `sample_threshold`.
    pub fn get(&self) -> Option<&T> {
        if self.sample_count >= self.sample_threshold {
            Some(&self.current_value)
        } else {
            None
        }
    }

    /// Deletes current aggregated value and returns it if the number of collected samples is at
    /// least `sample_threshold`.
    pub fn take(&mut self) -> Option<T> {
        if self.sample_count >= self.sample_threshold {
            Some(replace(&mut self.current_value, Monoid::identity()))
        } else {
            None
        }
    }
}
