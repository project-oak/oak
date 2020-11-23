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

#[cfg(test)]
mod tests;

/// Represents a data structure with a single associative binary operation (`combine`)
/// and an `identity` element.
/// https://en.wikipedia.org/wiki/Monoid
pub trait Monoid {
    fn identity() -> Self;
    fn combine(&self, other: &Self) -> Self;
}

/// Generic data structure that combines data values and counts the number of provided data samples.
/// It can also reveal an aggregated value only when there are enough data samples (equal to
/// `sample_threshold`).
pub struct ThresholdAggregator<T: Monoid> {
    /// Current aggregated value.
    current_value: T,
    /// Number of contributed data samples.
    sample_count: u64,
    /// The exact number of samples that must be collected before revealing the aggregation.
    sample_threshold: u64,
    /// Whether the aggregated value has already been extracted from this instance.
    exhausted: bool,
}

#[derive(Debug, PartialEq)]
pub enum AggregatorResult<T> {
    /// The aggregator has not reached the specified sample threshold yet.
    BelowThreshold,
    /// The aggregator has already output an aggregated value.
    Exhausted,
    /// The aggregated value computed by combining the current number of samples,  equal to the
    /// specified sample threshold.
    AggregatedValue(T),
}

impl<T: Monoid> ThresholdAggregator<T> {
    pub fn new(threshold: u64) -> Self {
        ThresholdAggregator {
            current_value: Monoid::identity(),
            sample_count: 0,
            sample_threshold: threshold,
            exhausted: false,
        }
    }

    /// Combines a new sample with the current aggregated value.
    ///
    /// If the number of current samples (including the current one) is exactly `sample_threshold`,
    /// then returns the current aggregated value and sets the status of the aggregator to
    /// exhausted.
    ///
    /// If the aggregator was already exhausted, the new sample is discarded.
    pub fn submit(&mut self, sample: &T) -> AggregatorResult<&T> {
        if self.exhausted {
            AggregatorResult::Exhausted
        } else {
            self.current_value = self.current_value.combine(sample);
            self.sample_count += 1;
            if self.sample_count >= self.sample_threshold {
                // We set the exhausted flag, so that future calls to this method will not return
                // additional values, since that would reveal the actual value of new samples.
                self.exhausted = true;
                AggregatorResult::AggregatedValue(&self.current_value)
            } else {
                AggregatorResult::BelowThreshold
            }
        }
    }
}
