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

use super::*;

/// Implementation of an additive monoid over i32 values for testing.
impl Monoid for i32 {
    fn identity() -> Self {
        0
    }

    fn combine(&self, other: &Self) -> Self {
        self + other
    }
}

#[test]
fn aggregator() {
    let mut aggregator = ThresholdAggregator::new(5);
    assert_eq!(AggregatorResult::BelowThreshold, aggregator.submit(&1));
    assert_eq!(AggregatorResult::BelowThreshold, aggregator.submit(&10));
    assert_eq!(AggregatorResult::BelowThreshold, aggregator.submit(&100));
    assert_eq!(AggregatorResult::BelowThreshold, aggregator.submit(&1000));
    assert_eq!(
        AggregatorResult::AggregatedValue(&11111),
        aggregator.submit(&10000)
    );
    assert_eq!(AggregatorResult::Exhausted, aggregator.submit(&100000));
    assert_eq!(AggregatorResult::Exhausted, aggregator.submit(&1000000));
}
