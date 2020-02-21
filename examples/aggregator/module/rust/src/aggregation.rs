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

pub trait Monoid {
    fn identity() -> Self;
    fn combine(&self, other: &Self) -> Self;
    fn len() -> usize;
}

pub struct Aggregation<T: Monoid> {
    /// Aggregated data.
    data: T,
    /// Number of contributed data samples.
    sample_number: u64,
    /// Minimal allowed number of samples ... before realising the aggregation.
    sample_threshold: u64,
}

impl<T: Monoid + Copy> Aggregation<T> {
    pub fn new(threshold: u64) -> Self {
        Aggregation {
            data: Monoid::identity(),
            sample_number: 0,
            sample_threshold: threshold,
        }
    }

    pub fn add(&mut self, sample: &T) {
        self.data = self.data.combine(sample);
        self.sample_number += 1;
    }

    pub fn get(&self) -> Option<T> {
        if self.sample_number >= self.sample_threshold {
            Some(self.data)
        } else {
            None
        }
    }
}
