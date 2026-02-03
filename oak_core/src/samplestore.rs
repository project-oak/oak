//
// Copyright 2022 The Project Oak Authors
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

//! Probabilistic sample store to compute percentiles over some measurement.

/// Basic Probabilistic sample store to compute percentiles
///
/// N is the number of elements kept in memory; it must be larger
/// than 0. The array is allocated statically; SampleStore does not use heap
/// allocation.
#[derive(Debug, PartialEq)]
pub struct StaticSampleStore<const N: usize> {
    data: [u64; N],
    samples: usize,
}

pub trait SampleStore {
    /// Records a new data point value.
    ///
    /// If the store has already been filled, it will probabilistically replace
    /// one of the existing entries based on reservoir sampling.
    fn record(&mut self, value: u64);

    /// Gets the n-th percentile.
    ///
    /// n needs to be between 0 and 100, otherwise None is returned; also,
    /// the store must have at least one recorded data point.
    fn percentile(&self, n: f64) -> Option<u64>;
}

impl<const N: usize> StaticSampleStore<N> {
    pub fn new() -> Option<Self> {
        if N == 0 { None } else { Some(Self { data: [0; N], samples: 0 }) }
    }
}

impl<const N: usize> SampleStore for StaticSampleStore<N> {
    fn record(&mut self, value: u64) {
        // Reservoir sampling. See https://en.wikipedia.org/wiki/Reservoir_sampling for the description.
        let j = if self.samples < self.data.len() {
            self.samples
        } else {
            // generate a random number in [0..samples)
            let mut buf = [0u8; 8];
            getrandom::getrandom(&mut buf[..]).unwrap();
            // This will introduce a small bias, but it should be small enough for our use
            // case.
            usize::from_ne_bytes(buf) % self.samples
        };

        // if j < N then replace data[j]
        if let Some(elem) = self.data.get_mut(j) {
            *elem = value;
        }

        self.samples += 1;
    }

    fn percentile(&self, n: f64) -> Option<u64> {
        if n > 100.0 || self.samples == 0 {
            return None;
        }
        let mut array = self.data;
        // If we've had more samples, cap the size of the slice at N.
        let size = core::cmp::min(N, self.samples);
        let slice = &mut array[..size];
        slice.sort_unstable();
        // samples > 0 (because of the check above) and N > 0 (as otherwise `new()`
        // would fail), so `size` will always be at least 1.
        let index = (size as f64 - 1.0) * n / 100.0;
        slice.get(index as usize).copied()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    pub fn empty() {
        let store = StaticSampleStore::<1>::new().unwrap();
        assert_eq!(store.percentile(10.0), None)
    }

    #[test]
    pub fn invalid() {
        let store = StaticSampleStore::<0>::new();
        assert_eq!(store, None)
    }

    #[test]
    pub fn one_entry() {
        let mut store = StaticSampleStore::<1>::new().unwrap();
        store.record(10);
        assert_eq!(store.percentile(0.0), Some(10));
        assert_eq!(store.percentile(50.0), Some(10));
        assert_eq!(store.percentile(100.0), Some(10));
        assert_eq!(store.percentile(100.1), None);
        assert_eq!(store.percentile(200.0), None);
    }

    #[test]
    pub fn filled() {
        let mut store = StaticSampleStore::<10>::new().unwrap();
        for x in 1..=10 {
            store.record(x);
        }
        assert_eq!(store.percentile(0.0), Some(1));
        assert_eq!(store.percentile(50.0), Some(5));
        assert_eq!(store.percentile(100.0), Some(10));
    }

    #[test]
    pub fn probabilistic_replacement() {
        let mut store = StaticSampleStore::<10>::new().unwrap();
        (1..=10).for_each(|_| store.record(0));
        // This will now get difficult, as replacing entries is probabilistic. But we
        // should get at least one hit.
        (1..=10).for_each(|_| store.record(10));
        assert_eq!(store.percentile(100.0), Some(10));
    }

    #[test]
    pub fn large() {
        let mut store = StaticSampleStore::<1000>::new().unwrap();
        (1..=1000).for_each(|x| store.record(x));
        assert_eq!(store.percentile(0.0), Some(1));
        assert_eq!(store.percentile(32.5), Some(325));
        assert_eq!(store.percentile(50.0), Some(500));
        assert_eq!(store.percentile(75.0), Some(750));
        assert_eq!(store.percentile(99.0), Some(990));
        assert_eq!(store.percentile(99.9), Some(999));
        assert_eq!(store.percentile(99.999), Some(999));
        assert_eq!(store.percentile(100.0), Some(1000));
    }
}
