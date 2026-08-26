//
// Copyright 2026 The Project Oak Authors
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

//! Summarising a metric over repeated runs of the same benchmark.
//!
//! A single run of a microbenchmark is not a measurement, it is one sample from
//! a right-skewed distribution. Scheduling, core migration, frequency changes
//! and a noisy neighbour all push a run slower and nothing pushes one faster,
//! so the tail is long in one direction only. Reporting one number hides that
//! entirely, and reporting a mean tracks the tail rather than the typical cost.
//!
//! So the suite reports the sample count, the median and the quartiles. That
//! combination is what eBACS publishes for its cycles-per-byte tables
//! (<https://bench.cr.yp.to/results-hash.html>), which is the closest published
//! precedent for the crypto rows here.
//!
//! Stating the sample count matters as much as the spread. In an audit of fifty
//! papers from the top four security venues, van der Kouwe et al. found "no
//! indication of significance of data" in thirty-eight of them, the most
//! widespread of the twenty-two reporting flaws they measured
//! (<https://arxiv.org/abs/1801.02381>).

/// Order statistics of one metric over repeated runs.
///
/// Deliberately not a mean and a standard deviation: both assume a symmetric
/// distribution, and these are not symmetric. See the module documentation.
#[derive(Debug, Clone, Copy, PartialEq)]
pub struct Distribution {
    /// Number of samples. Reported alongside every figure, because a median of
    /// three and a median of thirty are not the same claim.
    pub n: usize,
    pub min: f64,
    /// First quartile.
    pub q1: f64,
    pub median: f64,
    /// Third quartile.
    pub q3: f64,
    pub max: f64,
}

impl Distribution {
    /// Summarise a set of samples.
    ///
    /// Returns `None` for an empty input rather than inventing a zero, so that
    /// a benchmark which produced no usable samples cannot be formatted as if
    /// it had produced a measurement of zero.
    ///
    /// Quantiles are linearly interpolated at position `p * (n - 1)` over the
    /// sorted samples, the most common convention and the default in NumPy and
    /// in R's type 7. With the sample counts used here the choice of
    /// convention moves a quartile by more than the quantity being measured in
    /// some cases, so it is stated rather than left implicit.
    ///
    /// Samples are sorted in place; the caller's ordering is not preserved.
    pub fn from_samples(samples: &mut [f64]) -> Option<Self> {
        if samples.is_empty() {
            return None;
        }
        // `total_cmp` rather than `partial_cmp`, so a NaN sorts to one end
        // instead of panicking or producing an arbitrary order.
        samples.sort_by(f64::total_cmp);

        Some(Self {
            n: samples.len(),
            min: samples[0],
            q1: quantile(samples, 0.25),
            median: quantile(samples, 0.5),
            q3: quantile(samples, 0.75),
            max: samples[samples.len() - 1],
        })
    }

    /// Interquartile range, the spread of the middle half of the samples.
    pub fn iqr(&self) -> f64 {
        self.q3 - self.q1
    }

    /// Interquartile range as a fraction of the median.
    ///
    /// The number to look at before quoting a result: an effect smaller than
    /// this is not distinguishable from run-to-run variation. Returns `None`
    /// for a zero median, where a relative figure has no meaning.
    pub fn relative_iqr(&self) -> Option<f64> {
        if self.median == 0.0 { None } else { Some(self.iqr() / self.median) }
    }

    /// Full range as a fraction of the median, including both tails.
    pub fn relative_range(&self) -> Option<f64> {
        if self.median == 0.0 { None } else { Some((self.max - self.min) / self.median) }
    }
}

/// Linearly interpolated quantile over an already-sorted slice.
///
/// `sorted` must be non-empty and ascending.
fn quantile(sorted: &[f64], p: f64) -> f64 {
    debug_assert!(!sorted.is_empty());
    if sorted.len() == 1 {
        return sorted[0];
    }
    let position = p * (sorted.len() - 1) as f64;
    let lower = position.floor() as usize;
    let upper = position.ceil() as usize;
    if lower == upper {
        return sorted[lower];
    }
    let weight = position - lower as f64;
    sorted[lower] * (1.0 - weight) + sorted[upper] * weight
}

/// Geometric mean of a set of ratios.
///
/// Aggregating overhead ratios with an arithmetic mean makes the result depend
/// on which side was picked as the baseline, and van der Kouwe et al. class
/// that as a soundness flaw — explicitly including "other averaging strategies
/// such as using the median". Only the geometric mean is appropriate for
/// averaging ratios. Per-benchmark medians of raw latencies are unaffected by
/// this; it applies to summarising a table of ratios into one number.
///
/// Returns `None` for an empty input, and for any ratio that is not a positive
/// real number — zero, negative and NaN alike — where the geometric mean is
/// undefined.
pub fn geometric_mean(ratios: &[f64]) -> Option<f64> {
    // Negating `all` rather than asking for `any(|r| *r <= 0.0)`: NaN compares
    // false against every operand, so only this form rejects it.
    if ratios.is_empty() || !ratios.iter().all(|r| *r > 0.0) {
        return None;
    }
    // Summing logarithms rather than multiplying: the product of a few dozen
    // ratios can overflow or lose precision, the sum of their logs cannot.
    let sum: f64 = ratios.iter().map(|r| r.ln()).sum();
    Some((sum / ratios.len() as f64).exp())
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn empty_input_has_no_distribution() {
        assert_eq!(Distribution::from_samples(&mut []), None);
    }

    #[test]
    fn a_single_sample_is_its_own_every_statistic() {
        let d = Distribution::from_samples(&mut [7.0]).unwrap();
        assert_eq!(d.n, 1);
        assert_eq!((d.min, d.q1, d.median, d.q3, d.max), (7.0, 7.0, 7.0, 7.0, 7.0));
        assert_eq!(d.iqr(), 0.0);
    }

    #[test]
    fn quartiles_follow_the_documented_convention() {
        // Positions 0.75, 1.5 and 2.25 over [1, 2, 3, 4].
        let d = Distribution::from_samples(&mut [4.0, 1.0, 3.0, 2.0]).unwrap();
        assert_eq!(d.n, 4);
        assert_eq!(d.min, 1.0);
        assert_eq!(d.q1, 1.75);
        assert_eq!(d.median, 2.5);
        assert_eq!(d.q3, 3.25);
        assert_eq!(d.max, 4.0);
    }

    #[test]
    fn an_odd_count_takes_the_middle_sample() {
        let d = Distribution::from_samples(&mut [5.0, 1.0, 3.0]).unwrap();
        assert_eq!(d.median, 3.0);
    }

    /// The case the suite exists to catch: a right-skewed sample, where the
    /// bulk of the runs sit in a narrow band and a handful of stragglers drag
    /// the maximum well away from it. These are twenty real native `sha256`
    /// repetitions.
    #[test]
    fn a_skewed_sample_separates_median_from_range() {
        let mut samples = vec![
            2088.0, 2091.0, 2094.0, 2097.0, 2101.0, 2104.0, 2107.0, 2109.0, 2111.0, 2113.0, 2117.0,
            2121.0, 2126.0, 2130.0, 2133.0, 2201.0, 2233.0, 2237.0, 2280.0, 2327.0,
        ];
        let d = Distribution::from_samples(&mut samples).unwrap();
        assert_eq!(d.n, 20);
        assert_eq!(d.min, 2088.0);
        assert_eq!(d.max, 2327.0);
        // Exact quantiles under the p*(n-1) convention this module documents.
        assert_eq!(d.q1, 2103.25);
        assert_eq!(d.median, 2115.0);
        assert_eq!(d.q3, 2150.0);
        // The middle half spans 2.2% of the median, the full range 11.3%. A
        // single draw from this sample could land anywhere in the wider band,
        // which is precisely what reporting one number hides.
        assert!(
            d.relative_range().unwrap() > 5.0 * d.relative_iqr().unwrap(),
            "IQR {:?}, range {:?}",
            d.relative_iqr(),
            d.relative_range()
        );
    }

    #[test]
    fn a_zero_median_has_no_relative_spread() {
        let d = Distribution::from_samples(&mut [0.0, 0.0, 0.0]).unwrap();
        assert_eq!(d.relative_iqr(), None);
        assert_eq!(d.relative_range(), None);
    }

    #[test]
    fn geometric_mean_is_symmetric_in_the_baseline() {
        let forward = geometric_mean(&[2.0, 0.5, 4.0]).unwrap();
        let inverted = geometric_mean(&[0.5, 2.0, 0.25]).unwrap();
        // Inverting every ratio must invert the summary. An arithmetic mean
        // does not have this property, which is why it is the wrong tool.
        assert!((forward * inverted - 1.0).abs() < 1e-12, "{forward} vs {inverted}");
    }

    #[test]
    fn geometric_mean_rejects_undefined_input() {
        assert_eq!(geometric_mean(&[]), None);
        assert_eq!(geometric_mean(&[1.0, 0.0]), None);
        assert_eq!(geometric_mean(&[1.0, -2.0]), None);
        assert_eq!(geometric_mean(&[1.0, f64::NAN]), None);
    }
}
