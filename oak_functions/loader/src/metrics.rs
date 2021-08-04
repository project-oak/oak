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

use crate::logger::Logger;
use log::Level;
use rand::{distributions::Open01, thread_rng, Rng};
use serde::Deserialize;
use std::{
    collections::{HashMap, HashSet},
    sync::{Arc, Mutex},
};

/// Configuration for differentially-private metrics reporting.
#[derive(Deserialize, Debug)]
#[serde(deny_unknown_fields)]
pub struct PrivateMetricsConfig {
    /// The privacy budget. See
    /// https://desfontain.es/privacy/differential-privacy-in-practice.html for more information
    /// on epsilon-differential privacy and Laplacian noise.
    pub epsilon: f64,
    /// The number of requests that will be aggregated into each batch.
    pub batch_size: usize,
    /// The labels for events that can be reported. Any other events will be ignored.
    pub allowed_labels: Vec<String>,
}

/// Aggregator for count-based differentially private metrics. The request metrics are released in
/// aggregated batches after differentially private noise has been added. Once the number of
/// requests reaches the batch threshold the metrics are logged and the request count and bucket
/// counts are reset to 0.
pub struct PrivateMetricsAggregator {
    /// The request count.
    count: usize,
    /// The privacy budget.
    epsilon: f64,
    /// The number of requests that will be aggregated into each batch.
    batch_size: usize,
    /// The storage for event count buckets.
    events: HashMap<String, usize>,
    logger: Logger,
}

impl PrivateMetricsAggregator {
    pub fn new(config: &PrivateMetricsConfig, logger: Logger) -> anyhow::Result<Self> {
        anyhow::ensure!(config.epsilon > 0.0, "Epsilon must be positive.");
        Ok(Self {
            count: 0,
            epsilon: config.epsilon,
            batch_size: config.batch_size,
            events: config
                .allowed_labels
                .iter()
                .map(|label| (label.clone(), 0))
                .collect(),
            logger,
        })
    }

    /// Reports new events that should be included in the aggregated counts. If the batch threshold
    /// is reached the metrics batch is logged and the request count and bucket counts are reset.
    pub fn report_events(&mut self, events: HashSet<String>) {
        self.count += 1;
        for (label, count) in self.events.iter_mut() {
            if events.contains(label) {
                *count += 1;
            }
        }

        if self.count == self.batch_size {
            self.log_events();
        }
    }

    /// Logs the current bucket counts after adding appropriate noise, resets the request count and
    /// bucket counts to 0.
    fn log_events(&mut self) {
        let counts: Vec<String> = self
            .events
            .iter()
            .map(|(label, count)| {
                let value = self.add_laplace_noise(*count);
                format!("{}={}", label, value)
            })
            .collect();
        // The differentially private metrics can be treated as non-sensitive information and
        // therefore logged as public. This assumes that the client has validated that the
        // configured privacy budget provides sufficient privacy protection before sending any data
        // to the server.
        self.logger.log_public(
            Level::Info,
            &format!(
                "metrics export: batch size: {}; counts: {}",
                self.count,
                counts.join(";"),
            ),
        );
        self.reset();
    }

    /// Resets the request count and all the bucket counts to 0.
    fn reset(&mut self) {
        self.count = 0;
        for (_, count) in self.events.iter_mut() {
            *count = 0;
        }
    }

    /// Exports the request count and bucket counts without adding any noise for use in testing.
    /// Also resets the request count and bucket counts to 0.
    #[cfg(test)]
    pub fn get_events_for_test(&mut self) -> (usize, Vec<(String, usize)>) {
        let count = self.count;
        let buckets = self
            .events
            .iter()
            .map(|(label, count)| (label.to_string(), *count))
            .collect();
        self.reset();
        (count, buckets)
    }

    /// Adds Laplacian noise to a count. The Laplacian noise is sampled by sampling from a uniform
    /// distribution and calculating the inverse of the Laplace cummulative distribution function on
    /// the sampled value. Rounding of the noise is allowed as acceptable post-processing.
    pub fn add_laplace_noise(&self, count: usize) -> i64 {
        // Split the budget evenly over all of the labeled buckets.
        let beta = self.events.len() as f64 / self.epsilon;
        let p: f64 = thread_rng().sample(Open01);
        count as i64 + Self::inverse_laplace(beta, p).round() as i64
    }

    /// Applies the inverse of the Laplace cummulative distribution function with mu = 0.
    ///
    /// See https://en.wikipedia.org/wiki/Laplace_distribution
    fn inverse_laplace(beta: f64, p: f64) -> f64 {
        if p >= 1.0 {
            return f64::INFINITY;
        }
        if p <= 0.0 {
            return f64::NEG_INFINITY;
        }
        let u = p - 0.5;
        -beta * u.signum() * (1.0 - 2.0 * u.abs()).ln()
    }
}

/// Proxy for use by request handler instances to push metrics to the `PrivateMetricsAggregator`.
pub struct PrivateMetricsProxy {
    aggregator: Arc<Mutex<PrivateMetricsAggregator>>,
    events: HashSet<String>,
}

impl PrivateMetricsProxy {
    pub fn new(aggregator: Arc<Mutex<PrivateMetricsAggregator>>) -> Self {
        Self {
            aggregator,
            events: HashSet::new(),
        }
    }

    /// Adds an event to the set of reported events if it was not previously added.
    pub fn report_event(&mut self, label: &str) {
        if !self.events.contains(label) {
            self.events.insert(label.to_owned());
        }
    }

    /// Consumes the proxy and publishes the data to the aggregator.
    pub fn publish(self) {
        if let Ok(mut aggregator) = self.aggregator.lock() {
            aggregator.report_events(self.events);
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_private_metrics_aggregator() {
        let config = new_metrics_config(1.0, vec!["a", "b", "c", "d"]);
        let aggregator = Arc::new(Mutex::new(
            PrivateMetricsAggregator::new(&config, Logger::for_test()).unwrap(),
        ));

        let mut proxy1 = PrivateMetricsProxy::new(aggregator.clone());
        proxy1.report_event("a");
        proxy1.publish();
        let mut proxy2 = PrivateMetricsProxy::new(aggregator.clone());
        proxy2.report_event("a");
        proxy2.report_event("b");
        proxy2.publish();
        let mut proxy3 = PrivateMetricsProxy::new(aggregator.clone());
        proxy3.report_event("c");
        proxy3.report_event("b");
        proxy3.report_event("c");
        proxy3.publish();
        let mut proxy4 = PrivateMetricsProxy::new(aggregator.clone());
        proxy4.report_event("a");
        proxy4.report_event("e");
        proxy4.publish();
        let (count, mut buckets) = aggregator.lock().unwrap().get_events_for_test();
        buckets.sort();

        assert_eq!(4, count);
        assert_eq!(
            vec![
                ("a".to_string(), 3),
                ("b".to_string(), 2),
                ("c".to_string(), 1),
                ("d".to_string(), 0),
            ],
            buckets
        );
    }

    fn new_metrics_config<'a, T>(epsilon: f64, labels: T) -> PrivateMetricsConfig
    where
        T: IntoIterator<Item = &'a str>,
    {
        PrivateMetricsConfig {
            epsilon,
            batch_size: usize::MAX,
            allowed_labels: labels.into_iter().map(|label| label.to_owned()).collect(),
        }
    }

    #[test]
    fn test_laplace_noise() {
        // Run many times and make sure the shape of the histogram looks roughly right.
        let iterations = 1_000_000;
        // Check the 0 bucket and 5 buckets either side.
        let offset = 5;
        // Bucket is allowed up to 10% above or below expected size.
        let margin = 0.1_f64;
        let epsilon = 1.0_f64;
        let config = new_metrics_config(epsilon, vec!["a"]);
        let aggregator = PrivateMetricsAggregator::new(&config, Logger::for_test()).unwrap();

        let beta = 1.0 / epsilon;
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
            let noise = aggregator.add_laplace_noise(0);
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
