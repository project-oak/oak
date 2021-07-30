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

/// Configuration for differentially-private metrics reporting
#[derive(Deserialize, Debug)]
#[serde(deny_unknown_fields)]
pub struct PrivateMetricsConfig {
    pub epsilon: f64,
    pub batch_size: usize,
    pub allowed_labels: Vec<String>,
}

/// Aggregator for count-based differentially private metrics.
pub struct PrivateMetricsAggregator {
    count: usize,
    epsilon: f64,
    batch_size: usize,
    allowed_labels: HashSet<String>,
    label_count: f64,
    events: HashMap<String, usize>,
    logger: Logger,
}

impl PrivateMetricsAggregator {
    pub fn new(config: &PrivateMetricsConfig, logger: Logger) -> Self {
        Self {
            count: 0,
            epsilon: config.epsilon,
            batch_size: config.batch_size,
            allowed_labels: config
                .allowed_labels
                .iter()
                .map(|label| label.clone())
                .collect(),
            label_count: config.allowed_labels.iter().count() as f64,
            events: HashMap::new(),
            logger,
        }
    }

    /// Reports new events that should be included in the aggregated counts.
    pub fn report_events(&mut self, events: HashSet<String>) {
        self.count += 1;
        for label in self.allowed_labels.intersection(&events) {
            if let Some(bucket) = self.events.get_mut(label) {
                *bucket += 1;
            } else {
                self.events.insert(label.to_owned(), 1);
            }
        }

        if self.count == self.batch_size {
            self.export_events();
        }
    }

    /// Logs the current counts after adding appropriate noise, resets the batch count to 0 and
    /// clears the aggregated data.
    fn export_events(&mut self) {
        let counts: Vec<String> = self
            .allowed_labels
            .iter()
            .map(|label| {
                let value = self.add_laplace_noise(*self.events.get(label).unwrap_or(&0));
                format!("{}={}", label, value)
            })
            .collect();
        self.logger.log_public(
            Level::Info,
            &format!(
                "metrics export: batch size: {}; counts: {}",
                self.count,
                counts.join(";"),
            ),
        );
        self.count = 0;
        self.events.clear();
    }

    /// Exports the batch count and bucket counts without adding any noise for use in testing. Also
    /// resets the batch count to 0 and clears the aggregated data.
    pub fn export_events_for_test(&mut self) -> (usize, Vec<(String, usize)>) {
        let count = self.count;
        let buckets = self
            .allowed_labels
            .iter()
            .map(|label| (label.to_string(), *self.events.get(label).unwrap_or(&0)))
            .collect();
        self.count = 0;
        self.events.clear();
        (count, buckets)
    }

    /// Adds Laplacian noise to a count. The Laplacian noise is sampled by sampling from a uniform
    /// distribution and calculating inverse the of the Laplace cummulative distribution function on
    /// the sampled value. Rounding of the noise is allowed as acceptable post-processing.
    pub fn add_laplace_noise(&self, count: usize) -> i64 {
        // If epsilon is 0 (or smaller), always return a fixed value so we don't leak any
        // information.
        if self.epsilon <= 0.0 {
            return i64::MIN;
        }
        // Split the budget evenly over all of the labeled buckets.
        let beta = self.label_count / self.epsilon;
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

/// Proxy for use by request handler instances to push metrics to the `MerticsAggregator`.
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
