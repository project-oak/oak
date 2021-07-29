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
use serde::Deserialize;
use std::{
    collections::{HashMap, HashSet},
    sync::{Arc, Mutex},
};

/// Configuration for differentially-private metrics reporting
#[derive(Deserialize, Debug)]
#[serde(deny_unknown_fields)]
pub struct PrivateMetricsConfig {
    pub epsilon: f32,
    pub batch_size: usize,
    pub allowed_labels: Vec<String>,
}

/// Aggregator for count-based differentially private metrics.
pub struct PrivateMetricsAggregator {
    count: usize,
    epsilon: f32,
    batch_size: usize,
    allowed_labels: HashSet<String>,
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
            events: HashMap::new(),
            logger,
        }
    }

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

    fn export_events(&mut self) {
        let mut counts = Vec::new();
        for label in &self.allowed_labels {
            let value = self.add_laplace_noise(*self.events.get(label).unwrap_or(&0));
            counts.push(format!("{}={}", label, value));
        }
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

    fn add_laplace_noise(&self, count: usize) -> i64 {
        // TODO: Add Laplace noise based on epsilon.
        count as i64 + self.epsilon.round() as i64
    }
}

/// Proxy for use by request handler instances to push metrics to the `MerticsAggregator`.
pub struct PrivateMetricsProxy {
    aggregator: Arc<Mutex<PrivateMetricsAggregator>>,
    events: HashSet<String>,
}

impl PrivateMetricsProxy {
    pub fn new(aggregator: Arc<Mutex<PrivateMetricsAggregator>>, events: HashSet<String>) -> Self {
        Self { aggregator, events }
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
