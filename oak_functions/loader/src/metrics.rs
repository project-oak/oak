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

use crate::{
    logger::Logger,
    server::{
        AbiPointer, AbiPointerOffset, BoxedExtension, ExtensionFactory, OakApiNativeExtension,
        WasmState, ABI_USIZE,
    },
};
use oak_functions_abi::proto::OakStatus;

use anyhow::Context;
use log::Level;
use rand::{distributions::Open01, rngs::StdRng, thread_rng, Rng, SeedableRng};
use serde::Deserialize;
use std::{
    collections::HashMap,
    sync::{Arc, Mutex},
};
use wasmi::ValueType;

/// Host function name for reporting private metrics.
const METRICS_ABI_FUNCTION_NAME: &str = "report_metric";

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
    /// The labels and configurations of buckets for which metrics can be reported.
    pub buckets: HashMap<String, BucketConfig>,
}

impl PrivateMetricsConfig {
    pub fn validate(&self) -> anyhow::Result<()> {
        anyhow::ensure!(self.epsilon > 0.0, "Epsilon must be positive",);
        for (label, bucket_config) in &self.buckets {
            if let BucketConfig::Sum { min, max } = bucket_config {
                anyhow::ensure!(
                    max > min,
                    "Max must be bigger than min for bucket {}",
                    label,
                );
            }
        }
        Ok(())
    }
}

/// Configuration for metrics buckets.
#[derive(Clone, Deserialize, Debug)]
#[serde(deny_unknown_fields)]
pub enum BucketConfig {
    /// A bucket used for counting of events. This is equivalent to `Sum { min: 0, max: 1 }`.
    Count,
    /// A bucket used for summing integer values in a range. Values outside of the range are
    /// clamped at the minimum or maximum values. The noise added to the bucket is scaled by the
    /// size of the range (`max - min`).
    Sum { min: i64, max: i64 },
}

/// Combined configuration and data storage for a metrics bucket.
struct Bucket {
    config: BucketConfig,
    value: i64,
}

impl Bucket {
    /// Adds the input value to the bucket value. If the value is outside of the configured range it
    /// is clamped to the minimum or maximum.
    fn add(&mut self, input: i64) {
        self.value += match self.config {
            BucketConfig::Count => input.clamp(0, 1),
            BucketConfig::Sum { min, max } => input.clamp(min, max),
        }
    }
}

/// Aggregator for count- and sum-based differentially private metrics. The request metrics are
/// released in aggregated batches after differentially private noise has been added. Once the
/// number of requests reaches the batch threshold the metrics are logged and the request count and
/// bucket counts are reset to 0.
pub struct PrivateMetricsAggregator {
    /// The request count.
    count: usize,
    /// The privacy budget.
    epsilon: f64,
    /// The number of requests that will be aggregated into each batch.
    batch_size: usize,
    /// The storage for the buckets.
    buckets: HashMap<String, Bucket>,
    /// The random number generator used for sampling the noise.
    rng: StdRng,
}

impl PrivateMetricsAggregator {
    pub fn new(config: &PrivateMetricsConfig) -> anyhow::Result<Self> {
        Self::new_with_rng(
            config,
            StdRng::from_rng(thread_rng()).context("Couldn't create rng")?,
        )
    }

    #[cfg(test)]
    pub fn new_for_test(config: &PrivateMetricsConfig, rng: StdRng) -> anyhow::Result<Self> {
        Self::new_with_rng(config, rng)
    }

    fn new_with_rng(config: &PrivateMetricsConfig, rng: StdRng) -> anyhow::Result<Self> {
        anyhow::ensure!(config.epsilon > 0.0, "Epsilon must be positive.");
        Ok(Self {
            count: 0,
            epsilon: config.epsilon,
            batch_size: config.batch_size,
            buckets: config
                .buckets
                .iter()
                .map(|(label, bucket_config)| {
                    (
                        label.clone(),
                        Bucket {
                            config: bucket_config.clone(),
                            value: 0,
                        },
                    )
                })
                .collect(),
            rng,
        })
    }

    /// Reports new metrics for a single request that should be included in the aggregated counts.
    ///
    /// If the data contains entries with labels for buckets that are not configured those entries
    /// are ignored. If data does not include entries for some configured buckets, it will be
    /// treated as if values of 0 (or the minimum values where the minimum values are larger than 0)
    /// were included for those buckets.
    ///
    /// If the number of requests do not yet match the batch size `None` is returned. If the
    /// batch threshold is reached the aggregated metrics for the batch are returned and the
    /// request count and bucket values are reset to 0. Each Wasm instance can only call this
    /// function once, as it consumes its PrivateMetricsProxy in the process of reporting metrics.
    ///
    /// Laplacian noise is added to each of the aggregated bucket values that are returned. The
    /// noise is scaled by the size of the range allowed for the bucket.
    ///
    /// The metrics are returned as a tuple containing the batch size and a vector of tuples
    /// cotaining the label and value for each bucket.
    pub fn report_metrics(
        &mut self,
        data: HashMap<String, i64>,
    ) -> Option<(usize, Vec<(String, i64)>)> {
        self.count += 1;
        for (label, bucket) in self.buckets.iter_mut() {
            bucket.add(*data.get(label).unwrap_or(&0));
        }

        if self.count == self.batch_size {
            let beta = self.buckets.len() as f64 / self.epsilon;
            let rng = &mut self.rng;
            let metrics = self
                .buckets
                .iter()
                .map(|(label, bucket)| {
                    let scale = match bucket.config {
                        BucketConfig::Count => 1.0,
                        BucketConfig::Sum { min, max } => (max - min) as f64,
                    };
                    (
                        label.to_string(),
                        add_laplace_noise(rng, beta, bucket.value, scale),
                    )
                })
                .collect();
            self.reset();
            Some((self.batch_size, metrics))
        } else {
            None
        }
    }

    /// Resets the request count and all the bucket values to 0.
    fn reset(&mut self) {
        self.count = 0;
        for (_, bucket) in self.buckets.iter_mut() {
            bucket.value = 0;
        }
    }
}

/// Adds Laplacian noise with parameter `beta` scaled by `scale` to a `value`. The Laplacian noise
/// is sampled by sampling from a uniform distribution and calculating the inverse of the Laplace
/// cummulative distribution function on the sampled value.
///
/// Rounding of the noise is allowed as acceptable post-processing.
pub fn add_laplace_noise(rng: &mut StdRng, beta: f64, value: i64, scale: f64) -> i64 {
    // Split the budget evenly over all of the labeled buckets.
    let p: f64 = rng.sample(Open01);
    value + (scale * inverse_laplace(beta, p)).round() as i64
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

pub struct PrivateMetricsProxyFactory {
    aggregator: Arc<Mutex<PrivateMetricsAggregator>>,
    logger: Logger,
}

impl PrivateMetricsProxyFactory {
    pub fn new(config: &PrivateMetricsConfig, logger: Logger) -> anyhow::Result<Self> {
        let aggregator = PrivateMetricsAggregator::new(config)?;

        Ok(Self {
            aggregator: Arc::new(Mutex::new(aggregator)),
            logger,
        })
    }
}

impl ExtensionFactory for PrivateMetricsProxyFactory {
    fn create(&self) -> anyhow::Result<BoxedExtension> {
        let metrics_proxy = PrivateMetricsProxy::new(self.aggregator.clone());
        let extension = PrivateMetricsExtension {
            metrics_proxy: Some(metrics_proxy),
            logger: self.logger.clone(),
        };
        Ok(Box::new(extension))
    }
}

struct PrivateMetricsExtension {
    metrics_proxy: Option<PrivateMetricsProxy>,
    logger: Logger,
}

impl PrivateMetricsExtension {
    fn publish_metrics(&mut self) -> anyhow::Result<()> {
        let metrics_proxy = self
            .metrics_proxy
            .take()
            .context("metrics_proxy is consumed")?;

        if let Some((batch_size, metrics)) = metrics_proxy.publish() {
            let buckets: Vec<String> = metrics
                .iter()
                .map(|(label, count)| format!("{}={}", label, count))
                .collect();
            let message = format!(
                "metrics export: batch size: {}; counts: {}",
                batch_size,
                buckets.join(";"),
            );

            // The differentially private metrics can be treated as non-sensitive
            // information and therefore logged as public. This assumes
            // that the client has validated that the configured privacy
            // budget provides sufficient privacy protection before
            // sending any data to the server.
            self.logger.log_public(Level::Info, &message);
        }
        Ok(())
    }
}

impl OakApiNativeExtension for PrivateMetricsExtension {
    fn invoke(
        &mut self,
        wasm_state: &mut WasmState,
        args: wasmi::RuntimeArgs,
    ) -> Result<Result<(), OakStatus>, wasmi::Trap> {
        Ok(report_metric(
            wasm_state,
            self,
            args.nth_checked(0)?,
            args.nth_checked(1)?,
            args.nth_checked(2)?,
        ))
    }

    /// Each Oak Functions application can have at most one instance of PrivateMetricsProxy. So it
    /// is fine to return a constant name in the metadata.
    fn get_metadata(&self) -> (String, wasmi::Signature) {
        let signature = wasmi::Signature::new(
            &[
                ABI_USIZE, // buf_ptr
                ABI_USIZE, // buf_len
                ValueType::I64,
            ][..],
            Some(ValueType::I32),
        );

        (METRICS_ABI_FUNCTION_NAME.to_string(), signature)
    }

    fn terminate(&mut self) -> anyhow::Result<()> {
        self.publish_metrics()
    }
}

/// Proxy for use by request handler instances to push per-request metrics to the
/// `PrivateMetricsAggregator`.
struct PrivateMetricsProxy {
    aggregator: Arc<Mutex<PrivateMetricsAggregator>>,
    data: HashMap<String, i64>,
}

impl PrivateMetricsProxy {
    pub fn new(aggregator: Arc<Mutex<PrivateMetricsAggregator>>) -> Self {
        Self {
            aggregator,
            data: HashMap::new(),
        }
    }

    /// Sets the value for the labeled metric. If a value was previously set for the label it will
    /// be overwritten.
    fn report_metric(&mut self, label: &str, value: i64) {
        self.data.insert(label.to_owned(), value);
    }

    /// Consumes the proxy and publishes the local request-specific data to the aggregator. If
    /// publishing the metrics to the aggregator causes the batch threshold to be reached the
    /// aggregated metrics are returned.
    ///
    /// See [PrivateMetricsAggregator::report_metrics] for more details.
    fn publish(self) -> Option<(usize, Vec<(String, i64)>)> {
        if let Ok(mut aggregator) = self.aggregator.lock() {
            aggregator.report_metrics(self.data)
        } else {
            None
        }
    }
}

/// Corresponds to the host ABI function [`report_metric`](https://github.com/project-oak/oak/blob/main/docs/oak_functions_abi.md#report_metric).
fn report_metric(
    wasm_state: &mut WasmState,
    extension: &mut PrivateMetricsExtension,
    buf_ptr: AbiPointer,
    buf_len: AbiPointerOffset,
    value: i64,
) -> Result<(), OakStatus> {
    let raw_label = wasm_state
        .get_memory()
        .get(buf_ptr, buf_len as usize)
        .map_err(|err| {
            extension.logger.log_sensitive(
                Level::Error,
                &format!(
                    "report_metric(): Unable to read label from guest memory: {:?}",
                    err
                ),
            );
            OakStatus::ErrInvalidArgs
        })?;
    let label = std::str::from_utf8(raw_label.as_slice()).map_err(|err| {
        extension.logger.log_sensitive(
            Level::Warn,
            &format!(
                "report_metric(): Not a valid UTF-8 encoded string: {:?}\nContent: {:?}",
                err, raw_label
            ),
        );
        OakStatus::ErrInvalidArgs
    })?;
    extension
        .logger
        .log_sensitive(Level::Debug, &format!("report_metric(): {}", label));
    if let Some(metrics_proxy) = extension.metrics_proxy.as_mut() {
        metrics_proxy.report_metric(label, value);
        Ok(())
    } else {
        extension
            .logger
            .log_sensitive(Level::Error, "report_metric(): Missing metrics proxy");
        Err(OakStatus::ErrInternal)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use maplit::hashmap;

    #[test]
    fn test_private_metrics_aggregator_count() {
        let epsilon = 1.0;
        let batch_size = 4;
        let config = PrivateMetricsConfig {
            epsilon,
            batch_size,
            buckets: hashmap! {
                "a".to_string() => BucketConfig::Count,
                "b".to_string() => BucketConfig::Count,
                "c".to_string() => BucketConfig::Count,
                "d".to_string() => BucketConfig::Count,
            },
        };
        // Use a fixed seed for the random number generators so the errors are predicatable.
        let seed = 0;
        let rng = StdRng::seed_from_u64(seed);
        let aggregator = Arc::new(Mutex::new(
            PrivateMetricsAggregator::new_for_test(&config, rng).unwrap(),
        ));

        let expected = hashmap! {
            "a".to_string() => 3,
            "b".to_string() => 2,
            "c".to_string() => 1,
            "d".to_string() => 0,
        };
        // Calculate expected noise using a fixed seeded rng.
        let mut rng = StdRng::seed_from_u64(seed);
        let noise: Vec<i64> = (0..4)
            .map(|_| add_laplace_noise(&mut rng, config.buckets.len() as f64 / epsilon, 0, 1.0))
            .collect();

        let mut proxy1 = PrivateMetricsProxy::new(aggregator.clone());
        proxy1.report_metric("a", 1); // Expect +1 for "a".
        assert_eq!(proxy1.publish(), None);
        let mut proxy2 = PrivateMetricsProxy::new(aggregator.clone());
        proxy2.report_metric("a", 2); // Expect +1 for "a".
        proxy2.report_metric("b", 3); // Expect +1 for "b".
        assert_eq!(proxy2.publish(), None);
        let mut proxy3 = PrivateMetricsProxy::new(aggregator.clone());
        proxy3.report_metric("c", 1); // Overwritten.
        proxy3.report_metric("b", 1); // Expect +1 for "b".
        proxy3.report_metric("c", 3); // Expect +1 for "c".
        assert_eq!(proxy3.publish(), None);
        let mut proxy4 = PrivateMetricsProxy::new(aggregator);
        proxy4.report_metric("a", 1); // Expect +1 for "a".
        proxy4.report_metric("e", 1); // Ignored.
        let (count, buckets) = proxy4.publish().unwrap();

        assert_eq!(batch_size, count);
        for (index, (label, value)) in buckets.iter().enumerate() {
            println!(
                "Label: {}, Actual: {}, Expected: {}, Noise: {}",
                label,
                value,
                expected.get(label).unwrap(),
                noise[index]
            );
            assert_eq!(*value, expected.get(label).unwrap() + noise[index]);
        }
    }

    #[test]
    fn test_private_metrics_aggregator_sum() {
        let epsilon = 1.0;
        let batch_size = 3;
        let config = PrivateMetricsConfig {
            epsilon,
            batch_size,
            buckets: hashmap! {
                "a".to_string() => BucketConfig::Sum { min: 0, max: 10 },
                "b".to_string() => BucketConfig::Sum { min: 10, max: 20 },
            },
        };
        // Use a fixed seed for the random number generators so the errors are predicatable.
        let seed = 0;
        let rng = StdRng::seed_from_u64(seed);
        let aggregator = Arc::new(Mutex::new(
            PrivateMetricsAggregator::new_for_test(&config, rng).unwrap(),
        ));

        let expected = hashmap! {
            "a".to_string() => 13,
            "b".to_string() => 32,
        };
        // Calculate expected noise using a fixed seeded rng.
        let mut rng = StdRng::seed_from_u64(seed);
        let noise: Vec<i64> = (0..2)
            .map(|_| add_laplace_noise(&mut rng, config.buckets.len() as f64 / epsilon, 0, 10.0))
            .collect();

        let mut proxy1 = PrivateMetricsProxy::new(aggregator.clone());
        proxy1.report_metric("a", -100); // Expect +0 for "a", +10 for "b".
                                         // Note: even though no metric value is reported for "b" in this request, the minimum
                                         // configured value means that 10 will be added to bucket "b".
        assert_eq!(proxy1.publish(), None);
        let mut proxy2 = PrivateMetricsProxy::new(aggregator.clone());
        proxy2.report_metric("a", 5); // Overwritten.
        proxy2.report_metric("a", 3); // Expect +3 for "a".
        proxy2.report_metric("b", 12); // Expect +12 for "b".
        assert_eq!(proxy2.publish(), None);
        let mut proxy3 = PrivateMetricsProxy::new(aggregator);
        proxy3.report_metric("a", 100); // Expect +10 for "a".
        proxy3.report_metric("b", 5); // Expect +10 for "b".
        let (count, buckets) = proxy3.publish().unwrap();

        assert_eq!(batch_size, count);
        for (index, (label, value)) in buckets.iter().enumerate() {
            println!(
                "Label: {}, Actual: {}, Expected: {}, Noise: {}",
                label,
                value,
                expected.get(label).unwrap(),
                noise[index]
            );
            assert_eq!(*value, expected.get(label).unwrap() + noise[index]);
        }
    }

    #[test]
    fn test_laplace_noise() {
        // Run many times and make sure the shape of the histogram looks roughly right.
        let iterations = 1_000_000;
        // Check the 0 bucket and 5 buckets either side.
        let offset = 5;
        // Bucket is allowed up to 2% above or below expected size.
        let margin = 0.02_f64;
        let epsilon = 1.0_f64;
        let beta = 1.0 / epsilon;
        let scale = 1.0;
        // Use a fixed seed for the random number generator to avoid potential flakiness.
        let mut rng = StdRng::seed_from_u64(0);
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
            let noise = add_laplace_noise(&mut rng, beta, 0, scale);
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
