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
        BoxedExtension, BoxedExtensionFactory, ExtensionFactory, OakApiNativeExtension, ABI_USIZE,
    },
};
use alloc::sync::Arc;
use oak_functions_abi::{proto::OakStatus, ExtensionHandle, ReportMetricRequest};
use oak_functions_metrics::{
    PrivateMetricsAggregator, PrivateMetricsExtension, PrivateMetricsProxy,
};
// TODO(#2630): Use the std version of Mutex in environments where std is available.
use oak_functions_metrics::PrivateMetricsConfig;
use oak_functions_util::sync::Mutex;
use wasmi::ValueType;

/// Host function name for reporting private metrics.
const METRICS_ABI_FUNCTION_NAME: &str = "report_metric";

pub struct PrivateMetricsProxyFactory {
    aggregator: Arc<Mutex<PrivateMetricsAggregator>>,
    logger: Logger,
}

impl PrivateMetricsProxyFactory {
    pub fn new_boxed_extension_factory(
        config: &PrivateMetricsConfig,
        logger: Logger,
    ) -> anyhow::Result<BoxedExtensionFactory> {
        config.validate()?;
        let aggregator = PrivateMetricsAggregator::new(config)?;
        let metrics_factory = Self {
            aggregator: Arc::new(Mutex::new(aggregator)),
            logger,
        };
        Ok(Box::new(metrics_factory))
    }
}

// TODO(#2576): Move extension trait implementation to the metrics crate once the extension-related
// traits are in a separate crate.
impl ExtensionFactory for PrivateMetricsProxyFactory {
    fn create(&self) -> anyhow::Result<BoxedExtension> {
        let metrics_proxy = PrivateMetricsProxy::new(self.aggregator.clone());
        Ok(Box::new(PrivateMetricsExtension::<Logger>::new(
            metrics_proxy,
            self.logger.clone(),
        )))
    }
}

impl OakApiNativeExtension for PrivateMetricsExtension<Logger> {
    fn invoke(&mut self, request: Vec<u8>) -> Result<Vec<u8>, OakStatus> {
        let request: ReportMetricRequest =
            bincode::deserialize(&request).expect("Fail to deserialize report metric request.");

        self.log_debug(&format!("report_metric(): {}", request.label));
        let _ = self
            .report_metric(&request.label, request.value)
            .map_err(|err| {
                self.log_error(&format!("report_metric(): {:?}", err));
                OakStatus::ErrInternal
            })?;

        // No result is expected from computing metric.
        Ok(vec![])
    }

    /// Each Oak Functions application can have at most one instance of PrivateMetricsProxy. So it
    /// is fine to return a constant name in the metadata.
    fn get_metadata(&self) -> (String, wasmi::Signature) {
        let signature = wasmi::Signature::new(
            &[
                ABI_USIZE, // buf_ptr
                ABI_USIZE, // buf_len
            ][..],
            Some(ValueType::I32),
        );

        (METRICS_ABI_FUNCTION_NAME.to_string(), signature)
    }

    fn terminate(&mut self) -> anyhow::Result<()> {
        self.publish_metrics()
    }

    fn get_handle(&self) -> ExtensionHandle {
        ExtensionHandle::MetricsHandle
    }
}
