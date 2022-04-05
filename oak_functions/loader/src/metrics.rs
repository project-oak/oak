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
        BoxedExtension, BoxedExtensionFactory, ExtensionFactory, OakApiNativeExtension, WasmState,
        ABI_USIZE,
    },
};
use alloc::sync::Arc;
use oak_functions_abi::{proto::OakStatus, ExtensionHandle};
use oak_functions_metrics::{
    PrivateMetricsAggregator, PrivateMetricsExtension, PrivateMetricsProxy,
};
// TODO(#2630): Use the std version of Mutex in environments where std is available.
use oak_functions_util::sync::Mutex;
use serde::Deserialize;
use wasmi::ValueType;

// Export for use in integration test.
pub use oak_functions_metrics::{BucketConfig, PrivateMetricsConfig};

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
    fn invoke(
        &mut self,
        wasm_state: &mut WasmState,
        args: wasmi::RuntimeArgs,
    ) -> Result<Result<(), OakStatus>, wasmi::Trap> {
        let buf_ptr = args.nth_checked(0)?;
        let buf_len = args.nth_checked(1)?;

        let args = wasm_state
            .read_extension_args(buf_ptr, buf_len)
            .map_err(|err| {
                self.log_error(&format!(
                    "report_metric(): Unable to read label from guest memory: {:?}",
                    err
                ));
                OakStatus::ErrInvalidArgs
            });

        let result = args.and_then(|metric_message| report_metric(self, metric_message));

        Ok(result)
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

    fn get_handle(&mut self) -> ExtensionHandle {
        ExtensionHandle::MetricsHandle
    }
}

/// Provides logic for the host ABI function [`report_metric`](https://github.com/project-oak/oak/blob/main/docs/oak_functions_abi.md#report_metric).
fn report_metric(
    extension: &mut PrivateMetricsExtension<Logger>,
    metric_message: Vec<u8>,
) -> Result<(), OakStatus> {
    let metric_message: MetricMessage =
        bincode::deserialize(&metric_message).expect("Fail to deserialize metric message.");

    let label = std::str::from_utf8(metric_message.raw_label.as_slice()).map_err(|err| {
        extension.log_warning(&format!(
            "report_metric(): Not a valid UTF-8 encoded string: {:?}\nContent: {:?}",
            err, metric_message.raw_label
        ));
        OakStatus::ErrInvalidArgs
    })?;
    extension.log_debug(&format!("report_metric(): {}", label));
    extension
        .report_metric(label, metric_message.value)
        .map_err(|err| {
            extension.log_error(&format!("report_metric(): {:?}", err));
            OakStatus::ErrInternal
        })
}

#[derive(Deserialize)]
pub struct MetricMessage {
    raw_label: Vec<u8>,
    value: i64,
}
