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
        AbiPointer, AbiPointerOffset, BoxedExtension, BoxedExtensionFactory, ExtensionFactory,
        OakApiNativeExtension, WasmState, ABI_USIZE,
    },
};
use oak_functions_abi::proto::OakStatus;
use oak_functions_metrics::{
    PrivateMetricsAggregator, PrivateMetricsConfig, PrivateMetricsExtension, PrivateMetricsProxy,
};
use std::sync::{Arc, Mutex};
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
        Ok(BoxedExtension::Native(Box::new(PrivateMetricsExtension::<
            Logger,
        >::new(
            metrics_proxy,
            self.logger.clone(),
        ))))
    }
}

impl OakApiNativeExtension for PrivateMetricsExtension<Logger> {
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

/// Corresponds to the host ABI function [`report_metric`](https://github.com/project-oak/oak/blob/main/docs/oak_functions_abi.md#report_metric).
fn report_metric(
    wasm_state: &mut WasmState,
    extension: &mut PrivateMetricsExtension<Logger>,
    buf_ptr: AbiPointer,
    buf_len: AbiPointerOffset,
    value: i64,
) -> Result<(), OakStatus> {
    let raw_label = wasm_state
        .get_memory()
        .get(buf_ptr, buf_len as usize)
        .map_err(|err| {
            extension.log_error(&format!(
                "report_metric(): Unable to read label from guest memory: {:?}",
                err
            ));
            OakStatus::ErrInvalidArgs
        })?;
    let label = std::str::from_utf8(raw_label.as_slice()).map_err(|err| {
        extension.log_warning(&format!(
            "report_metric(): Not a valid UTF-8 encoded string: {:?}\nContent: {:?}",
            err, raw_label
        ));
        OakStatus::ErrInvalidArgs
    })?;
    extension.log_debug(&format!("report_metric(): {}", label));
    extension.report_metric(label, value).map_err(|err| {
        extension.log_error(&format!("report_metric(): {:?}", err));
        OakStatus::ErrInternal
    })
}
