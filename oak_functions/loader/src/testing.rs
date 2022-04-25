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

use crate::{logger::Logger, server::ABI_USIZE, OakFunctionsBoxedExtensionFactory};
use oak_functions_extension::{ExtensionFactory, OakApiNativeExtension};

use log::Level;
use oak_functions_abi::{proto::OakStatus, ExtensionHandle, TestingRequest, TestingResponse};
use oak_logger::OakLogger;
use wasmi::ValueType;

/// Host function name for testing.
const TESTING_ABI_FUNCTION_NAME: &str = "testing";

impl OakApiNativeExtension for TestingExtension<Logger> {
    fn invoke(&mut self, request: Vec<u8>) -> Result<Vec<u8>, OakStatus> {
        let request = bincode::deserialize(&request).expect("Fail to deserialize testing request.");

        let response = match request {
            TestingRequest::Echo(echo_message) => {
                let echo_response = TestingResponse::Echo(echo_message);
                bincode::serialize(&echo_response).expect("Fail to serialize testing request.")
            }
            TestingRequest::Blackhole(message) => {
                self.logger.log_sensitive(Level::Debug, &message);
                // We don't expect the BlackholeRequest to give back a result.
                vec![]
            }
        };
        Ok(response)
    }

    fn get_metadata(&self) -> (String, wasmi::Signature) {
        let signature = wasmi::Signature::new(
            &[
                ABI_USIZE, // request_ptr
                ABI_USIZE, // request_len
                ABI_USIZE, // response_ptr_ptr
                ABI_USIZE, // response_len_ptr
            ][..],
            Some(ValueType::I32),
        );

        (TESTING_ABI_FUNCTION_NAME.to_string(), signature)
    }

    fn terminate(&mut self) -> anyhow::Result<()> {
        Ok(())
    }

    fn get_handle(&self) -> ExtensionHandle {
        ExtensionHandle::TestingHandle
    }
}
pub struct TestingFactory {
    logger: Logger,
}

impl TestingFactory {
    pub fn new_boxed_extension_factory(
        logger: Logger,
    ) -> anyhow::Result<OakFunctionsBoxedExtensionFactory> {
        Ok(Box::new(Self { logger }))
    }
}

impl ExtensionFactory<Logger> for TestingFactory {
    fn create(&self) -> anyhow::Result<Box<dyn OakApiNativeExtension>> {
        let extension = TestingExtension::new(self.logger.clone());
        Ok(Box::new(extension))
    }
}
struct TestingExtension<Logger> {
    logger: Logger,
}

impl TestingExtension<Logger> {
    pub fn new(logger: Logger) -> Self {
        Self { logger }
    }
}
