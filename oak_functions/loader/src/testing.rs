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
        AbiPointer, BoxedExtension, BoxedExtensionFactory, ExtensionFactory, OakApiNativeExtension,
        ABI_USIZE,
    },
};

use log::Level;
use oak_functions_abi::{proto::OakStatus, ExtensionHandle, TestingRequest, TestingResponse};
use wasmi::ValueType;

/// Host function name for testing.
const TESTING_ABI_FUNCTION_NAME: &str = "testing";

impl OakApiNativeExtension for TestingExtension<Logger> {
    fn invoke(
        &mut self,
        wasm_state: &mut crate::server::WasmState,
        args: wasmi::RuntimeArgs,
        request: Vec<u8>,
    ) -> Result<Result<(), oak_functions_abi::proto::OakStatus>, wasmi::Trap> {
        // TODO(#2699, #2664): Do not write response to Wasm State here.
        let response_ptr_ptr: AbiPointer = args.nth_checked(3)?;
        let response_len_ptr: AbiPointer = args.nth_checked(4)?;

        let result = testing(request).and_then(|result| {
            wasm_state.write_extension_result(result, response_ptr_ptr, response_len_ptr)
        });

        Ok(result)
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

    fn get_handle(&mut self) -> ExtensionHandle {
        ExtensionHandle::TestingHandle
    }
}

fn testing(message: Vec<u8>) -> Result<Vec<u8>, OakStatus> {
    let deserialized_testing_message =
        bincode::deserialize(&message).expect("Fail to deserialize testing message.");

    let result = match deserialized_testing_message {
        TestingRequest::Echo(echo_message) => {
            let echo_response = TestingResponse::Echo(echo_message);
            bincode::serialize(&echo_response).expect("Fail to serialize testing message.")
        }
    };

    Ok(result)
}

pub struct TestingFactory {
    logger: Logger,
}

impl TestingFactory {
    pub fn new_boxed_extension_factory(logger: Logger) -> anyhow::Result<BoxedExtensionFactory> {
        Ok(Box::new(Self { logger }))
    }
}

impl ExtensionFactory for TestingFactory {
    fn create(&self) -> anyhow::Result<BoxedExtension> {
        let extension = TestingExtension::new(self.logger.clone());
        Ok(Box::new(extension))
    }
}

#[allow(dead_code)]
pub struct TestingExtension<L: oak_logger::OakLogger> {
    logger: L,
}

impl<L> TestingExtension<L>
where
    L: oak_logger::OakLogger,
{
    pub fn new(logger: L) -> Self {
        Self { logger }
    }

    pub fn log_error(&self, message: &str) {
        self.logger.log_sensitive(Level::Error, message)
    }
}
