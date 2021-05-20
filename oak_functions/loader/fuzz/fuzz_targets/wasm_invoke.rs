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

#![no_main]

pub mod proto {
    include!(concat!(env!("OUT_DIR"), "/loader.fuzz.abi_functions.rs"));
}

use crate::proto::{abi_function::Function, AbiFunctions};
use arbitrary::{Arbitrary, Result, Unstructured};
use libfuzzer_sys::fuzz_target;
use oak_functions_abi::proto::Request;
use oak_functions_loader::{
    grpc::handle_request, logger::Logger, lookup::LookupData, server::WasmHandler,
};
use prost::Message;
use std::sync::Arc;

#[derive(Arbitrary, Debug)]
enum AbiFunction {
    Panic,
    ReadRequest,
    WriteResponse {
        // The response to write.
        response: Bytes,
    },
    StorageGetItem {
        // The key to lookup.
        key: Bytes,
    },
    WriteLogMessage {
        message: Bytes,
    },
}

/// Wrapper for a byte vector, to provide a custom `Arbitrary` implementation.
#[derive(Debug)]
struct Bytes {
    bytes: Vec<u8>,
}

impl Arbitrary<'_> for Bytes {
    fn arbitrary(raw: &mut Unstructured<'_>) -> Result<Self> {
        let bytes = <Vec<u8>>::arbitrary(raw)?;
        Ok(Self { bytes })
    }
}

const MANIFEST_PATH: &str = "../examples/fuzzable/module/Cargo.toml";
lazy_static::lazy_static! {
    static ref WASM_MODULE_BYTES: Vec<u8> =
        test_utils::compile_rust_wasm(MANIFEST_PATH).expect("Couldn't read Wasm module");
}

// Randomly generate a list of `AbiFunctions` and send them to the Wasm module to run them.
fuzz_target!(|methods: Vec<AbiFunction>| {
    let functions = methods
        .iter()
        .map(|method| {
            let function = match method {
                AbiFunction::Panic => Some(Function::Panic(crate::proto::Panic {})),
                AbiFunction::ReadRequest => {
                    Some(Function::ReadRequest(crate::proto::ReadRequest {}))
                }
                AbiFunction::WriteResponse { response } => {
                    Some(Function::WriteResponse(crate::proto::WriteResponse {
                        response: response.bytes.clone(),
                    }))
                }
                AbiFunction::StorageGetItem { key } => {
                    Some(Function::StorageGetItem(crate::proto::StorageGetItem {
                        key: key.bytes.clone(),
                    }))
                }
                AbiFunction::WriteLogMessage { message } => {
                    Some(Function::WriteLogMessage(crate::proto::WriteLogMessage {
                        message: message.bytes.clone(),
                    }))
                }
            };
            crate::proto::AbiFunction { function }
        })
        .collect();
    let abi_functions = AbiFunctions { functions };
    let mut body = vec![];
    abi_functions
        .encode(&mut body)
        .expect("Error encoding abi_function");
    let request = Request { body };

    let wasm_handler = WasmHandler::create(
        &WASM_MODULE_BYTES,
        Arc::new(LookupData::new_empty("", Logger::for_test())),
        Logger::for_test(),
    )
    .expect("Could instantiate WasmHandler");

    let rt = tokio::runtime::Runtime::new().unwrap();
    let result = rt.block_on(handle_request(wasm_handler, tonic::Request::new(request)));
    assert!(result.is_ok());
    // Cannot check the exact response value, since the wasm function may panic at any point.
});
