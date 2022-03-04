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
    include!(concat!(env!("OUT_DIR"), "/loader.fuzz.instructions.rs"));
}

use crate::proto::{instruction::InstructionVariant, Instructions};
use arbitrary::Arbitrary;
use libfuzzer_sys::fuzz_target;
use maplit::{btreemap, hashmap};
use oak_functions_abi::proto::Request;
use oak_functions_loader::{
    logger::Logger,
    lookup::LookupFactory,
    lookup_data::LookupData,
    metrics::PrivateMetricsProxyFactory,
    server::{BoxedExtensionFactory, WasmHandler},
};
use oak_functions_metrics::{BucketConfig, PrivateMetricsConfig};
use prost::Message;
use std::{convert::Into, sync::Arc};

#[derive(Arbitrary, Debug, Clone, PartialEq)]
enum ArbitraryInstruction {
    Panic,
    ReadRequest,
    WriteResponse {
        // The response to write.
        response: Vec<u8>,
    },
    StorageGetItem {
        // The key to lookup.
        key: LookupKey,
    },
    WriteLogMessage {
        message: Vec<u8>,
    },
    ReportEvent {
        label: Vec<u8>,
    },
}

/// Enum to allow simulating both hit and miss lookup scenarios.
#[derive(Arbitrary, Debug, Clone, PartialEq)]
enum LookupKey {
    /// Uses `FIXED_KEY` for lookup. Covers the scenario where the lookup matches a key in
    /// LookupData.
    FixedKey,
    /// Uses a random key for lookup. Covers the scenario where the key does not match anything in
    /// LookupData.
    RandomKey { key: Vec<u8> },
}

impl From<&LookupKey> for Vec<u8> {
    fn from(key: &LookupKey) -> Self {
        match key {
            LookupKey::FixedKey => FIXED_KEY.to_vec(),
            LookupKey::RandomKey { key } => key.clone(),
        }
    }
}

const FIXED_KEY: &[u8] = b"key";

lazy_static::lazy_static! {
    static ref WASM_MODULE_BYTES: Vec<u8> = include_bytes!("./data/fuzzable.wasm").to_vec();
}

// Create the `tokio::runtime::Runtime` only once, instead of creating a new instance in each
// testcase.
lazy_static::lazy_static! {
    static ref RUNTIME: tokio::runtime::Runtime = tokio::runtime::Runtime::new().unwrap();
}

/// To avoid timeouts, allow executing a limited number of instructions. On oss-fuzz, the timeout is
/// set to 25s. On average, the slowest instruction is ReadRequest. A maximum of 10_000 instructions
/// should give a good margin to avoid timeouts.
const MAX_INSTRUCTIONS_COUNT: usize = 10_000;

// Generate a random list of `Instruction`s and send them to the Wasm module to run.
fuzz_target!(|instruction_list: Vec<ArbitraryInstruction>| {
    let mut instructions: Vec<crate::proto::Instruction> = instruction_list
        .iter()
        .map(crate::proto::Instruction::from)
        .collect();

    // To avoid timeouts, keep only the first MAX_INSTRUCTIONS_COUNT instructions.
    if instructions.len() > MAX_INSTRUCTIONS_COUNT {
        instructions.drain(MAX_INSTRUCTIONS_COUNT..);
    }
    let instructions = Instructions { instructions };

    let mut body = vec![];
    instructions
        .encode(&mut body)
        .expect("Error encoding abi_function");
    let request = Request { body };

    let entries = hashmap! {
        FIXED_KEY.to_vec() => br"value".to_vec(),
    };

    let logger = Logger::for_test();
    let lookup_data = Arc::new(LookupData::for_test(entries));
    let lookup_factory = LookupFactory::new_boxed_extension_factory(lookup_data, logger.clone())
        .expect("could not create LookupFactory");
    let metrics_factory = create_metrics_factory();

    let wasm_handler = WasmHandler::create(
        &WASM_MODULE_BYTES,
        vec![lookup_factory, metrics_factory],
        logger,
    )
    .expect("Could not instantiate WasmHandler");

    let result = RUNTIME.block_on(wasm_handler.handle_invoke(request));
    assert!(result.is_ok(), "Error: {:?}", result);
    // Cannot check the exact response value, since the wasm function may panic at any point.
});

/// Convert [`&ArbitraryInstruction`] into [`crate::proto::Instruction`].
impl From<&ArbitraryInstruction> for crate::proto::Instruction {
    fn from(instruction: &ArbitraryInstruction) -> Self {
        let instruction_variant = match instruction {
            ArbitraryInstruction::Panic => Some(InstructionVariant::Panic(crate::proto::Panic {})),
            ArbitraryInstruction::ReadRequest => Some(InstructionVariant::ReadRequest(
                crate::proto::ReadRequest {},
            )),
            ArbitraryInstruction::WriteResponse { response } => Some(
                InstructionVariant::WriteResponse(crate::proto::WriteResponse {
                    response: response.clone(),
                }),
            ),
            ArbitraryInstruction::StorageGetItem { key } => {
                Some(InstructionVariant::StorageGetItem(
                    crate::proto::StorageGetItem { key: key.into() },
                ))
            }
            ArbitraryInstruction::WriteLogMessage { message } => Some(
                InstructionVariant::WriteLogMessage(crate::proto::WriteLogMessage {
                    message: message.clone(),
                }),
            ),
            ArbitraryInstruction::ReportEvent { label } => {
                Some(InstructionVariant::ReportEvent(crate::proto::ReportEvent {
                    label: label.clone(),
                }))
            }
        };
        crate::proto::Instruction {
            instruction_variant,
        }
    }
}

fn create_metrics_factory() -> BoxedExtensionFactory {
    // TODO(#2252): Use `Arbitrary` to generate metrics configuration.
    let metrics_config = PrivateMetricsConfig {
        epsilon: 1.0,
        batch_size: 20,
        buckets: btreemap! {"count".to_string() => BucketConfig::Count },
    };

    PrivateMetricsProxyFactory::new_boxed_extension_factory(&metrics_config, Logger::for_test())
        .expect("could not create PrivateMetricsProxyFactory")
}
