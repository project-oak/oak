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
use maplit::hashmap;
use oak_functions_abi::proto::Request;
use oak_functions_loader::{logger::Logger, lookup::LookupDataForTest, server::WasmHandler};
use prost::Message;
use std::sync::Arc;

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
}

#[derive(Arbitrary, Debug, Clone, PartialEq)]
enum LookupKey {
    Key,
    RandomKey { key: Vec<u8> },
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

// Generate a random list of `Instruction`s and send them to the Wasm module to run.
fuzz_target!(|instruction_list: Vec<ArbitraryInstruction>| {
    let (folded, _) =
        instruction_list
            .iter()
            .fold((vec![], None), |(mut folded, last_seen), instruction| {
                // If there are a number of consecutive ReadRequest instructions merge them into
                // one, since it is idempotent. This is required to avoid timeouts.
                match last_seen {
                    Some(ArbitraryInstruction::ReadRequest) => {
                        if *instruction != ArbitraryInstruction::ReadRequest {
                            folded.push(instruction.clone())
                        }
                    }
                    _ => folded.push(instruction.clone()),
                }
                (folded, Some(instruction.clone()))
            });

    let instructions = folded.iter().map(crate::proto::Instruction::from).collect();
    let instructions = Instructions { instructions };
    let mut body = vec![];
    instructions
        .encode(&mut body)
        .expect("Error encoding abi_function");
    let request = Request { body };

    let entries = hashmap! {
        FIXED_KEY.to_vec() => br"value".to_vec(),
    };

    let wasm_handler = WasmHandler::create(
        &WASM_MODULE_BYTES,
        Arc::new(LookupDataForTest::new(entries).lookup_data),
        Logger::for_test(),
    )
    .expect("Could instantiate WasmHandler");

    let result = RUNTIME.block_on(wasm_handler.handle_invoke(request));
    assert!(result.is_ok());
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
            ArbitraryInstruction::StorageGetItem { key } => match key {
                LookupKey::Key => Some(InstructionVariant::StorageGetItem(
                    crate::proto::StorageGetItem {
                        key: FIXED_KEY.to_vec(),
                    },
                )),
                LookupKey::RandomKey { key } => Some(InstructionVariant::StorageGetItem(
                    crate::proto::StorageGetItem { key: key.clone() },
                )),
            },
            ArbitraryInstruction::WriteLogMessage { message } => Some(
                InstructionVariant::WriteLogMessage(crate::proto::WriteLogMessage {
                    message: message.clone(),
                }),
            ),
        };
        crate::proto::Instruction {
            instruction_variant,
        }
    }
}
