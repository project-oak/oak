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
use oak_functions_loader::{logger::Logger, lookup::LookupData, server::WasmHandler};
use prost::Message;
use std::{path::Path, sync::Arc};

#[derive(Arbitrary, Debug)]
enum ArbitraryInstruction {
    Panic,
    ReadRequest,
    WriteResponse {
        // The response to write.
        response: Vec<u8>,
    },
    StorageGetItem {
        // The key to lookup.
        key: Vec<u8>,
    },
    WriteLogMessage {
        message: Vec<u8>,
    },
}

/// Path to the manifest file of the `fuzzable` example. Required for running locally, or the CI.
const MANIFEST_PATH: &str = "../examples/fuzzable/module/Cargo.toml";

/// Path to the Wasm module when running the OSS-Fuzz project.
/// The OSS-Fuzz project uses separate directories for building and running fuzz targets.
/// Therefore, to build the Wasm module at runtime, we'll have to copy the entire `oak` project
/// to the running path (i.e., `/out`). To avoid the need for this, in the OSS-Fuzz project, we
/// build the Wasm module for `fuzzable` in the build phase, when the fuzz targets are built as
/// well, and store the `.wasm` file in `/out/bin`.
///
/// Keep this path in sync with `https://github.com/google/oss-fuzz/blob/master/projects/oak/build.sh`.
const OSS_FUZZ_WASM_MODULE_PATH: &str = "/out/bin/fuzzable.wasm";

lazy_static::lazy_static! {
    static ref WASM_MODULE_BYTES: Vec<u8> = get_wasm_module_bytes();
}

// Create the `tokio::runtime::Runtime` only once, instead of creating a new instance in each
// testcase.
lazy_static::lazy_static! {
    static ref RUNTIME: tokio::runtime::Runtime = tokio::runtime::Runtime::new().unwrap();
}

// Generate a random list of `Instruction`s and send them to the Wasm module to run.
fuzz_target!(|instruction_list: Vec<ArbitraryInstruction>| {
    let instructions = instruction_list
        .iter()
        .map(crate::proto::Instruction::from)
        .collect();
    let instructions = Instructions { instructions };
    let mut body = vec![];
    instructions
        .encode(&mut body)
        .expect("Error encoding abi_function");

    let wasm_handler = WasmHandler::create(
        &WASM_MODULE_BYTES,
        Arc::new(LookupData::new_empty("", Logger::for_test())),
        Logger::for_test(),
    )
    .expect("Could instantiate WasmHandler");

    let result = RUNTIME.block_on(wasm_handler.handle_invoke(body));
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
            ArbitraryInstruction::StorageGetItem { key } => {
                Some(InstructionVariant::StorageGetItem(
                    crate::proto::StorageGetItem { key: key.clone() },
                ))
            }
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

fn get_wasm_module_bytes() -> Vec<u8> {
    let module_path = Path::new(OSS_FUZZ_WASM_MODULE_PATH);
    if module_path.exists() {
        std::fs::read(module_path).expect("Couldn't read wasm module")
    } else {
        test_utils::compile_rust_wasm(&MANIFEST_PATH).expect("Couldn't read Wasm module")
    }
}
