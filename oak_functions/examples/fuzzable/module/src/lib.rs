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

//! Oak Functions fuzzable example.

pub mod proto {
    include!(concat!(env!("OUT_DIR"), "/loader.fuzz.instructions.rs"));
}
use crate::proto::{
    instruction::InstructionVariant, Instructions, Panic, ReadRequest, StorageGetItem,
    WriteLogMessage, WriteResponse,
};
use prost::Message;

#[cfg(test)]
mod tests;

#[cfg_attr(not(test), no_mangle)]
pub extern "C" fn main() {
    let request = oak_functions::read_request().expect("couldn't read request body");
    let request = Instructions::decode(&*request).expect("couldn't decode request");

    // Run all the instructions given in the request
    for instruction in request.instructions {
        match instruction.instruction_variant {
            Some(InstructionVariant::Panic(Panic {})) => panic!("panic"),
            Some(InstructionVariant::ReadRequest(ReadRequest {})) => {
                let _req = oak_functions::read_request().expect("couldn't read request body");
            }
            Some(InstructionVariant::WriteResponse(WriteResponse { response })) => {
                oak_functions::write_response(&response).expect("couldn't write response body")
            }
            Some(InstructionVariant::StorageGetItem(StorageGetItem { key })) => {
                let _value = oak_functions::storage_get_item(&key)
                    .expect("couldn't find key in the storage")
                    .unwrap_or_default();
            }
            Some(InstructionVariant::WriteLogMessage(WriteLogMessage { message })) => {
                oak_functions::write_log_message(
                    std::str::from_utf8(&message).expect("couldn't convert bytes to string"),
                )
                .expect("couldn't write log message")
            }
            None => (),
        }
    }

    oak_functions::write_response(br"Done fuzzing!").expect("couldn't write response body");
}
