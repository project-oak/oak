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
    include!(concat!(env!("OUT_DIR"), "/loader.fuzz.abi_functions.rs"));
}
use crate::proto::{
    abi_function::Function, AbiFunctions, StorageGetItem, WriteLogMessage, WriteResponse,
};
use prost::Message;

#[cfg(test)]
mod tests;

#[cfg_attr(not(test), no_mangle)]
pub extern "C" fn main() {
    let request = oak_functions::read_request().expect("Couldn't read request body.");
    let request = AbiFunctions::decode(&*request).expect("Couldn't decode request.");

    // Run all the functions given in the request
    for function in request.functions {
        match function.function {
            Some(Function::Panic(_)) => panic!("panic"),
            Some(Function::ReadRequest(_)) => {
                let _req = oak_functions::read_request().expect("Couldn't read request body.");
            }
            Some(Function::WriteResponse(WriteResponse { response })) => {
                oak_functions::write_response(&response).expect("Couldn't write response body.")
            }
            Some(Function::StorageGetItem(StorageGetItem { key })) => {
                let _value = oak_functions::storage_get_item(&key)
                    .expect("Couldn't find key in the storage")
                    .unwrap_or_default();
            }
            Some(Function::WriteLogMessage(WriteLogMessage { message })) => {
                oak_functions::write_log_message(
                    std::str::from_utf8(&message).expect("Couldn't convert bytes to string"),
                )
                .expect("Couldn't write log message.")
            }
            _ => (),
        }
    }

    oak_functions::write_response(br"Done fuzzing!").expect("Couldn't write response body.");
}
