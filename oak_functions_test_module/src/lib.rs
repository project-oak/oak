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

//! Oak Functions test module.

#![feature(never_type)]
#![feature(unwrap_infallible)]

use core::sync::atomic::{AtomicBool, Ordering};
use std::sync::Arc;

use micro_rpc::Transport;
use oak_micro_rpc::oak::functions::testing::{TestModule, TestModuleServer};
use oak_proto_rust::oak::functions::testing::{
    EchoAndPanicRequest, EchoAndPanicResponse, LookupRequest, LookupResponse, lookup_request::Mode,
};

#[cfg_attr(not(test), unsafe(no_mangle))]
pub extern "C" fn main() {
    let should_panic_afterwards = Arc::new(AtomicBool::new(false));

    let service = Service { should_panic_afterwards: should_panic_afterwards.clone() };
    let mut trasport = TestModuleServer::new(service);
    let request_bytes = oak_functions_sdk::read_request().expect("couldn't read request body");
    let response_bytes = trasport.invoke(&request_bytes).into_ok();
    oak_functions_sdk::write_response(&response_bytes).expect("couldn't write response body");

    if should_panic_afterwards.load(Ordering::Relaxed) {
        panic!("panic requested");
    }
}

struct Service {
    should_panic_afterwards: Arc<AtomicBool>,
}

impl TestModule for Service {
    fn lookup(&mut self, request: LookupRequest) -> Result<LookupResponse, ::micro_rpc::Status> {
        // Implicitly convert not found entries to empty values.
        let values: Vec<Vec<u8>> = match request.mode() {
            // Look up individual keys one by one and collect the results.
            Mode::Individual => request
                .keys
                .into_iter()
                .map(|key| {
                    oak_functions_sdk::storage_get_item(&key)
                        .expect("couldn't look up entry")
                        .unwrap_or_default()
                })
                .collect(),
            // Look up all keys in a batch.
            Mode::Batch => oak_functions_sdk::storage_get_items(request.keys)
                .expect("couldn't look up entries")
                .into_iter()
                .map(|v| v.unwrap_or_default())
                .collect(),
        };

        Ok(LookupResponse { values })
    }
    fn echo_and_panic(
        &mut self,
        request: EchoAndPanicRequest,
    ) -> Result<EchoAndPanicResponse, ::micro_rpc::Status> {
        self.should_panic_afterwards.store(true, Ordering::Relaxed);
        Ok(EchoAndPanicResponse { data: request.data })
    }
}
