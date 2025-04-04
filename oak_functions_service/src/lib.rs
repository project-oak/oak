//
// Copyright 2022 The Project Oak Authors
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

#![no_std]
#![feature(never_type)]
#![feature(new_zeroed_alloc)]
#![feature(unwrap_infallible)]
// Required for enabling benchmark tests.
#![feature(test)]

use alloc::sync::Arc;

use lookup::LookupDataManager;
use oak_functions_abi::{Request, Response};

extern crate alloc;
extern crate rand_core;

#[cfg(test)]
extern crate std;

pub mod instance;
pub mod logger;
pub mod lookup;
pub mod lookup_htbl;
pub mod wasm;

pub trait Observer {
    fn wasm_initialization(&self, duration: core::time::Duration);
    fn wasm_invocation(&self, duration: core::time::Duration);
}

pub trait Handler {
    type HandlerType: Handler;
    type HandlerConfig: Default + Send + Sync + Clone;

    fn new_handler<const S: usize>(
        config: Self::HandlerConfig,
        wasm_module_bytes: &[u8],
        lookup_data_manager: Arc<LookupDataManager<S>>,
        observer: Option<Arc<dyn Observer + Send + Sync>>,
    ) -> anyhow::Result<Self::HandlerType>;

    /// Handles a call to invoke by getting the raw request bytes from the body
    /// of the request to invoke and returns a reponse to invoke setting the
    /// raw bytes in the body of the response.
    fn handle_invoke(&self, invoke_request: Request) -> Result<Response, micro_rpc::Status>;
}
