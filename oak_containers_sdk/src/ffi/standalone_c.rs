//
// Copyright 2024 The Project Oak Authors
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

//! A few bindings to SDK-provided functionality for C++ callers.
//!
//! This is not a comprehensive set of SDK functionality; it's just to bridge
//! any gaps we have between our current C++ and Rust featureset.
use std::os::raw::c_void;

use oak_containers_sdk::standalone::StandaloneOrchestrator;
use prost::Message;

/// C bindings for generating standalone endorsed evidence.
/// Currently only supports the default configuration.
///
/// The provided callback will be called with the serialized EndorsedEvidence
/// proto generated by rust. Within the scope of the callback, you should
/// process the data however you'd like; but do not hold onto it, it will become
/// invalid when the callback scope is exited.
///
/// The callback also receive a caller-provided context object of the callers
/// choosing; this can contain the resources needed to properly handle the data.
///
/// # Safety
///
/// The semantics of `callback_context` are defined by the provided callback.
/// Ensure that the callback imlementation does not hold onto the memory pointed
/// to by `data` longer than the scope of the callback invocation.
#[no_mangle]
pub unsafe extern "C" fn standalone_endorsed_evidence(
    callback_context: *mut c_void,
    callback: unsafe extern "C" fn(
        callback_context: *mut c_void,
        data: *const u8,
        data_length: usize,
    ),
) -> bool {
    let orchestrator = StandaloneOrchestrator::default();
    let endorsed_evidence = orchestrator.get_endorsed_evidence();
    let serialized_endorsed_evidence = Message::encode_to_vec(&endorsed_evidence);

    unsafe {
        callback(
            callback_context,
            serialized_endorsed_evidence.as_ptr(),
            serialized_endorsed_evidence.len(),
        );
    }

    true
}