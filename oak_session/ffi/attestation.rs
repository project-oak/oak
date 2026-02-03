//
// Copyright 2025 The Project Oak Authors
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

use oak_ffi_bytes::BytesView;
use oak_ffi_error::Error;
use oak_proto_rust::oak::attestation::v1::{Endorsements, Evidence};
use oak_sdk_common::{StaticAttester, StaticEndorser};
use oak_session_ffi_config::{FfiAttester, FfiEndorser};
use prost::Message;

#[repr(C)]
pub struct ErrorOrFfiAttester {
    pub result: FfiAttester,
    pub error: *const Error,
}

impl ErrorOrFfiAttester {
    pub fn ok(result: FfiAttester) -> Self {
        Self { result, error: std::ptr::null() }
    }

    pub fn err(message: impl std::fmt::Display) -> Self {
        Self { result: FfiAttester::null(), error: Error::new_raw(message) }
    }
}

/// Create a new simple attester with the provided evidence.
///
/// # Safety
///
/// * evidence_proto_bytes is a valid, non-null, aligned BytesView instances.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn new_simple_attester(
    evidence_proto_bytes: BytesView,
) -> ErrorOrFfiAttester {
    match Evidence::decode(unsafe { evidence_proto_bytes.as_slice() }) {
        Ok(evidence) => {
            ErrorOrFfiAttester::ok(FfiAttester::new(Box::new(StaticAttester::new(evidence))))
        }
        Err(e) => ErrorOrFfiAttester::err(format!("failed to decode evidence proto: {e:?}")),
    }
}

#[repr(C)]
pub struct ErrorOrFfiEndorser {
    pub result: FfiEndorser,
    pub error: *const Error,
}

impl ErrorOrFfiEndorser {
    pub fn ok(result: FfiEndorser) -> Self {
        Self { result, error: std::ptr::null() }
    }

    pub fn err(message: impl std::fmt::Display) -> Self {
        Self { result: FfiEndorser::null(), error: Error::new_raw(message) }
    }
}
/// Create a new simple endorser with the provided endorsements.
///
/// # Safety
///
/// * eneodrsements_proto_bytes is a valid, non-null, aligned BytesView
///   instances.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn new_simple_endorser(
    endorsements_proto_bytes: BytesView,
) -> ErrorOrFfiEndorser {
    match Endorsements::decode(unsafe { endorsements_proto_bytes.as_slice() }) {
        Ok(endorsements) => {
            ErrorOrFfiEndorser::ok(FfiEndorser::new(Box::new(StaticEndorser::new(endorsements))))
        }
        Err(e) => ErrorOrFfiEndorser::err(format!("failed to decode evidence proto: {e:?}")),
    }
}
