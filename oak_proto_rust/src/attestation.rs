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

// Random IDs for commonly used attestation types.
use core::ffi::CStr;

/// Attestation type where the session binding key is signed by a key known to
/// the client.
pub const CERTIFICATE_BASED_ATTESTATION_ID_CSTR: &CStr = c"95553023-358f-4f8c-b75c-e6e185cc05ca";

// Safety: the UUID is valid UTF-8, and we can't use `Result` in a const
// context.
#[allow(dead_code)]
pub const CERTIFICATE_BASED_ATTESTATION_ID: &str =
    unsafe { str::from_utf8_unchecked(CERTIFICATE_BASED_ATTESTATION_ID_CSTR.to_bytes()) };

/// Attestation type where the session binding key is included in a JWT which
/// itself is signed by a certificate chain whose root is GCP Confidential
/// Space's root certificate (see
/// https://cloud.google.com/confidential-computing/confidential-space/docs/reference/token-claims).
pub const CONFIDENTIAL_SPACE_ATTESTATION_ID_CSTR: &CStr = c"d4d3e98d-334f-4f6d-9e84-d0291f9dbcdd";

// Safety: the UUID is valid UTF-8, and we can't use `Result` in a const
// context.
#[allow(dead_code)]
pub const CONFIDENTIAL_SPACE_ATTESTATION_ID: &str =
    unsafe { str::from_utf8_unchecked(CONFIDENTIAL_SPACE_ATTESTATION_ID_CSTR.to_bytes()) };
