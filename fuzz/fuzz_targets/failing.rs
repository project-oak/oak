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

// TODO(#3503): This target is temporary. Remove the file once we have enough data.
//! This is an intentionally failing fuzz target for testing.

#![no_main]
#![feature(async_closure)]

use libfuzzer_sys::fuzz_target;
use oak_remote_attestation::crypto::get_sha256;

// A fake fuzz target that computes the SHA256 digest of the input, and checks that it does not
// start with `000` zeros. This fuzz target is intentionally designed to fail.
fuzz_target!(|data: &[u8]| {
    let digest_bytes = get_sha256(data);
    let digest_hex = hex::encode(digest_bytes);
    assert!(!digest_hex.starts_with("000"));
});
