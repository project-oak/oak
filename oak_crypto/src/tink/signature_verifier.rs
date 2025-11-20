//
// Copyright 2025 Oak Authors
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
//     https://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

use alloc::{string::String, vec::Vec};

use cxx_string::CxxString;
use oak_crypto::verifier::Verifier;
use oak_ffi_bytes::BytesView;

#[repr(C)]
pub struct StatusWrapper {
    pub status_code: i32,
    pub status_message: CxxString,
}

// See the implementations in cc/crypto/tink/signature/verification-ffi.h
#[link(name = "verification-ffi")]
extern "C" {
    fn VerifySignatureWithTink(
        message: BytesView,
        signature: BytesView,
        ca_public_keyset: BytesView,
    ) -> StatusWrapper;
}

#[derive(Clone, Debug)]
pub struct SignatureVerifier {
    tink_public_keyset: Vec<u8>,
}

impl SignatureVerifier {
    pub fn new(tink_public_keyset: &[u8]) -> Self {
        Self { tink_public_keyset: tink_public_keyset.to_vec() }
    }
}

impl Verifier for SignatureVerifier {
    fn verify(&self, message: &[u8], signature: &[u8]) -> anyhow::Result<()> {
        let status_wrapper: StatusWrapper = unsafe {
            VerifySignatureWithTink(
                BytesView::new_from_slice(message),
                BytesView::new_from_slice(signature),
                BytesView::new_from_slice(self.tink_public_keyset.as_slice()),
            )
        };
        // See https://github.com/abseil/abseil-cpp/blob/master/absl/status/status.h#L99
        match status_wrapper.status_code {
            // Status Code 0 is an OK status.
            0 => Ok(()),
            // All other statuses are not Ok.
            _ => {
                let error_message_bytes = status_wrapper.status_message.as_slice();
                let error_message = String::from_utf8(error_message_bytes.to_vec())
                    .map_err(|_| anyhow::anyhow!("failed to parse the error"))?;
                anyhow::bail!(error_message)
            }
        }
    }
}
