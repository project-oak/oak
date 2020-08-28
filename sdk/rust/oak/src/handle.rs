//
// Copyright 2020 The Project Oak Authors
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

//! Utilities for visiting, extract and injecting handles.
//!
//! Applications will usually not interact with the types in this module directly, as the
//! `HandleVisit` trait is automatically derived for all protobuf types compiled with `oak_utils`,
//! and extracting and injecting handles is taken care of by
//! [`oak::io::Receiver`](../io/struct.Receiver.html) and
//! [`oak::io::Sender`](../io/struct.Sender.html).

use crate::Handle;
use byteorder::{ReadBytesExt, WriteBytesExt};
pub use oak_io::handle::{extract_handles, inject_handles, HandleVisit, Receiver, Sender};

/// Check this handle is valid.
pub fn is_valid(handle: Handle) -> bool {
    handle != oak_abi::INVALID_HANDLE
}

/// Returns an intentionally invalid handle.
pub fn invalid() -> Handle {
    oak_abi::INVALID_HANDLE
}

/// Pack a slice of `Handles` into the Wasm host ABI format.
pub(crate) fn pack(handles: &[Handle]) -> Vec<u8> {
    let mut packed = Vec::with_capacity(handles.len() * 8);
    for handle in handles {
        packed
            .write_u64::<byteorder::LittleEndian>(handle.to_owned())
            .unwrap();
    }
    packed
}

/// Unpack a slice of Handles from the Wasm host ABI format.
pub(crate) fn unpack(bytes: &[u8], handle_count: u32, handles: &mut Vec<Handle>) {
    handles.clear();
    let mut reader = std::io::Cursor::new(bytes);
    for _ in 0..handle_count {
        handles.push(reader.read_u64::<byteorder::LittleEndian>().unwrap());
    }
}
