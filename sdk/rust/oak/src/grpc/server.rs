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

//! Functionality to help Oak Nodes create gRPC pseudo-Nodes.

use crate::{OakStatus, ReadHandle};

/// Default name for predefined Node configuration that corresponds to a gRPC pseudo-Node.
pub const DEFAULT_CONFIG_NAME: &str = "grpc_server";

/// Initialize a gRPC pseudo-Node with the default configuration.
pub fn init_default() {
    init(DEFAULT_CONFIG_NAME).expect("Coundn't create a gRPC pseudo-Node");
}

/// Initializes a gRPC server pseudo-Node and passes it a handle to write invocations to.
///
/// Returns a [`ReadHandle`] to read invocations from.
///
/// [`ReadHandle`]: crate::ReadHandle
pub fn init(config: &str) -> std::result::Result<ReadHandle, OakStatus> {
    // Create a channel and pass the read half to a new gRPC pseudo-Node.
    let (write_handle, read_handle) = crate::channel_create().expect("Couldn't create a channel");
    crate::node_create(config, "oak_main", read_handle)?;
    crate::channel_close(read_handle.handle).expect("Couldn't close a channel");

    // Create a separate channel for receiving invocations and pass it to a gRPC pseudo-Node.
    let (invocation_write_handle, invocation_read_handle) =
        crate::channel_create().expect("Couldn't create a channel");
    crate::channel_write(write_handle, &[], &[invocation_write_handle.handle])
        .expect("Couldn't write to a channel");
    crate::channel_close(write_handle.handle).expect("Couldn't close a channel");
    crate::channel_close(invocation_write_handle.handle).expect("Couldn't close a channel");

    Ok(invocation_read_handle)
}
