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

//! Functionality covering configuration of a Runtime instance.

use crate::RuntimeProxy;
use oak_abi::{proto::oak::application::ApplicationConfiguration, OakStatus};

/// Configures a [`RuntimeProxy`] from the given protobuf [`ApplicationConfiguration`] and begins
/// execution.
///
/// Returns a [`RuntimeProxy`] for an initial implicit Node, and a writeable [`oak_abi::Handle`] to
/// send messages into the Runtime. Creating a new channel and passing the write [`oak_abi::Handle`]
/// into the runtime will enable messages to be read back out from the [`RuntimeProxy`].
pub fn configure_and_run(
    application_configuration: ApplicationConfiguration,
    runtime_configuration: crate::RuntimeConfiguration,
    grpc_configuration: crate::GrpcConfiguration,
) -> Result<(RuntimeProxy, oak_abi::Handle), OakStatus> {
    let proxy = RuntimeProxy::create_runtime(application_configuration, grpc_configuration);
    let handle = proxy.start_runtime(runtime_configuration)?;
    Ok((proxy, handle))
}
