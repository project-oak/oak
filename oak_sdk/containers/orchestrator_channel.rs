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

use anyhow::{Context, Result};
use tokio::net::UnixStream;
use tonic::transport::{Channel, Endpoint, Uri};
use tower::service_fn;
// Unix Domain Sockets do not use URIs, hence this URI will never be used.
// It is defined purely since in order to create a channel, since a URI has to
// be supplied to create an `Endpoint`. Even though in this case the endpoint
// is technically a file, tonic expects us to provide our own connector, and
// this ignored endpoint. :(
static IGNORED_ENDPOINT_URI: &str = "file://[::]:0";

// Path used to facilitate inter-process communication between the orchestrator
// and the trusted application.
const IPC_SOCKET: &str = "/oak_utils/orchestrator_ipc";

// Connect to the orchestrator instance in a default Oak Containers stack.
pub async fn default_orchestrator_channel() -> Result<Channel> {
    Endpoint::try_from(IGNORED_ENDPOINT_URI)
        .context("couldn't form endpoint")?
        .connect_with_connector(service_fn(move |_: Uri| UnixStream::connect(IPC_SOCKET)))
        .await
        .context("couldn't connect to UDS socket")
}
