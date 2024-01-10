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

mod proto {
    pub mod oak {
        pub mod containers {
            tonic::include_proto!("oak.containers");
            pub mod v1 {
                #![allow(clippy::return_self_not_must_use)]
                tonic::include_proto!("oak.containers.v1");
            }
        }
        pub use oak_crypto::proto::oak::crypto;
        pub use oak_remote_attestation::proto::oak::{attestation, session};
    }
}

pub mod crypto;
pub mod orchestrator_client;

// Unix Domain Sockets do not use URIs, hence this URI will never be used.
// It is defined purely since in order to create a channel, since a URI has to
// be supplied to create an `Endpoint`. Even though in this case the endpoint
// is technically a file, tonic expects us to provide our own connector, and
// this ignored endpoint. :(
static IGNORED_ENDPOINT_URI: &str = "file://[::]:0";

// Path used to facilitate inter-process communication between the orchestrator
// and the trusted application.
const ORCHESTRATOR_IPC_SOCKET: &str = "/oak_utils/orchestrator_ipc";

// Re-export structs so that they are available at the top level of the SDK.
pub use crypto::{EncryptionKeyHandle, InstanceEncryptionKeyHandle};
pub use orchestrator_client::OrchestratorClient;
