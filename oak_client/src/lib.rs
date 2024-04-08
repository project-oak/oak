//
// Copyright 2023 The Project Oak Authors
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

pub mod proto {
    pub mod oak {
        pub mod session {
            pub mod v1 {
                #![allow(clippy::return_self_not_must_use)]
                #![allow(clippy::large_enum_variant)]
                tonic::include_proto!("oak.session.v1");
            }
        }
        pub use oak_proto_rust::oak::{attestation, crypto};
    }
}

pub mod client;
pub mod transport;
pub mod verifier;
