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

pub mod oak {
    pub mod containers {
        #![allow(clippy::return_self_not_must_use)]
        tonic::include_proto!("oak.containers");
        pub mod v1 {
            #![allow(clippy::return_self_not_must_use)]
            tonic::include_proto!("oak.containers.v1");
        }
    }
    pub mod functions {
        #![allow(clippy::return_self_not_must_use)]
        tonic::include_proto!("oak.functions");
        pub mod standalone {
            #![allow(clippy::return_self_not_must_use)]
            tonic::include_proto!("oak.functions.standalone");
        }
    }

    pub mod key_provisioning {
        pub mod v1 {
            #![allow(clippy::return_self_not_must_use)]
            tonic::include_proto!("oak.key_provisioning.v1");
        }
    }
    pub mod session {
        pub mod v1 {
            #![allow(clippy::return_self_not_must_use)]
            tonic::include_proto!("oak.session.v1");
        }
    }
    pub mod debug {
        tonic::include_proto!("oak.debug");
    }
    pub mod verity {
        #![allow(clippy::return_self_not_must_use)]
        tonic::include_proto!("oak.verity");
    }
}
