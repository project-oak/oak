//
// Copyright 2019 The Project Oak Authors
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

//! Auto-generated code derived from protocol buffer definitions.

pub mod oak {
    pub mod authentication {
        include!(concat!(env!("OUT_DIR"), "/oak.authentication.rs"));
    }

    pub mod introspection_events {
        include!(concat!(env!("OUT_DIR"), "/oak.introspection_events.rs"));
    }

    pub mod invocation {
        include!(concat!(env!("OUT_DIR"), "/oak.invocation.rs"));
    }

    // Add a refernce to the label proto to ensure that `super::label::Label`
    // can be resolved. Prost references it in the code genereated from the
    // introspection_events proto and expects the module to resolve.
    // Ref: https://github.com/danburkert/prost/issues/142
    pub mod label {
        pub use oak_abi::proto::oak::label::Label;
    }
}
