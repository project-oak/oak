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

pub mod google {
    pub mod rpc {
        include!("google.rpc.rs");
    }
}

pub mod oak {
    include!("oak_abi.rs");

    pub mod label {
        include!("oak.label.rs");
    }

    pub mod encap {
        include!("oak.encap.rs");
    }

    pub mod log {
        include!("oak.log.rs");
    }
}
