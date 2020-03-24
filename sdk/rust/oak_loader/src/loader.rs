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

use oak_runtime::{configure_and_run, RuntimeRef, ChannelWriter};
use oak_runtime::proto::ApplicationConfiguration;

struct Loader {
    runtime: RuntimeRef,
    channel: ChannelWriter,
    grpc_server: Server,
}

impl Loader {
    fn new(app_config: &ApplicationConfiguration) -> Result<Self, String> {
        self.runtime, self.channel = {
            match configure_and_run(app_config) {
                Ok() => ,
                Err() => ,
            }
        }
    }
}
