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

pub mod proto {
    include!(concat!(env!("OUT_DIR"), "/oak.examples.minimal.rs"));
}

use log::info;
use oak::grpc;
use proto::{Minimal, MinimalDispatcher, MinimalReply, MinimalRequest};

oak::entrypoint!(oak_main => |_in_channel| {
    oak::logger::init_default();
    let node = Node {};
    let dispatcher = MinimalDispatcher::new(node);
    let grpc_channel =
        oak::grpc::server::init("[::]:8080").expect("could not create gRPC server pseudo-Node");
    oak::run_event_loop(dispatcher, grpc_channel);
});

struct Node {}

impl Minimal for Node {
    fn knock(&mut self, req: MinimalRequest) -> grpc::Result<MinimalReply> {
        info!("{} is knocking", req.request);
        let mut res = MinimalReply::default();
        res.reply = format!("Hello {}!", req.request);
        Ok(res)
    }
}
