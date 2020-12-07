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

use crate::proto::oak::examples::treehouse::{
    Treehouse, TreehouseInit, TreehouseResponse, TreehouseRequest, TreehouseDispatcher,
};
use log::debug;
use oak::grpc;

#[derive(Default)]
pub struct Handler {
}

impl oak::WithInit for Handler {
    type Init = TreehouseInit;

    fn create(init: Self::Init) -> Self {
        oak::logger::init(init.log_sender.unwrap(), log::Level::Debug).unwrap();
        Self::default()
    }
}

impl Treehouse for Handler {
    fn get_data(
        &mut self,
        request: TreehouseRequest,
    ) -> grpc::Result<TreehouseResponse> {
        debug!("Received request: {:?}", request);

        // create an HTTP client pseudo-Node.
        let http_client = oak::http::client::init("")
            .expect("Could not create HttpClient pseudo-node");
        let request = http::Request::builder()
            .method(http::Method::GET)
            .uri("http://www.google.com")
            .body(vec![])
            .expect("Could not build request");
        http_client
            .send_request(request, &Label::public_untrusted())
            .expect("Could not get response");


        Ok(TreehouseResponse {})
    }
}

oak::entrypoint_command_handler_init!(handler => Handler);

oak::impl_dispatcher!(impl Handler : TreehouseDispatcher);
