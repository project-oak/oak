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
    Card, GetCardsRequest, GetCardsResponse, Treehouse, TreehouseDispatcher, TreehouseHandlerInit,
};
use log::debug;
use oak::grpc;
use oak_abi::label::Label;

pub struct Handler {
    http_client: oak::http::client::HttpClient,
}

impl oak::WithInit for Handler {
    type Init = TreehouseHandlerInit;

    fn create(init: Self::Init) -> Self {
        oak::logger::init(init.log_sender.unwrap(), log::Level::Debug).unwrap();
        Self {
            http_client: oak::http::client::from_sender(
                init.http_invocation_sender.unwrap(),
                "".to_string(),
            ),
        }
    }
}

impl Treehouse for Handler {
    fn get_cards(&mut self, request: GetCardsRequest) -> grpc::Result<GetCardsResponse> {
        debug!("Received request: {:?}", request);

        let request = http::Request::builder()
            .method(http::Method::GET)
            .uri("http://www.google.com")
            .body(vec![])
            .expect("Could not build request");
        self.http_client
            .send_request(request, &Label::public_untrusted())
            .expect("Could not get response");

        Ok(GetCardsResponse {
            cards: vec![Card {
                title: "Example Card #0".to_string(),
                subtitle: "subtitle".to_string(),
                description: "".to_string(),
                media_png: vec![],
            }],
        })
    }
}

oak::entrypoint_command_handler_init!(handler => Handler);

oak::impl_dispatcher!(impl Handler : TreehouseDispatcher);
