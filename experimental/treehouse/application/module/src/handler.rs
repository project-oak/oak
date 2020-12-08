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
use fetch::CalendarEvents;
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

        // Collect all the events that happened on the date given in the request.
        let date = request.date;
        let latest_start_time = format!("{}T23:59:59Z", date);
        let earliest_end_time = format!("{}T00:00:00Z", date);

        let uri = "https://www.googleapis.com/calendar/v3/calendars/primary/events";
        let uri_with_query = format!(
            "{}?timeMax={}&timeMin={}&maxResults=10",
            uri, latest_start_time, earliest_end_time
        );

        let request = http::Request::builder()
            .method(http::Method::GET)
            .uri(uri_with_query)
            .body(vec![])
            .expect("Could not build request");
        let response = self
            .http_client
            .send_request(request, &Label::public_untrusted())
            .expect("Could not get response");

        let events: CalendarEvents = serde_json::from_slice(response.body()).unwrap();
        if let Some(event) = events.items.get(0) {
            Ok(GetCardsResponse {
                cards: vec![Card {
                    title: "Example Card #0".to_string(),
                    subtitle: "subtitle".to_string(),
                    description: event.description.to_string(),
                    media_png: vec![],
                }],
            })
        } else {
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
}

oak::entrypoint_command_handler_init!(handler => Handler);

oak::impl_dispatcher!(impl Handler : TreehouseDispatcher);
