//
// Copyright 2018 The Project Oak Authors
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

use crate::proto::oak::examples::veracruz_demo::{
    RandomRequest, RandomResponse, RandomResult, VeracruzDemo, VeracruzDemoDispatcher, Init,
};
use log::info;
use oak::grpc;
use http;
use oak::http::create_http_invocation;
use oak_abi::{
    label::{confidentiality_label, tls_endpoint_tag}
};

use oak::io::SenderExt;

oak::impl_dispatcher!(impl Handler : VeracruzDemoDispatcher);
oak::entrypoint_command_handler_init!(handler => Handler);

pub struct Handler {
    translator: Option<translator_common::TranslatorClient>,
}

impl oak::WithInit for Handler {
    type Init = Init;

    fn create(init: Self::Init) -> Self {
        oak::logger::init(init.log_sender.unwrap(), log::Level::Debug).unwrap();
        Self {
            translator: init
                .translator_sender
                .map(translator_common::TranslatorClient),
        }
    }
}

impl Handler {
    fn translate(&self, text: &str, from_lang: &str, to_lang: &str) -> Option<String> {
        let client = self.translator.as_ref()?;
        translator_common::translate(client, text, from_lang, to_lang)
    }
}

impl VeracruzDemo for Handler {
    fn generate_random(&mut self, req: RandomRequest) -> grpc::Result<RandomResponse> {
        info!("generate random called requesting {:} bytes", req.number_of_bytes);
        let mut response: RandomResponse = RandomResponse::default();
        let mut data: Vec<u8> = vec![0; req.number_of_bytes as usize];
        oak::random_get(&mut data).unwrap();
        response.data = data;
        Ok(response)
    }

    fn forward_random(&mut self, req: RandomRequest) -> grpc::Result<RandomResult> {
        info!("forward random called requesting {:} bytes", req.number_of_bytes);
        let mut result: RandomResult = RandomResult::default();
        let mut data: Vec<u8> = vec![0; req.number_of_bytes as usize];
        match oak::random_get(&mut data) {
            Ok(_) => {},
            Err(_) => {
                result.status = 1;
                return Ok(result);
            }
        }

        // Here's where the fun begins. How do we instantiate a http client pseudo node?

        let authority = "https://172.17.0.1:8090/hello";
        let request = http::Request::builder()
            .method(http::Method::GET)
            .uri(authority)
            .body(data)
            .unwrap();
        info!("creating client node");
        let client_invocation_sender = oak::http::client::init("").unwrap();
        let label = oak_abi::label::Label::public_untrusted();
        //let label = confidentiality_label(tls_endpoint_tag(authority));
        let (client_invocation, client_invocation_source) = create_http_invocation(&label).unwrap();
        info!("sending client_invocation to client_invocation_sender");
        client_invocation_sender.send(&client_invocation).unwrap();
        info!("Sending request to client_invocation_source");
        match client_invocation_source.send(request) {
            Ok(whatisthis) => info!("Send Ok:{:?}", whatisthis),
            Err(err) => info!("Send Err:{:?}", err),
        }
        info!("Receiving through client_invocation_source");
        match client_invocation_source.receive() {
            Ok(whatisthis) => info!("Receive Ok:{:?}", whatisthis),
            Err(err) => info!("Receive Err:{:?}", err),
        }
        // info!("forward random calling send");
        // let send_request: http::request::Request<Vec<u8>> = http::request::Builder::new()
        //     .uri("https://172.17.0.1:8090/hello")
        //     .body(data).expect("Crap");
        // match client_invocation_source.send(send_request) {
        //     Ok(whatisthis) => info!("It's all good:{:?}", whatisthis),
        //     Err(err) => info!("crap:{:?}", err),
        // }
        // match client_invocation_source.receive() {
        //     Ok(whatisthis) => info!("Receive went well:{:?}", whatisthis),
        //     Err(err) => info!("receive failed:{:?}", err),
        // }

        result.status = 0;

        Ok(result)
    }

}
