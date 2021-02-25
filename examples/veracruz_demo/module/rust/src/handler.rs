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
    RandomRequest, RandomResponse, VeracruzDemo, VeracruzDemoDispatcher, Init,
};
use log::info;
use oak::grpc;

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
        info!("generate random called requesting {:} bits", req.number_of_bytes);
        let mut response: RandomResponse = RandomResponse::default();
        let mut data = vec![0; req.number_of_bytes as usize];
        oak::random_get(&mut data).unwrap();
        response.data = data;
        Ok(response)
    }

}
