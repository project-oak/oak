//
// Copyright 2021 The Project Oak Authors
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

use crate::{
    logger::Logger,
    server::{BoxedExtension, BoxedExtensionFactory, Endpoint, ExtensionFactory, UwabiExtension},
};
use async_trait::async_trait;
use oak_functions_abi::proto::ChannelHandle;
use serde::{Deserialize, Serialize};
pub struct TestingFactory {
    logger: Logger,
}

impl TestingFactory {
    pub fn new_boxed_extension_factory(logger: Logger) -> anyhow::Result<BoxedExtensionFactory> {
        Ok(Box::new(Self { logger }))
    }
}

impl ExtensionFactory for TestingFactory {
    fn create(&self) -> anyhow::Result<BoxedExtension> {
        let extension = TestingExtension {
            logger: self.logger.clone(),
            endpoint: None,
        };
        Ok(BoxedExtension::Uwabi(Box::new(extension)))
    }
}

#[allow(dead_code)]
pub struct TestingExtension {
    logger: Logger,
    endpoint: Option<Endpoint>,
}

#[derive(Serialize, Deserialize)]
// Note that currently the caller is responsible that the Request is send to the extension, and
// the extension responds with the response.
pub enum TestingMessage {
    EchoRequest(String),
    EchoResponse(String),
}

#[async_trait]
impl UwabiExtension for TestingExtension {
    fn get_channel_handle(&self) -> oak_functions_abi::proto::ChannelHandle {
        ChannelHandle::Testing
    }

    fn get_endpoint_mut(&mut self) -> &mut Endpoint {
        match &mut self.endpoint {
            Some(endpoint) => endpoint,
            None => panic!("No endpoint set for extension"),
        }
    }

    fn set_endpoint(&mut self, endpoint: Endpoint) {
        if self.endpoint.is_none() {
            self.endpoint = Some(endpoint);
        }
    }

    async fn run(mut self: Box<Self>) {
        let endpoint = self.get_endpoint_mut();
        let receiver = &mut endpoint.receiver;
        let sender = &mut endpoint.sender;

        // The runtime endpoint continiously reads messages from the Wasm module endpoint until
        // all senders from the Wasm endpoint are closed.
        //
        // If the Testing Message is not an expected request, the Testing Extension panics.
        while let Some(request) = receiver.recv().await {
            let deserialized_testing_message =
                bincode::deserialize(&request).expect("Fail to deserialize testing message.");
            match deserialized_testing_message {
                TestingMessage::EchoRequest(echo_message) => {
                    let echo_response = TestingMessage::EchoResponse(echo_message);
                    let serialized_echo_response = bincode::serialize(&echo_response)
                        .expect("Fail to serialize testing message.");
                    let result = sender.send(serialized_echo_response).await;
                    assert!(result.is_ok())
                }
                _ => panic!("Unexpected Testing Message: {:?}", request),
            }
        }
    }
}
