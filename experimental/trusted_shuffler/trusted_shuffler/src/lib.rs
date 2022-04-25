//
// Copyright 2022 The Project Oak Authors
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

//! Trusted Shuffler implementation.

#[cfg(test)]
mod tests;

use anyhow::{anyhow, Context};
use futures::future::join_all;
use std::{
    future::Future,
    marker::{Send, Sync},
    mem::replace,
    ops::DerefMut,
    sync::{Arc, Mutex},
};
use tokio::sync::oneshot;

type Request = Vec<u8>;
type Response = Vec<u8>;

struct Message {
    // Arbitrary message data.
    data: Vec<u8>,
    // Channel for sending responses back to the client async tasks.
    response_sender: oneshot::Sender<Response>,
}

// Trusted Shuffler implementation.
pub struct TrustedShuffler<F, O>
where
    F: Send + Sync + 'static + FnOnce(Request) -> O,
    O: Send + Sync + Future<Output = Response>,
{
    // Value k that represents k-anonymity.
    anonymity_value: usize,

    // Current batch of requests to be shuffled.
    // Mutex is used because messages are collected from different async tasks.
    current_requests: Arc<Mutex<Vec<Message>>>,

    // Async function that sends a request to the backend and returns a response.
    request_handler: F,
}

impl<F, O> TrustedShuffler<F, O>
where
    F: Send + Sync + Clone + 'static + FnOnce(Request) -> O,
    O: Send + Sync + Future<Output = Response>,
{
    pub fn new(anonymity_value: usize, request_handler: F) -> Self {
        Self {
            anonymity_value,
            current_requests: Arc::new(Mutex::new(vec![])),
            request_handler,
        }
    }

    // Asynchronously handles an incoming request.
    pub async fn invoke(&self, request: Request) -> anyhow::Result<Response> {
        let (response_sender, response_receiver) = oneshot::channel();

        let request = Message {
            data: request,
            response_sender,
        };

        // Check if the request batch is filled and create a separate task for shuffling requests.
        {
            let mut current_requests = self
                .current_requests
                .lock()
                .map_err(|error| anyhow!("Couldn't lock current messages mutex: {:?}", error))?;
            current_requests.push(request);

            if current_requests.len() >= self.anonymity_value {
                // Replace current requests with an empty vector.
                let requests = replace(current_requests.deref_mut(), vec![]);

                // Shuffle current requests and send them to the backend.
                let request_handler = self.request_handler.clone();
                tokio::spawn(async move {
                    if let Err(error) =
                        TrustedShuffler::shuffle_requests(requests, request_handler).await
                    {
                        log::error!("Shuffling error: {:?}", error);
                    }
                });
            }
        }

        response_receiver.await.context("Couldn't receive response")
    }

    // Lexicographically sorts requests and sends them to the backend using the
    // [`TrustedShuffler::request_sender`].
    async fn shuffle_requests(
        mut requests: Vec<Message>,
        request_handler: F,
    ) -> anyhow::Result<()> {
        requests.sort_by(|first, second| first.data.cmp(&second.data));

        let response_futures = requests.into_iter().map(|request| {
            let request_handler_clone = request_handler.clone();
            async move {
                let response = (request_handler_clone)(request.data).await;
                Message {
                    data: response,
                    response_sender: request.response_sender,
                }
            }
        });
        let responses = join_all(response_futures).await;

        Self::shuffle_responses(responses)
    }

    // Lexicographically sorts received backend responses and sends them back to the client async
    // tasks using corresponding channels defined in the [`Message::response_sender`].
    fn shuffle_responses(mut responses: Vec<Message>) -> anyhow::Result<()> {
        responses.sort_by(|first, second| first.data.cmp(&second.data));

        for response in responses {
            response
                .response_sender
                .send(response.data.clone())
                .map_err(|error| anyhow!("Couldn't send the response: {:?}", error))?;
        }
        Ok(())
    }
}
