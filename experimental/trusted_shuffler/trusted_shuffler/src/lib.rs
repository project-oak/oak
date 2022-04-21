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
use rand::{seq::SliceRandom, thread_rng};
use std::{
    future::Future,
    marker::{Send, Sync},
    mem::replace,
    ops::DerefMut,
    sync::{Arc, Mutex},
};
use tokio::sync::oneshot;

const CHANNEL_BUFFER_SIZE: usize = 100;
type Request = Vec<u8>;
type Response = Vec<u8>;

struct Message {
    // Arbitrary message data.
    data: Vec<u8>,
    // Channel for sending responses back to the client async tasks.
    response_sender: oneshot::Sender<Response>,
}

// Trusted Shuffler inmpelentation.
// Generic parameter `R` represents a request type, and `S` a response type.
pub struct TrustedShuffler<F, O>
where
    F: Send + Sync + 'static + FnOnce(Request) -> O,
    O: Send + Sync + Future<Output = Response>,
{
    // Value k that represents k-anonymity.
    anonymity_value: usize,

    // Current batch of requests to be shuffled.
    current_requests: Arc<Mutex<Vec<Message>>>,

    // Async function that sends a request to the backend and returns a response.
    request_sender: F,
}

impl<F, O> TrustedShuffler<F, O>
where
    F: Send + Sync + Clone + 'static + FnOnce(Request) -> O,
    O: Send + Sync + Future<Output = Response>,
{
    pub fn new(anonymity_value: usize, request_sender: F) -> Self {
        Self {
            anonymity_value,
            current_requests: Arc::new(Mutex::new(vec![])),
            request_sender,
        }
    }

    // Asynchronously handles an incoming request.
    pub async fn invoke(&self, request: Request) -> anyhow::Result<Response> {
        let (sender, receiver) = oneshot::channel();

        let request = Message {
            data: request,
            response_sender: sender,
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
                let request_sender = self.request_sender.clone();
                tokio::spawn(async move {
                    TrustedShuffler::shuffle_requests(requests, request_sender).await;
                });
            }
        }

        receiver.await.context("Couldn't receive response")
    }

    // Shuffles requests and sends them to the backend using the
    // [`TrustedShuffler::request_sender`].
    async fn shuffle_requests(mut requests: Vec<Message>, request_sender: F) {
        requests.shuffle(&mut thread_rng());

        // let response_futures: Vec<impl Future<Output = Message>> = requests
        let response_futures: Vec<_> = requests
            .drain(..)
            .into_iter()
            .map(|request| {
                let request_sender_clone = request_sender.clone();
                async move {
                    let response = (request_sender_clone)(request.data).await;
                    Message {
                        data: response,
                        response_sender: request.response_sender,
                    }
                }
            })
            .collect();
        let responses = join_all(response_futures).await;

        TrustedShuffler::shuffle_responses(responses);
    }

    // Shuffles received backend responses and sends them back to the client async tasks using
    // corresponding channels defined in the [`Message::response_sender`].
    fn shuffle_responses(mut responses: Vec<Message>) {
        responses.shuffle(&mut thread_rng());

        for response in responses.drain(..) {
            response.response_sender.send(response.data.clone());
        }
    }
}
