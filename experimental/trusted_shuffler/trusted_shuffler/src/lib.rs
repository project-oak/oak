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
use async_trait::async_trait;
use futures::{stream::FuturesOrdered, StreamExt};
use std::{
    marker::{Send, Sync},
    mem::take,
    ops::DerefMut,
    sync::{Arc, Mutex},
};
use tokio::{sync::oneshot, time::Duration};

type Request = Vec<u8>;
type Response = Vec<u8>;

struct Message {
    // Determines the original order in which messages arrived.
    // Index is used to send requests back to the client in the order of arrival.
    index: usize,
    // Arbitrary message data.
    data: Vec<u8>,
    // Channel for sending responses back to the client async tasks.
    response_sender: oneshot::Sender<Response>,
}

#[async_trait]
pub trait RequestHandler: Send + Sync {
    async fn handle(&self, request: Vec<u8>) -> anyhow::Result<Vec<u8>>;
}

// Trusted Shuffler implementation.
#[allow(dead_code)]
pub struct TrustedShuffler {
    // Value k that represents k-anonymity.
    k: usize,

    // When the k-th request in a batch arrives we start a timeout. For any request were the
    // Trusted Shuffler did not receive a response from the backend after the timeout, the Trusted
    // Shuffler sends an empty response.
    timeout: Duration,

    // Current batch of requests to be shuffled.
    // Mutex is used because messages are collected in different async tasks.
    requests_to_shuffle: Arc<Mutex<Vec<Message>>>,

    // Async function that sends a request to the backend and returns a response.
    request_handler: Arc<dyn RequestHandler>,
}

impl TrustedShuffler {
    pub fn new(k: usize, timeout: Duration, request_handler: Arc<dyn RequestHandler>) -> Self {
        Self {
            k,
            timeout,
            requests_to_shuffle: Arc::new(Mutex::new(vec![])),
            request_handler,
        }
    }

    // Asynchronously handles an incoming request.
    pub async fn invoke(&self, request: Request) -> anyhow::Result<Response> {
        let (response_sender, response_receiver) = oneshot::channel();

        // Check if the request batch is filled and create a separate task for shuffling requests.
        {
            let mut requests_to_shuffle = self
                .requests_to_shuffle
                .lock()
                .map_err(|error| anyhow!("Couldn't lock current messages mutex: {:?}", error))?;

            let request = Message {
                index: requests_to_shuffle.len(),
                data: request,
                response_sender,
            };

            requests_to_shuffle.push(request);

            if requests_to_shuffle.len() >= self.k {
                // Replace current requests with an empty vector.
                let requests = take(requests_to_shuffle.deref_mut());

                // Shuffle requests and spawn async tasks for sending them to the backend.
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
    // [`TrustedShuffler::request_handler`].
    async fn shuffle_requests(
        mut requests: Vec<Message>,
        request_handler: Arc<dyn RequestHandler>,
    ) -> anyhow::Result<()> {
        requests.sort_by(|first, second| first.data.cmp(&second.data));

        let response_futures: FuturesOrdered<_> = requests
            .into_iter()
            .map(|request| {
                let request_handler_clone = request_handler.clone();
                async move {
                    request_handler_clone
                        .handle(request.data)
                        .await
                        .map(|response| Message {
                            index: request.index,
                            data: response,
                            response_sender: request.response_sender,
                        })
                }
            })
            .collect();
        let responses = response_futures
            .collect::<Vec<Result<_, _>>>()
            .await
            .into_iter()
            .collect::<Result<Vec<_>, _>>()
            .context("Couldn't send responses")?;

        Self::shuffle_responses(responses)
    }

    // Restores the original order in which messages arrived and sends them back to the client async
    // tasks using corresponding channels defined in the [`Message::response_sender`].
    fn shuffle_responses(mut responses: Vec<Message>) -> anyhow::Result<()> {
        responses.sort_by_key(|response| response.index);

        responses
            .into_iter()
            .map(
                |Message {
                     index: _,
                     data,
                     response_sender,
                 }| {
                    response_sender
                        .send(data)
                        .map_err(|_data| anyhow!("Couldn't send response"))
                },
            )
            .collect::<Result<Vec<_>, _>>()
            .map(|_: Vec<()>| ())
    }
}
