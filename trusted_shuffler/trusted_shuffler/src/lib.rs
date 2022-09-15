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
use hyper::Uri;
use std::{
    cmp::Ordering,
    mem::take,
    ops::DerefMut,
    sync::{Arc, Mutex},
    vec,
};
use tokio::{sync::oneshot, time::Duration};

#[derive(Debug, PartialEq)]
pub struct TrustedShufflerRequest {
    pub body: Vec<u8>,
    pub headers: hyper::HeaderMap,
    pub uri: Uri,
}

impl TrustedShufflerRequest {
    // We only compare the body, and we need revisit this and decide if this
    // is how we want to sort our requests.
    fn compare_body(&self, r2: &TrustedShufflerRequest) -> Ordering {
        self.body.cmp(&r2.body)
    }
}

#[derive(Debug, PartialEq)]
pub struct TrustedShufflerResponse {
    pub data: hyper::body::Bytes,
    pub trailers: hyper::HeaderMap,
}

impl TrustedShufflerResponse {
    fn empty() -> TrustedShufflerResponse {
        TrustedShufflerResponse {
            data: hyper::body::Bytes::new(),
            trailers: hyper::HeaderMap::new(),
        }
    }
}

struct RequestMessage {
    // Determines the original order in which Trusted Shuffler Requests arrived.
    // Index is used to send responses back to the client in the order of arrival.
    index: usize,
    // A TrustedShufflerRequest.
    data: TrustedShufflerRequest,
    // Channel for sending responses back to the client async tasks.
    response_sender: oneshot::Sender<TrustedShufflerResponse>,
}

struct ResponseMessage {
    // Copied from the corresponding RequestMessage.
    // Determines the original order in which the Trusted Shuffler Request for the Response
    // arrived. Index is used to send responses back to the client in the order of arrival.
    index: usize,
    // The TrustedShufflerResponse to a TrustedShufflerRequest.
    data: TrustedShufflerResponse,
    // Copied from the corresponding RequestMessage.
    // Channel for sending responses back to the client async tasks.
    response_sender: oneshot::Sender<TrustedShufflerResponse>,
}

#[async_trait]
pub trait RequestHandler: Send + Sync {
    async fn handle(
        &self,
        request: TrustedShufflerRequest,
    ) -> anyhow::Result<TrustedShufflerResponse>;
}

// Trusted Shuffler implementation.
pub struct TrustedShuffler {
    // The size of a batch.
    batch_size: usize,

    // When `batch_size` requests arrived we start a timeout. For any request were the
    // Trusted Shuffler did not receive a response from the backend after the timeout, the Trusted
    // Shuffler sends an empty response.
    timeout: Option<Duration>,

    // Current batch of requests to be shuffled.
    // Mutex is used because messages are collected in different async tasks.
    requests_to_shuffle: Arc<Mutex<Vec<RequestMessage>>>,

    // Async function that sends a request to the backend and returns a response.
    request_handler: Arc<dyn RequestHandler>,
}

impl TrustedShuffler {
    pub fn new(
        batch_size: usize,
        timeout: Option<Duration>,
        request_handler: Arc<dyn RequestHandler>,
    ) -> Self {
        Self {
            batch_size,
            timeout,
            requests_to_shuffle: Arc::new(Mutex::new(vec![])),
            request_handler,
        }
    }

    // Asynchronously handles an incoming request.
    pub async fn invoke(
        &self,
        request: TrustedShufflerRequest,
    ) -> anyhow::Result<TrustedShufflerResponse> {
        let (response_sender, response_receiver) = oneshot::channel();

        // Check if the request batch is filled and create a separate task for shuffling requests.
        {
            let mut requests_to_shuffle = self
                .requests_to_shuffle
                .lock()
                .map_err(|error| anyhow!("Couldn't lock current messages mutex: {:?}", error))?;

            let request = RequestMessage {
                index: requests_to_shuffle.len(),
                data: request,
                response_sender,
            };

            requests_to_shuffle.push(request);

            if requests_to_shuffle.len() >= self.batch_size {
                // Replace current requests with an empty vector.
                let requests = take(requests_to_shuffle.deref_mut());

                // Shuffle requests and spawn async tasks for sending them to the backend.
                let request_handler = self.request_handler.clone();
                let timeout = self.timeout;
                tokio::spawn(async move {
                    if let Err(error) =
                        TrustedShuffler::shuffle_requests(requests, request_handler, timeout).await
                    {
                        log::error!("Shuffling error: {:?}", error);
                    }
                });
            }
        }

        response_receiver.await.context("Couldn't receive response")
    }

    // Lexicographically sorts requests and sends them to the backend using the
    // [`TrustedShuffler::request_handler`]. For every batch of requests it either waits until all
    // responses are received, except if a timeout is set, then it sends a default response.
    async fn shuffle_requests(
        mut requests: Vec<RequestMessage>,
        request_handler: Arc<dyn RequestHandler>,
        timeout: Option<Duration>,
    ) -> anyhow::Result<()> {
        requests.sort_by(|first, second| first.data.compare_body(&second.data));

        let response_futures: FuturesOrdered<_> = requests
            .into_iter()
            .map(|request_message| {
                // Deconstruct the Message holding a request in data.
                let request_handler_clone = request_handler.clone();
                let index = request_message.index;
                let response_sender = request_message.response_sender;
                let data = request_message.data;
                async move {
                    let response = match timeout {
                        None => request_handler_clone.handle(data).await,
                        Some(timeout) => {
                            match tokio::time::timeout(timeout, request_handler_clone.handle(data))
                                .await
                            {
                                Err(_) => Ok(TrustedShufflerResponse::empty()),
                                Ok(response) => response,
                            }
                        }
                    };
                    // Create a Message holding the response in data.
                    response.map(|response| ResponseMessage {
                        index,
                        data: response,
                        response_sender,
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
    fn shuffle_responses(mut responses: Vec<ResponseMessage>) -> anyhow::Result<()> {
        responses.sort_by_key(|response| response.index);

        responses
            .into_iter()
            .map(
                |ResponseMessage {
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
