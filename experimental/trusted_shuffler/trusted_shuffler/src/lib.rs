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
use hyper::Body;
use std::{
    cmp::Ordering,
    marker::{Send, Sync},
    mem::take,
    ops::DerefMut,
    sync::{Arc, Mutex},
};
use tokio::{sync::oneshot, time::Duration};

type Request = hyper::Request<Body>;
type Response = hyper::Response<Body>;

enum Wrapper {
    Request(Request),
    Response(Response),
}

// TODO(mschett): Implement an ordering on wrappers.
fn cmp(_w1: &Wrapper, _w2: &Wrapper) -> Ordering {
    todo!()
}

struct Message {
    // Determines the original order in which messages arrived.
    // Index is used to send requests back to the client in the order of arrival.
    index: usize,
    // Arbitrary message data.
    data: Wrapper,
    // Channel for sending responses back to the client async tasks.
    response_sender: oneshot::Sender<Response>,
}

// TODO(mschett): Remove dead code.
impl Message {
    #[allow(dead_code)]
    fn new_response(self, data: Wrapper) -> Message {
        Message {
            index: self.index,
            data,
            response_sender: self.response_sender,
        }
    }

    // The Trusted Shuffler responds with the `EMPTY_RESPONSE` if the backend does not respond
    // within a given timeout.
    #[allow(dead_code)]
    fn new_empty_response(self) -> Message {
        self.new_response(Wrapper::Response(hyper::Response::default()))
    }
}

#[async_trait]
pub trait RequestHandler: Send + Sync {
    async fn handle(&self, request: Request) -> anyhow::Result<Response>;
}

// Trusted Shuffler implementation.
pub struct TrustedShuffler {
    // Value k that represents k-anonymity.
    k: usize,

    // When the k-th request in a batch arrives we start a timeout. For any request were the
    // Trusted Shuffler did not receive a response from the backend after the timeout, the Trusted
    // Shuffler sends an empty response.
    timeout: Option<Duration>,

    // Current batch of requests to be shuffled.
    // Mutex is used because messages are collected in different async tasks.
    requests_to_shuffle: Arc<Mutex<Vec<Message>>>,

    // Async function that sends a request to the backend and returns a response.
    request_handler: Arc<dyn RequestHandler>,
}

impl TrustedShuffler {
    pub fn new(
        k: usize,
        timeout: Option<Duration>,
        request_handler: Arc<dyn RequestHandler>,
    ) -> Self {
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
                data: Wrapper::Request(request),
                response_sender,
            };

            requests_to_shuffle.push(request);

            if requests_to_shuffle.len() >= self.k {
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
    // [`TrustedShuffler::request_handler`].
    async fn shuffle_requests(
        mut requests: Vec<Message>,
        request_handler: Arc<dyn RequestHandler>,
        timeout: Option<Duration>,
    ) -> anyhow::Result<()> {
        requests.sort_by(|first, second| cmp(&first.data, &second.data));

        let response_futures: FuturesOrdered<_> = requests
            .into_iter()
            .map(|request| {
                // TODO(mschett): Refactor to not build message in every branch.
                let request_handler_clone = request_handler.clone();
                let index = request.index;
                let response_sender = request.response_sender;
                let data = get_request(request.data);
                async move {
                    match timeout {
                        None => request_handler_clone
                            .handle(data)
                            .await
                            .map(|response| Message {
                                index,
                                data: Wrapper::Response(response),
                                response_sender,
                            }),
                        Some(timeout) => {
                            match tokio::time::timeout(timeout, request_handler_clone.handle(data))
                                .await
                            {
                                Err(_) => Ok(Message {
                                    index,
                                    data: Wrapper::Response(hyper::Response::default()),
                                    response_sender,
                                }),
                                Ok(response) => response.map(|response| Message {
                                    index,
                                    data: Wrapper::Response(response),
                                    response_sender,
                                }),
                            }
                        }
                    }
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
                        .send(get_response(data))
                        .map_err(|_data| anyhow!("Couldn't send response"))
                },
            )
            .collect::<Result<Vec<_>, _>>()
            .map(|_: Vec<()>| ())
    }
}

// TODO(mschett): Implement todo!()
fn get_response(w: Wrapper) -> Response {
    match w {
        Wrapper::Response(r) => r,
        _ => todo!(),
    }
}

// TODO(mschett): Implement todo!()
fn get_request(w: Wrapper) -> Request {
    match w {
        Wrapper::Request(r) => r,
        _ => todo!(),
    }
}
