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
use rand::{seq::SliceRandom, thread_rng};
use std::{
    collections::{HashMap, HashSet, VecDeque},
    future::Future,
    sync::{Arc, Mutex},
    marker::{Send, Sync},
};
use tokio::sync::{
    mpsc::{self, Receiver, Sender},
    oneshot,
};

const CHANNEL_BUFFER_SIZE: usize = 100;
type Request = Vec<u8>;
type Response = Vec<u8>;

#[derive(Eq, PartialEq, Hash, Clone, Debug)]
pub struct BatchId(u64);

#[derive(Eq, PartialEq, Hash, Clone, Debug)]
pub struct RequestId {
    id: u64,
    batch_id: BatchId,
}

struct RequestIdGenerator {
    batch_size: usize,
    batch_counter: usize,
    next_request_id: u64,
    next_batch_id: u64,
}

impl RequestIdGenerator {
    pub fn new(batch_size: usize) -> Self {
        Self {
            batch_size,
            batch_counter: 0,
            next_request_id: 0,
            next_batch_id: 0,
        }
    }

    pub fn generate(&mut self) -> RequestId {
        assert!(self.batch_counter <= self.batch_size);
        if self.batch_counter == self.batch_size {
            self.next_batch_id += 1;
            self.batch_counter = 0;
        }

        let request_id = self.next_request_id;
        let batch_id = self.next_batch_id;
        self.next_request_id += 1;
        self.batch_counter += 1;
        RequestId {
            id: request_id,
            batch_id: BatchId(batch_id),
        }
    }
}

#[derive(Clone)]
struct Message {
// struct Message<R: Send + Sync + Clone + Sized + 'static> {
    id: RequestId,
    data: Vec<u8>,
    // data: R,
}

// Trusted Shuffler inmpelentation.
// Generic parameter `R` represents a request type, and `S` a response type.
#[derive(Clone)]
pub struct TrustedShuffler<F, O>
// pub struct TrustedShuffler<R, S, F>
where
//     R: Send + Sync + Clone + Sized + 'static,
//     S: Send + Sync + Clone + Sized + 'static,
//     F: Send + Sync + Clone + 'static + FnOnce(R) -> dyn Future<Output = S>,
    F: Send + Sync + Clone + 'static + FnOnce(Request) -> O,
    O: Future<Output = Response> + std::marker::Send,
    // F: Send + Sync + Clone + 'static + FnOnce(Request) -> impl Future<Output = Response>,
{
    // Value k that represents k-anonymity.
    anonymity_value: usize,

    // Generator for creating unique IDs for incoming requests.
    request_id_generator: Arc<Mutex<RequestIdGenerator>>,

    // Map for sending responses back to the clients.
    request_promise_map: Arc<Mutex<HashMap<RequestId, oneshot::Sender<Response>>>>,
    // request_promise_map: Arc<Mutex<HashMap<RequestId, oneshot::Sender<S>>>>,

    // Queue of incoming requests to be shuffled.
    incoming_request_queue: Arc<Mutex<VecDeque<Message>>>,
    // incoming_request_queue: AsyncQueue<Message<R>>,

    // Queue of shuffled requests to be sent out.
    // outgoing_request_queue: VecDeque<Message<R>>,
    // outgoing_request_queue: AsyncQueue<Message<R>>,

    // Map containing batches of responses to be received from the backend.
    // Once a particular item receives all of the responses, they are being
    // shuffled back to the clients.
    response_promise_map: Arc<Mutex<HashMap<BatchId, (HashSet<RequestId>, Vec<Message>)>>>,

    // Queue of incoming batched responses to be shuffled.
    // incoming_response_queue: VecDeque<Vec<Message<S>>>,
    // incoming_response_queue: AsyncQueue<Vec<Message<S>>>,

    // Async function that sends a request to the backend and returns a
    // responce.
    request_sender: F,
}

impl<F, O> TrustedShuffler<F, O>
// impl<R, S, F> TrustedShuffler<R, S, F>
where
//     R: Send + Sync + Clone + Sized + 'static,
//     S: Send + Sync + Clone + Sized + 'static,
    F: Send + Sync + Clone + 'static + FnOnce(Request) -> O,
    O: Send + Sync + Future<Output = Response>,
    // F: Send + Sync + Clone + 'static + FnOnce(Request) -> impl Future<Output = Response>,
{
    pub fn new(anonymity_value: usize, request_sender: F) -> Self {
        Self {
            anonymity_value,
            request_id_generator: Arc::new(Mutex::new(RequestIdGenerator::new(anonymity_value))),
            request_promise_map: Arc::new(Mutex::new(HashMap::new())),
            // incoming_request_queue: AsyncQueue::new(CHANNEL_BUFFER_SIZE),
            incoming_request_queue: Arc::new(Mutex::new(VecDeque::new())),
            // outgoing_request_queue: AsyncQueue::new(CHANNEL_BUFFER_SIZE),
            // outgoing_request_queue: VecDeque::new(),
            response_promise_map: Arc::new(Mutex::new(HashMap::new())),
            // incoming_response_queue: AsyncQueue::new(CHANNEL_BUFFER_SIZE),
            // incoming_response_queue: VecDeque::new(),
            request_sender,
        }
    }

    // Asynchronously handles incoming requests.
    pub async fn invoke(&self, request: Request) -> anyhow::Result<Response> {
        let request_id = self.request_id_generator.lock().unwrap().generate();
        let request = Message {
            id: request_id.clone(),
            data: request,
        };

        let mut incoming_request_queue = self.incoming_request_queue.lock().unwrap();
        incoming_request_queue.push_back(request);

        let (sender, receiver) = oneshot::channel();
        self.request_promise_map
            .lock()
            .unwrap()
            .insert(request_id, sender);

        if incoming_request_queue.len() >= self.anonymity_value {
            let batch = incoming_request_queue
                .drain(..)
                .take(self.anonymity_value)
                .collect();
            self.shuffle_forward(batch);
        }

        receiver.await.context("Couldn't receive response")
    }

    // Pushes a backend response through the Trusted Shuffler back to the client.
    // `request_id` should correspond to the original client request sent to the
    // backend.
    pub async fn push_response(
        &mut self,
        request_id: RequestId,
        response: Response,
    ) -> anyhow::Result<()> {
        let mut response_promise_map = self.response_promise_map.lock().unwrap();

        let mut full_response_batch = vec![];
        match response_promise_map.get_mut(&request_id.batch_id) {
            Some(batch_entry) => {
                let id_set = &mut batch_entry.0;
                if id_set.remove(&request_id) {
                    let responses = &mut batch_entry.1;
                    responses.push(Message {
                        id: request_id.clone(),
                        data: response,
                    });

                    if id_set.is_empty() {
                        full_response_batch = responses.drain(..).collect();
                    }
                } else {
                    Err(anyhow!("Invalid request id: {:?}", request_id))?;
                }
            }
            None => Err(anyhow!("Invalid request batch: {:?}", request_id.batch_id))?,
        }

        if !full_response_batch.is_empty() {
            self.shuffle_backward(full_response_batch);
            response_promise_map.remove(&request_id.batch_id);
        }

        Ok(())
    }

    pub fn shuffle_forward(&self, batch: Vec<Message>) {
        batch.shuffle(&mut thread_rng());

        for request in batch.drain(..) {
            let request_sender = self.request_sender.clone();
            let join_handle = tokio::spawn(async move {
                let response = (request_sender)(request.data).await;
            });
        }
    }

    pub fn shuffle_backward(&self, batch: Vec<Message>) {
        batch.shuffle(&mut thread_rng());

        let request_promise_map = self.request_promise_map.lock().unwrap();
        for response in batch.drain(..) {
            if let Some(promise) = request_promise_map.remove(&response.id) {
                let join_handle = tokio::spawn(async move {
                    promise.send(response.data);
                });
            }
        }
    }
}
