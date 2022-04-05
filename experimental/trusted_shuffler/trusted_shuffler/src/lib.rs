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
    collections::{HashMap, HashSet},
    sync::{Arc, Mutex},
};
use tokio::sync::{
    mpsc::{self, Receiver, Sender},
    oneshot,
};

const CHANNEL_BUFFER_SIZE: usize = 100;

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
struct Message<R: std::marker::Send> {
    id: RequestId,
    data: R,
}

#[derive(Clone)]
struct AsyncQueue<T: std::marker::Send> {
    sender: Sender<T>,
    // receiver: Receiver<T>,
    // sender: Arc<Mutex<Sender<T>>>,
    receiver: Arc<Mutex<Receiver<T>>>,
    phantom: std::marker::PhantomData<T>,
}

impl<T: std::marker::Send> AsyncQueue<T> {
    pub fn new(buffer_size: usize) -> Self {
        let (sender, receiver) = mpsc::channel(buffer_size);
        Self {
            sender,
            // receiver,
            // sender: Arc::new(Mutex::new(sender)),
            receiver: Arc::new(Mutex::new(receiver)),
            phantom: std::marker::PhantomData,
        }
    }

    pub async fn get(&self) -> anyhow::Result<T> {
        self.receiver
            .lock()
            .map_err(|error| anyhow!("Couldn't lock mutex: {:?}", error))?
            .recv()
            .await
            .context("Channel closed")
    }

    pub async fn put(&self, item: T) -> anyhow::Result<()> {
        self.sender
            // .lock()
            // .map_err(|error| anyhow!("Couldn't lock mutex: {:?}", error))?
            .send(item)
            .await
            .map_err(|_| anyhow!("Channel closed"))
    }
}

//------------------------------------------------------------------------------
// pub struct TrustedShufflerClientFacingPart<R, S> {
//     // Value k that represents k-anonymity.
//     anonymity_value: usize,

//     // Generator for creating unique IDs for incoming requests.
//     request_id_generator: Arc<Mutex<RequestIdGenerator>>,

//     // Map for sending responses back to the clients.
//     request_promise_map: Arc<Mutex<HashMap<RequestId, oneshot::Sender<S>>>>,

//     // Queue of incoming requests to be shuffled.
//     incoming_request_sender: Sender<Message<R>>,
// }

// pub struct TrustedShufflerForwardPart<R, S> {
//     // Queue of incoming requests to be shuffled.
//     incoming_request_receiver: Arc<Receiver<R>>,

//     // Queue of shuffled requests to be sent out.
//     // outgoing_request_queue: AsyncQueue<Message<R>>,
//     outgoing_request_sender: Sender<Message<R>>,
// }

// pub struct TrustedShufflerBackwardPart<R, S> {
//     // Map for sending responses back to the clients.
//     request_promise_map: Arc<Mutex<HashMap<RequestId, oneshot::Sender<S>>>>,

//     // Queue of incoming batched responses to be shuffled.
//     incoming_response_receiver: Receiver<Vec<Message<S>>>,
// }

// pub struct TrustedShufflerBackendFacingPart<R, S> {
//     // Queue of shuffled requests to be sent out.
//     outgoing_request_receiver: Receiver<Message<R>>,
// }

// pub struct TrustedShufflerBackendFacingPartPerRequest<R, S> {
//     // Map containing batches of responses to be received from the backend.
//     // Once a particular item receives all of the responses, they are being
//     // shuffled back to the clients.
//     response_promise_map: Arc<Mutex<HashMap<BatchId, (HashSet<RequestId>, Vec<Message<S>>)>>>,

//     // Queue of incoming batched responses to be shuffled.
//     incoming_response_sender: Sender<Vec<Message<S>>>,
// }
//------------------------------------------------------------------------------

// Trusted Shuffler inmpelentation.
// Generic parameter `R` represents a request type, and `S` a response type.
#[derive(Clone)]
pub struct TrustedShuffler<R, S>
where
    R: std::marker::Send,
    S: std::marker::Send,
{
    // Value k that represents k-anonymity.
    anonymity_value: usize,

    // Generator for creating unique IDs for incoming requests.
    request_id_generator: Arc<Mutex<RequestIdGenerator>>,

    // Map for sending responses back to the clients.
    request_promise_map: Arc<Mutex<HashMap<RequestId, oneshot::Sender<S>>>>,

    // Queue of incoming requests to be shuffled.
    incoming_request_queue: AsyncQueue<Message<R>>,

    // Queue of shuffled requests to be sent out.
    outgoing_request_queue: AsyncQueue<Message<R>>,

    // Map containing batches of responses to be received from the backend.
    // Once a particular item receives all of the responses, they are being
    // shuffled back to the clients.
    response_promise_map: Arc<Mutex<HashMap<BatchId, (HashSet<RequestId>, Vec<Message<S>>)>>>,

    // Queue of incoming batched responses to be shuffled.
    incoming_response_queue: AsyncQueue<Vec<Message<S>>>,
}

impl<R, S> TrustedShuffler<R, S>
where
    R: std::marker::Send,
    S: std::marker::Send,
{
    pub fn new(anonymity_value: usize) -> Self {
        Self {
            anonymity_value,
            request_id_generator: Arc::new(Mutex::new(RequestIdGenerator::new(anonymity_value))),
            request_promise_map: Arc::new(Mutex::new(HashMap::new())),
            incoming_request_queue: AsyncQueue::new(CHANNEL_BUFFER_SIZE),
            outgoing_request_queue: AsyncQueue::new(CHANNEL_BUFFER_SIZE),
            response_promise_map: Arc::new(Mutex::new(HashMap::new())),
            incoming_response_queue: AsyncQueue::new(CHANNEL_BUFFER_SIZE),
        }
    }

    // pub async fn generate(&mut self) {
    //     self.request_id_generator.lock().unwrap().generate();
    // }

    // Asynchronously handles incoming requests.
    pub async fn invoke(&self, request: R) -> anyhow::Result<S> {
        let request_id = self.request_id_generator.lock().unwrap().generate();
        let request = Message {
            id: request_id.clone(),
            data: request,
        };

        self.incoming_request_queue
            .put(request)
            .await
            .context("Couldn't put request in a queue")?;

        let (sender, receiver) = oneshot::channel();
        self.request_promise_map
            .lock()
            .unwrap()
            .insert(request_id, sender);

        receiver.await.context("Couldn't receive response")
    }

    // Returns a request from the shuffled queue to be sent to the backend.
    pub async fn pop_request(&mut self) -> anyhow::Result<(RequestId, R)> {
        let request = self
            .outgoing_request_queue
            .get()
            .await
            .context("Couldn't get request")?;
        Ok((request.id, request.data))
    }

    // Pushes a backend response through the Trusted Shuffler back to the client.
    // `request_id` should correspond to the original client request sent to the
    // backend.
    pub async fn push_response(
        &mut self,
        request_id: RequestId,
        response: S,
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
            self.incoming_response_queue
                .put(full_response_batch.drain(..).collect())
                .await
                .context("Couldn't put response in a queue")?;
            response_promise_map.remove(&request_id.batch_id);
        }

        Ok(())
    }

    pub async fn shuffle_forward(&mut self) -> anyhow::Result<()> {
        let mut current_batch = vec![];
        loop {
            let request = self
                .incoming_request_queue
                .get()
                .await
                .context("Couldn't get request from an incoming request queue")?;
            current_batch.push(request);

            if current_batch.len() >= self.anonymity_value {
                current_batch.shuffle(&mut thread_rng());
                for request in current_batch.drain(..) {
                    self.outgoing_request_queue
                        .put(request)
                        .await
                        .context("Couldn't put request to an outgoing request queue")?;
                }
                // TODO(): Populate the response promise map.
                assert!(current_batch.is_empty());
            }
        }
    }

    pub async fn shuffle_backward(batch_id: BatchId) {
        loop {}
    }
}
