//
// Copyright 2020 The Project Oak Authors
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
//! Example module showcasing handle passing inside of Protocol Buffers.
//!
//! The following diagram illustrates how the system stores client blobs:
//!
//! ```text
//!                     Client
//!                       /\               (1) \/ PutBlob request
//!                       ||                            (7) /\ BlobResponse (from (6))
//!                       \/
//!                  gRPC service
//!                       /\
//!                       ||  Proxies messages to and from the frontend
//!                       \/
//!        BlobStore frontend
//!         /\            /\               (2) \/ Request a BlobStoreInterface
//!         ||            ||                    (4) /\ Return BlobStoreInterface to frontend
//!         ||            \/
//!         ||     BlobStore provider
//!         ||      |
//!         ||      |                      (3) Start a new BlobStore impl
//!         ||      |
//!         ||      |                           (5) \/ PutBlob request (from (1))
//!         ||      |                                   (6) /\ BlobResponse
//!         \/      |
//!        BlobStore impl
//! ```
//!
//! Note that this will only ever create one BlobStore impl, as the handles to the store are
//! cached by the frontend. Subsequent requests to store or receive blobs are forwarded to the
//! existing BlobStore by the BlobStore frontend:
//!
//! ```text
//!                     Client
//!                       /\               (1) \/ GetBlob request
//!                       ||                    (4) /\ BlobResponse (from (3))
//!                       \/
//!                  gRPC service
//!                       /\
//!                       ||  Proxies messages to and from the frontend
//!                       \/
//!              BlobStore frontend
//!                       /\
//!                       ||               (2) \/ GetBlob request (from (1))
//!                       \/                    (3) /\ BlobResponse
//!                BlobStore impl
//! ```

mod proto {
    include!(concat!(env!("OUT_DIR"), "/oak.examples.injection.rs"));
}

use oak::{
    grpc,
    io::{ReceiverExt, SenderExt},
};
use oak_io::{Receiver, Sender};
use proto::{
    blob_request::Request, BlobRequest, BlobResponse, BlobStore, BlobStoreDispatcher,
    BlobStoreInterface, BlobStoreProviderSender, BlobStoreRequest, BlobStoreSender, GetBlobRequest,
    PutBlobRequest,
};

oak::entrypoint!(grpc_fe => |_in_channel| {
    oak::logger::init_default();
    let (to_provider_write_handle, to_provider_read_handle) = oak::channel_create().unwrap();
    let (from_provider_write_handle, from_provider_read_handle) = oak::channel_create().unwrap();

    oak::node_create(&oak::node_config::wasm("app", "provider"), to_provider_read_handle)
        .expect("Failed to create provider");
    oak::channel_close(to_provider_read_handle.handle).expect("Failed to close channel");

    Sender::new(to_provider_write_handle)
        .send(&BlobStoreProviderSender { sender: Some(Sender::new(from_provider_write_handle)) })
        .expect("Failed to send handle to provider");
    oak::channel_close(from_provider_write_handle.handle).expect("Failed to close channel");

    let frontend = BlobStoreFrontend::new(
            Sender::new(to_provider_write_handle),
            Receiver::new(from_provider_read_handle));
    let dispatcher = BlobStoreDispatcher::new(frontend);
    let grpc_channel = oak::grpc::server::init("[::]:8080")
        .expect("could not create gRPC server pseudo-Node");

    oak::run_event_loop(dispatcher, grpc_channel);
});

oak::entrypoint!(provider => |frontend_read| {
    oak::logger::init_default();
    let frontend_sender =
        Receiver::<BlobStoreProviderSender>::new(frontend_read).receive()
            .expect("Did not receive a decodable message")
            .sender
            .expect("No sender in received message");
    oak::run_event_loop(BlobStoreProvider::new(frontend_sender),
        Receiver::<BlobStoreRequest>::new(frontend_read));
});

oak::entrypoint!(store => |reader| {
    oak::logger::init_default();
    let sender =
        Receiver::<BlobStoreSender>::new(reader).receive()
            .expect("Did not receive a write handle")
            .sender
            .expect("No write handle in received message");
    oak::run_event_loop(BlobStoreImpl::new(sender),
        Receiver::<BlobRequest>::new(reader));
});

enum BlobStoreAccess {
    BlobStoreProvider {
        sender: Sender<BlobStoreRequest>,
        receiver: Receiver<BlobStoreInterface>,
    },
    BlobStore(BlobStoreInterface),
}

struct BlobStoreFrontend {
    store: BlobStoreAccess,
}

impl BlobStoreFrontend {
    pub fn new(
        sender: Sender<BlobStoreRequest>,
        receiver: Receiver<BlobStoreInterface>,
    ) -> BlobStoreFrontend {
        BlobStoreFrontend {
            store: BlobStoreAccess::BlobStoreProvider { sender, receiver },
        }
    }

    fn get_interface(&mut self) -> &BlobStoreInterface {
        // Make sure it is cached
        if let BlobStoreAccess::BlobStoreProvider { sender, receiver } = &self.store {
            sender
                .send(&BlobStoreRequest {})
                .expect("Failed to send BlobStoreRequest");
            sender.close().expect("Failed to close sender");

            let iface = receiver
                .receive()
                .expect("Failed to receive BlobStoreInterface");
            receiver.close().expect("Failed to close receiver");

            self.store = BlobStoreAccess::BlobStore(iface);
        };

        match &self.store {
            BlobStoreAccess::BlobStore(iface) => &iface,
            _ => unreachable!(),
        }
    }

    fn send(&mut self, request: &BlobRequest) -> BlobResponse {
        let iface = self.get_interface();
        iface
            .sender
            .as_ref()
            .expect("No sender present on interface")
            .send(request)
            .expect("Could not send request");
        iface
            .receiver
            .as_ref()
            .expect("No receiver present on interface")
            .receive()
            .expect("Could not receive response")
    }
}

impl BlobStore for BlobStoreFrontend {
    fn get_blob(&mut self, request: GetBlobRequest) -> grpc::Result<BlobResponse> {
        Ok(self.send(&BlobRequest {
            request: Some(Request::Get(request)),
        }))
    }

    fn put_blob(&mut self, request: PutBlobRequest) -> grpc::Result<BlobResponse> {
        Ok(self.send(&BlobRequest {
            request: Some(Request::Put(request)),
        }))
    }
}

struct BlobStoreProvider {
    sender: Sender<BlobStoreInterface>,
}

impl BlobStoreProvider {
    pub fn new(sender: Sender<BlobStoreInterface>) -> BlobStoreProvider {
        BlobStoreProvider { sender }
    }
}

impl oak::Node<BlobStoreRequest> for BlobStoreProvider {
    fn handle_command(&mut self, _command: BlobStoreRequest) -> Result<(), oak::OakError> {
        // Create new BlobStore
        let (to_store_write_handle, to_store_read_handle) = oak::channel_create().unwrap();
        let (from_store_write_handle, from_store_read_handle) = oak::channel_create().unwrap();
        oak::node_create(
            &oak::node_config::wasm("app", "store"),
            to_store_read_handle,
        )?;
        oak::channel_close(to_store_read_handle.handle).expect("Failed to close channel");

        Sender::new(to_store_write_handle).send(&BlobStoreSender {
            sender: Some(Sender::new(from_store_write_handle)),
        })?;
        oak::channel_close(from_store_write_handle.handle).expect("Failed to close channel");

        self.sender.send(&BlobStoreInterface {
            sender: Some(Sender::new(to_store_write_handle)),
            receiver: Some(Receiver::new(from_store_read_handle)),
        })
    }
}

struct BlobStoreImpl {
    sender: Sender<BlobResponse>,
    blobs: Vec<Vec<u8>>,
}

impl BlobStoreImpl {
    pub fn new(sender: Sender<BlobResponse>) -> BlobStoreImpl {
        BlobStoreImpl {
            sender,
            blobs: Vec::new(),
        }
    }

    fn get_blob(&mut self, request: GetBlobRequest) -> BlobResponse {
        self.blobs
            .get(blob_index(request.id))
            .map(|blob| BlobResponse {
                blob: blob.clone(),
                id: request.id,
            })
            // Return the default instance if the blob was not found.
            .unwrap_or_default()
    }

    fn put_blob(&mut self, request: PutBlobRequest) -> BlobResponse {
        if request.id == 0 {
            // Insert a new blob
            self.blobs.push(request.blob.clone());
            BlobResponse {
                id: self.blobs.len() as u64,
                blob: request.blob,
            }
        } else if let Some(blob) = self.blobs.get_mut(blob_index(request.id)) {
            *blob = request.blob.clone();
            BlobResponse {
                id: request.id,
                blob: request.blob,
            }
        } else {
            BlobResponse::default()
        }
    }
}

fn blob_index(id: u64) -> usize {
    (id - 1) as usize
}

impl oak::Node<BlobRequest> for BlobStoreImpl {
    fn handle_command(&mut self, request: BlobRequest) -> Result<(), oak::OakError> {
        let response = match request.request {
            Some(Request::Get(req)) => self.get_blob(req),
            Some(Request::Put(req)) => self.put_blob(req),
            None => panic!("No inner request"),
        };
        self.sender.send(&response)
    }
}
