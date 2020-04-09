//
// Copyright 2019 The Project Oak Authors
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

//! Helper library for accessing Oak storage services.

use crate::grpc;
use crate::proto::oak::storage::{
    StorageChannelDeleteRequest, StorageChannelDeleteResponse, StorageChannelReadRequest,
    StorageChannelReadResponse, StorageChannelWriteRequest, StorageChannelWriteResponse,
    StorageItem,
};
use log::info;

/// Default name for predefined Node config that corresponds to a storage
/// pseudo-Node.
pub const DEFAULT_CONFIG_NAME: &str = "storage";

/// Local representation of the connection to an external storage service.
pub struct Storage {
    client: crate::grpc::client::Client,
}

impl Storage {
    /// Create a default `Storage` instance assuming the default pre-defined
    /// name (`"storage"`) identifying storage Node config.
    pub fn default() -> Option<Storage> {
        Storage::new(DEFAULT_CONFIG_NAME)
    }

    /// Create a `Storage` instance using the given name identifying storage
    /// Node configuration.
    pub fn new(config: &str) -> Option<Storage> {
        crate::grpc::client::Client::new(config, "oak_main").map(|client| Storage { client })
    }

    fn execute_operation<Req, Res>(
        &mut self,
        grpc_method_name: &str,
        operation_request: Req,
    ) -> grpc::Result<Res>
    where
        Req: prost::Message,
        Res: prost::Message + Default,
    {
        info!("StorageChannelRequest: {:?}", operation_request);
        crate::grpc::invoke_grpc_method(
            grpc_method_name,
            &operation_request,
            None,
            &self.client.invocation_sender,
        )
    }

    /// Read the value associated with the given `name` from the storage
    /// instance identified by `name`.
    pub fn read(&mut self, storage_name: &[u8], name: &[u8]) -> grpc::Result<Vec<u8>> {
        let read_request = StorageChannelReadRequest {
            storage_name: storage_name.to_owned(),
            transaction_id: vec![],
            item: Some(StorageItem {
                name: name.to_owned(),
                value: vec![],
                label: None,
            }),
        };

        // TODO(#757): Automatically generate boilerplate from the proto
        // definition.
        self.execute_operation::<StorageChannelReadRequest, StorageChannelReadResponse>(
            "/oak.storage.StorageService/Read",
            read_request,
        )
        .map(|r| r.item.unwrap_or_default().value.to_vec())
    }

    /// Set the value associated with the given `name` from the storage instance
    /// identified by `name`.
    pub fn write(&mut self, storage_name: &[u8], name: &[u8], value: &[u8]) -> grpc::Result<()> {
        // TODO(#449): Set policy for item.
        let write_request = StorageChannelWriteRequest {
            storage_name: storage_name.to_owned(),
            transaction_id: vec![],
            item: Some(StorageItem {
                name: name.to_owned(),
                value: value.to_owned(),
                label: None,
            }),
        };

        // TODO(#757): Automatically generate boilerplate from the proto definition.
        self.execute_operation::<StorageChannelWriteRequest, StorageChannelWriteResponse>(
            "/oak.storage.StorageService/Write",
            write_request,
        )
        .map(|_| ())
    }

    /// Delete the value associated with the given `name` from the storage
    /// instance identified by `name`.
    pub fn delete(&mut self, storage_name: &[u8], name: &[u8]) -> grpc::Result<()> {
        let delete_request = StorageChannelDeleteRequest {
            storage_name: storage_name.to_owned(),
            transaction_id: vec![],
            item: Some(StorageItem {
                name: name.to_owned(),
                value: vec![],
                label: None,
            }),
        };

        // TODO(#757): Automatically generate boilerplate from the proto definition.
        self.execute_operation::<StorageChannelDeleteRequest, StorageChannelDeleteResponse>(
            "/oak.storage.StorageService/Delete",
            delete_request,
        )
        .map(|_| ())
    }
}
