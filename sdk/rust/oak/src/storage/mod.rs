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

use crate::{
    grpc,
    proto::oak::storage::{
        StorageChannelDeleteRequest, StorageChannelReadRequest, StorageChannelWriteRequest,
        StorageItem, StorageServiceClient,
    },
};
use oak_abi::proto::oak::application::{
    node_configuration::ConfigType, NodeConfiguration, StorageProxyConfiguration,
};

/// Local representation of the connection to an external storage service.
pub struct Storage {
    client: StorageServiceClient,
}

impl Storage {
    /// Creates a [`Storage`] instance using the given configuration.
    pub fn new(config: &StorageProxyConfiguration) -> Option<Storage> {
        crate::grpc::client::Client::new(&NodeConfiguration {
            name: "storage".to_string(),
            config_type: Some(ConfigType::StorageConfig(config.clone())),
        })
        .map(|client| Storage {
            client: StorageServiceClient(client),
        })
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

        self.client
            .read(read_request)
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

        self.client.write(write_request).map(|_| ())
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

        self.client.delete(delete_request).map(|_| ())
    }
}
