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

extern crate protobuf;

use crate::{GrpcResult, ReceiveChannelHalf, SendChannelHalf};
use proto::storage_channel::{
    StorageChannelDeleteRequest, StorageChannelReadRequest, StorageChannelRequest,
    StorageChannelResponse, StorageChannelWriteRequest,
};
use protobuf::Message;

/// Local representation of the connection to an external storage service.
pub struct Storage {
    write_channel: crate::SendChannelHalf,
    wait_space: Vec<u8>,
    read_channel: crate::ReceiveChannelHalf,
}

impl Default for Storage {
    /// Create a default `Storage` instance assuming the standard port names
    /// (`"storage_in"`, `"storage_out"`) for pre-defined channels for storage
    /// communication.
    fn default() -> Storage {
        Storage::new("storage_in", "storage_out")
    }
}

impl Storage {
    /// Create a `Storage` instance using the given port names for pre-defined
    /// channels for storage communication.
    pub fn new(in_port_name: &str, out_port_name: &str) -> Storage {
        let handle = crate::channel_find(in_port_name);
        let handles = vec![handle];
        Storage {
            write_channel: SendChannelHalf::new(crate::channel_find(out_port_name)),
            wait_space: crate::new_handle_space(&handles),
            read_channel: ReceiveChannelHalf::new(handle),
        }
    }

    fn execute_operation(
        &mut self,
        operation_request: &StorageChannelRequest,
    ) -> StorageChannelResponse {
        info!(
            "StorageChannelRequest: {}",
            protobuf::text_format::print_to_string(operation_request)
        );

        operation_request
            .write_to_writer(&mut self.write_channel)
            .unwrap();

        // Block until there is a response available.
        unsafe {
            crate::wasm::wait_on_channels(self.wait_space.as_mut_ptr(), 1);
        }

        let mut buffer = Vec::<u8>::with_capacity(256);
        let mut handles = Vec::<crate::Handle>::with_capacity(1);
        self.read_channel
            .read_message(&mut buffer, &mut handles)
            .unwrap();
        if !handles.is_empty() {
            panic!("unexpected handles received alongside storage request")
        }
        let response: StorageChannelResponse =
            protobuf::parse_from_reader(&mut &buffer[..]).unwrap();
        info!(
            "StorageChannelResponse: {}",
            protobuf::text_format::print_to_string(&response)
        );

        response
    }

    /// Read the value associated with the given `name` from the storage
    /// instance identified by `name`.
    pub fn read(&mut self, storage_name: &[u8], name: &[u8]) -> GrpcResult<Vec<u8>> {
        let mut read_request = StorageChannelReadRequest::new();
        read_request.datum_name = name.to_owned();

        let mut operation_request = StorageChannelRequest::new();
        operation_request.storage_name = storage_name.to_owned();
        operation_request.set_read_request(read_request);

        let mut operation_response = self.execute_operation(&operation_request);

        let status = operation_response.take_status();
        if status.code != 0 {
            Err(status)
        } else {
            Ok(operation_response
                .get_read_response()
                .get_datum_value()
                .to_vec())
        }
    }

    /// Set the value associated with the given `name` from the storage instance
    /// identified by `name`.
    pub fn write(&mut self, storage_name: &[u8], name: &[u8], value: &[u8]) -> GrpcResult<()> {
        let mut write_request = StorageChannelWriteRequest::new();
        write_request.datum_name = name.to_owned();
        write_request.datum_value = value.to_owned();

        let mut operation_request = StorageChannelRequest::new();
        operation_request.storage_name = storage_name.to_owned();
        operation_request.set_write_request(write_request);

        let mut operation_response = self.execute_operation(&operation_request);
        let status = operation_response.take_status();
        if status.code != 0 {
            Err(status)
        } else {
            Ok(())
        }
    }

    /// Delete the value associated with the given `name` from the storage
    /// instance identified by `name`.
    pub fn delete(&mut self, storage_name: &[u8], name: &[u8]) -> GrpcResult<()> {
        let mut delete_request = StorageChannelDeleteRequest::new();
        delete_request.datum_name = name.to_owned();

        let mut operation_request = StorageChannelRequest::new();
        operation_request.storage_name = storage_name.to_owned();
        operation_request.set_delete_request(delete_request);

        let mut operation_response = self.execute_operation(&operation_request);
        let status = operation_response.take_status();
        if status.code != 0 {
            Err(status)
        } else {
            Ok(())
        }
    }
}
