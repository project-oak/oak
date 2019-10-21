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

use crate::grpc;
use crate::{ReadHandle, WriteHandle};
use proto::grpc_encap::{GrpcRequest, GrpcResponse};
use proto::storage_channel::{
    StorageChannelDeleteRequest, StorageChannelDeleteResponse, StorageChannelReadRequest,
    StorageChannelReadResponse, StorageChannelWriteRequest, StorageChannelWriteResponse,
};
use protobuf::Message;

/// Local representation of the connection to an external storage service.
pub struct Storage {
    write_channel: crate::io::Channel,
    wait_space: Vec<u8>,
    read_channel: crate::ReadHandle,
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
        let read_handle = ReadHandle {
            handle: crate::channel_find(in_port_name),
        };
        let write_handle = WriteHandle {
            handle: crate::channel_find(out_port_name),
        };
        let handles = vec![read_handle];
        Storage {
            write_channel: crate::io::Channel::new(write_handle),
            wait_space: crate::new_handle_space(&handles),
            read_channel: read_handle,
        }
    }

    fn execute_operation<Req, Res>(
        &mut self,
        grpc_method_name: &str,
        operation_request: &Req,
    ) -> grpc::Result<Res>
    where
        Req: protobuf::Message,
        Res: protobuf::Message,
    {
        info!(
            "StorageChannelRequest: {}",
            protobuf::text_format::print_to_string(operation_request)
        );

        let mut request_any = protobuf::well_known_types::Any::new();
        operation_request
            .write_to_writer(&mut request_any.value)
            .unwrap();
        let mut grpc_request = GrpcRequest::new();
        grpc_request.method_name = grpc_method_name.to_owned();
        grpc_request.set_req_msg(request_any);

        grpc_request
            .write_to_writer(&mut self.write_channel)
            .unwrap();

        // Block until there is a response available.
        unsafe {
            crate::wasm::wait_on_channels(self.wait_space.as_mut_ptr(), 1);
        }

        let mut buffer = Vec::<u8>::with_capacity(256);
        let mut handles = Vec::<crate::Handle>::with_capacity(1);
        crate::channel_read(self.read_channel, &mut buffer, &mut handles);
        if !handles.is_empty() {
            panic!("unexpected handles received alongside storage request")
        }
        let mut grpc_response: GrpcResponse =
            protobuf::parse_from_reader(&mut &buffer[..]).unwrap();
        info!(
            "StorageChannelResponse: {}",
            protobuf::text_format::print_to_string(&grpc_response)
        );

        let status = grpc_response.take_status();
        if status.code != 0 {
            Err(status)
        } else {
            let response =
                protobuf::parse_from_bytes(grpc_response.get_rsp_msg().value.as_slice()).unwrap();
            Ok(response)
        }
    }

    /// Read the value associated with the given `name` from the storage
    /// instance identified by `name`.
    pub fn read(&mut self, storage_name: &[u8], name: &[u8]) -> grpc::Result<Vec<u8>> {
        let mut read_request = StorageChannelReadRequest::new();
        read_request.storage_name = storage_name.to_owned();
        read_request.datum_name = name.to_owned();

        // TODO: Automatically generate boilerplate from the proto definition.
        self.execute_operation::<StorageChannelReadRequest, StorageChannelReadResponse>(
            "/oak.StorageNode/Read",
            &read_request,
        )
        .map(|r| r.get_datum_value().to_vec())
    }

    /// Set the value associated with the given `name` from the storage instance
    /// identified by `name`.
    pub fn write(&mut self, storage_name: &[u8], name: &[u8], value: &[u8]) -> grpc::Result<()> {
        let mut write_request = StorageChannelWriteRequest::new();
        write_request.storage_name = storage_name.to_owned();
        write_request.datum_name = name.to_owned();
        write_request.datum_value = value.to_owned();

        // TODO: Automatically generate boilerplate from the proto definition.
        self.execute_operation::<StorageChannelWriteRequest, StorageChannelWriteResponse>(
            "/oak.StorageNode/Write",
            &write_request,
        )
        .map(|_| ())
    }

    /// Delete the value associated with the given `name` from the storage
    /// instance identified by `name`.
    pub fn delete(&mut self, storage_name: &[u8], name: &[u8]) -> grpc::Result<()> {
        let mut delete_request = StorageChannelDeleteRequest::new();
        delete_request.storage_name = storage_name.to_owned();
        delete_request.datum_name = name.to_owned();

        // TODO: Automatically generate boilerplate from the proto definition.
        self.execute_operation::<StorageChannelDeleteRequest, StorageChannelDeleteResponse>(
            "/oak.StorageNode/Delete",
            &delete_request,
        )
        .map(|_| ())
    }
}
