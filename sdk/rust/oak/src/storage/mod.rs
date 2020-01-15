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
use crate::proto::grpc_encap::{GrpcRequest, GrpcResponse};
use crate::proto::storage_channel::{
    StorageChannelDeleteRequest, StorageChannelDeleteResponse, StorageChannelReadRequest,
    StorageChannelReadResponse, StorageChannelWriteRequest, StorageChannelWriteResponse,
};
use log::{info, warn};
use protobuf::{Message, ProtobufEnum};

/// Default name for predefined node config that corresponds to a storage
/// pseudo-Node.
pub const DEFAULT_CONFIG_NAME: &str = "storage";

/// Local representation of the connection to an external storage service.
pub struct Storage {
    write_channel: crate::WriteHandle,
}

impl Storage {
    /// Create a default `Storage` instance assuming the default pre-defined
    /// name (`"storage"`) identifying storage node config.
    pub fn default() -> Option<Storage> {
        Storage::new(DEFAULT_CONFIG_NAME)
    }

    /// Create a `Storage` instance using the given name identifying storage
    /// node configuration.
    pub fn new(config: &str) -> Option<Storage> {
        // Create a channel and pass the read half to a fresh storage Node.
        let (write_channel, read_channel) = match crate::channel_create() {
            Ok(x) => x,
            Err(_e) => return None,
        };
        if crate::node_create(config, read_channel).is_err() {
            if let Err(status) = crate::channel_close(write_channel.handle) {
                warn!("could not close write channel: {:?}", status);
            };
            if let Err(status) = crate::channel_close(read_channel.handle) {
                warn!("could not close read channel: {:?}", status);
            };
            return None;
        }

        if let Err(status) = crate::channel_close(read_channel.handle) {
            warn!("could not close read channel: {:?}", status);
        };
        Some(Storage { write_channel })
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
        // TODO: rust-protobuf does not provide pack_from/unpack_to functions.
        // https://github.com/stepancheg/rust-protobuf/issues/455
        request_any.set_type_url(
            String::from("type.googleapis.com/") + operation_request.descriptor().full_name(),
        );
        operation_request
            .write_to_writer(&mut request_any.value)
            .expect("could not convert operation request to `Any` value");
        let mut grpc_request = GrpcRequest::new();
        grpc_request.method_name = grpc_method_name.to_owned();
        grpc_request.set_req_msg(request_any);
        let mut grpc_data = Vec::new();
        grpc_request
            .write_to_writer(&mut grpc_data)
            .expect("could not convert gRPC request to bytes");

        // Create an ephemeral channel for the response.
        let (rsp_out, rsp_in) = match crate::channel_create() {
            Ok(x) => x,
            Err(status) => {
                return Err(grpc::build_status(
                    grpc::Code::INTERNAL,
                    &format!(
                        "failed to create storage response channel: {}",
                        status.value()
                    ),
                ));
            }
        };

        crate::channel_write(self.write_channel, &grpc_data, &[rsp_out.handle])
            .expect("could not write to channel");
        crate::channel_close(rsp_out.handle).expect("could not close channel");

        // Block until there is a response available.
        loop {
            let wait_result = crate::wait_on_channels(&[rsp_in]).unwrap();
            if wait_result[0] == crate::ChannelReadStatus::READ_READY {
                break;
            }
        }

        let mut buffer = Vec::<u8>::with_capacity(256);
        let mut handles = Vec::<crate::Handle>::with_capacity(1);
        if crate::channel_read(rsp_in, &mut buffer, &mut handles)
            .expect("could not read from channel")
            != crate::ChannelStatus::Ready
        {
            panic!("empty message received");
        }
        if !handles.is_empty() {
            panic!("unexpected handles received alongside storage request")
        }
        let mut grpc_response: GrpcResponse = protobuf::parse_from_reader(&mut &buffer[..])
            .expect("could not parse gRPC response from bytes");
        info!(
            "StorageChannelResponse: {}",
            protobuf::text_format::print_to_string(&grpc_response)
        );
        crate::channel_close(rsp_in.handle).expect("could not close channel");

        let status = grpc_response.take_status();
        if status.code != 0 {
            Err(status)
        } else {
            let response = protobuf::parse_from_bytes(grpc_response.get_rsp_msg().value.as_slice())
                .expect("could not parse gRPC response message from `Any` value");
            Ok(response)
        }
    }

    /// Read the value associated with the given `name` from the storage
    /// instance identified by `name`.
    pub fn read(&mut self, storage_name: &[u8], name: &[u8]) -> grpc::Result<Vec<u8>> {
        let mut read_request = StorageChannelReadRequest::new();
        read_request.storage_name = storage_name.to_owned();
        read_request.mut_item().set_name(name.to_owned());

        // TODO: Automatically generate boilerplate from the proto definition.
        self.execute_operation::<StorageChannelReadRequest, StorageChannelReadResponse>(
            "/oak.StorageNode/Read",
            &read_request,
        )
        .map(|r| r.get_item().get_value().to_vec())
    }

    /// Set the value associated with the given `name` from the storage instance
    /// identified by `name`.
    pub fn write(&mut self, storage_name: &[u8], name: &[u8], value: &[u8]) -> grpc::Result<()> {
        let mut write_request = StorageChannelWriteRequest::new();
        // TODO: Set policy for item.
        write_request.storage_name = storage_name.to_owned();
        write_request.mut_item().set_name(name.to_owned());
        write_request.mut_item().set_value(value.to_owned());

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
        delete_request.mut_item().set_name(name.to_owned());

        // TODO: Automatically generate boilerplate from the proto definition.
        self.execute_operation::<StorageChannelDeleteRequest, StorageChannelDeleteResponse>(
            "/oak.StorageNode/Delete",
            &delete_request,
        )
        .map(|_| ())
    }
}
