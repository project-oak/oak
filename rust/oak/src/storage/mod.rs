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

extern crate protobuf;

use crate::{GrpcResult, ReceiveChannelHalf, SendChannelHalf};
use proto::storage_channel::{
    StorageChannelDeleteRequest, StorageChannelReadRequest, StorageChannelRequest,
    StorageChannelResponse, StorageChannelWriteRequest,
};
use protobuf::Message;

fn execute_operation(operation_request: &StorageChannelRequest) -> StorageChannelResponse {
    info!(
        "StorageChannelRequest: {}",
        protobuf::text_format::print_to_string(operation_request)
    );

    // TODO: save channels and re-use them to prevent looking up again
    let mut storage_write_channel = SendChannelHalf::new(crate::channel_find("storage_out"));
    operation_request
        .write_to_writer(&mut storage_write_channel)
        .unwrap();

    // Block until there is a response available.
    let storage_in_handle = crate::channel_find("storage_in");
    let read_handles = vec![storage_in_handle];
    let mut space = crate::new_handle_space(&read_handles);
    crate::prep_handle_space(&mut space);
    unsafe {
        crate::wasm::wait_on_channels(space.as_mut_ptr(), read_handles.len() as u32);
    }

    let mut storage_read_channel = ReceiveChannelHalf::new(storage_in_handle);
    let mut buffer = Vec::<u8>::with_capacity(256);
    storage_read_channel.read_message(&mut buffer).unwrap();
    let response: StorageChannelResponse = protobuf::parse_from_reader(&mut &buffer[..]).unwrap();
    info!(
        "StorageChannelResponse: {}",
        protobuf::text_format::print_to_string(&response)
    );

    response
}

pub fn read(storage_name: &[u8], name: &[u8]) -> GrpcResult<Vec<u8>> {
    let mut read_request = StorageChannelReadRequest::new();
    read_request.datum_name = name.to_owned();

    let mut operation_request = StorageChannelRequest::new();
    operation_request.storage_name = storage_name.to_owned();
    operation_request.set_read_request(read_request);

    let mut operation_response = execute_operation(&operation_request);

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

pub fn write(storage_name: &[u8], name: &[u8], value: &[u8]) -> GrpcResult<()> {
    let mut write_request = StorageChannelWriteRequest::new();
    write_request.datum_name = name.to_owned();
    write_request.datum_value = value.to_owned();

    let mut operation_request = StorageChannelRequest::new();
    operation_request.storage_name = storage_name.to_owned();
    operation_request.set_write_request(write_request);

    let mut operation_response = execute_operation(&operation_request);
    let status = operation_response.take_status();
    if status.code != 0 {
        Err(status)
    } else {
        Ok(())
    }
}

pub fn delete(storage_name: &[u8], name: &[u8]) -> GrpcResult<()> {
    let mut delete_request = StorageChannelDeleteRequest::new();
    delete_request.datum_name = name.to_owned();

    let mut operation_request = StorageChannelRequest::new();
    operation_request.storage_name = storage_name.to_owned();
    operation_request.set_delete_request(delete_request);

    let mut operation_response = execute_operation(&operation_request);
    let status = operation_response.take_status();
    if status.code != 0 {
        Err(status)
    } else {
        Ok(())
    }
}
