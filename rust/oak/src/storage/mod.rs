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

use proto::storage::{
    DeleteRequest, ReadRequest, StorageOperationRequest, StorageOperationResponse, WriteRequest,
};

fn execute_operation(operation_request: &StorageOperationRequest) -> StorageOperationResponse {
    writeln!(
        logging_channel(),
        "StorageOperationRequest: {}",
        protobuf::text_format::print_to_string(operation_request)
    )
    .unwrap();

    let mut storage_write_channel = SendChannelHalf::new(STORAGE_WRITE_CHANNEL_HANDLE);
    operation_request
        .write_to_writer(&mut storage_write_channel)
        .unwrap();

    let mut storage_read_channel = ReceiveChannelHalf::new(STORAGE_READ_CHANNEL_HANDLE);
    let mut buffer = Vec::<u8>::with_capacity(256);
    storage_read_channel.read_message(&mut buffer).unwrap();
    let response: StorageOperationResponse = protobuf::parse_from_reader(&mut &buffer[..]).unwrap();
    writeln!(
        logging_channel(),
        "StorageOperationResponse: {}",
        protobuf::text_format::print_to_string(&response)
    )
    .unwrap();

    return response;
}

pub fn read(storage_name: &Vec<u8>, name: &Vec<u8>) -> Vec<u8> {
    let mut read_request = ReadRequest::new();
    read_request.name = name.clone();

    let mut operation_request = StorageOperationRequest::new();
    operation_request.storage_name = storage_name.clone();
    operation_request.set_read_request(read_request);

    let operation_response = execute_operation(&operation_request);

    return operation_response.get_read_response().get_value().to_vec();
}

pub fn write(storage_name: &Vec<u8>, name: &Vec<u8>, value: &Vec<u8>) {
    let mut write_request = WriteRequest::new();
    write_request.name = name.clone();
    write_request.value = value.clone();

    let mut operation_request = StorageOperationRequest::new();
    operation_request.storage_name = storage_name.clone();
    operation_request.set_write_request(write_request);

    execute_operation(&operation_request);
}

pub fn delete(storage_name: &Vec<u8>, name: &Vec<u8>) {
    let mut delete_request = DeleteRequest::new();
    delete_request.name = name.clone();

    let mut operation_request = StorageOperationRequest::new();
    operation_request.storage_name = storage_name.clone();
    operation_request.set_delete_request(delete_request);

    execute_operation(&operation_request);
}
