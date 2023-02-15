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

use crate::{AbiPointer, AbiPointerOffset, WasmHandler, WasmState};
use alloc::{borrow::ToOwned, vec};
use oak_functions_abi::{proto::OakStatus, ExtensionHandle, TestingRequest, TestingResponse};
use oak_functions_testing_extension::{TestingFactory, TestingLogger};

#[test]
fn test_invoke_extension_with_invalid_handle() {
    let mut wasm_state = create_test_wasm_state();
    // Assumes there is no negative ExtensionHandle. The remaining arguments don't matter, hence
    // they are 0.
    let extension = wasm_state.invoke_extension(-1, 0, 0, 0, 0);
    assert!(extension.is_err());
    assert_eq!(OakStatus::ErrInvalidHandle, extension.unwrap_err())
}

#[test]
fn test_find_extension_not_available() {
    let mut wasm_state = create_test_wasm_state();
    // Assumes we have no extension with a handle value of 5 in our test wasm_state. The remaining
    // arguments don't matter, hence they are 0.
    let extension = wasm_state.invoke_extension(5, 0, 0, 0, 0);
    assert!(extension.is_err());
    assert_eq!(OakStatus::ErrInvalidHandle, extension.unwrap_err())
}

#[test]
fn test_read_write_u32_in_wasm_memory() {
    let wasm_state = create_test_wasm_state();
    // Guess some memory address in linear Wasm memory to write to.
    let address: AbiPointer = 100;
    let value: u32 = 32;
    let write_status = wasm_state.write_u32_to_wasm_memory(value, address);
    assert!(write_status.is_ok());
    let read_value = wasm_state.read_u32_from_wasm_memory(address).unwrap();
    assert_eq!(read_value, value);
}

#[test]
fn test_alloc_and_write_empty() {
    let mut wasm_state = create_test_wasm_state();
    // Guess some memory addresses in linear Wasm memory to write to.
    let dest_ptr_ptr: AbiPointer = 100;
    let dest_len_ptr: AbiPointer = 150;
    let write_status =
        wasm_state.alloc_and_write_buffer_to_wasm_memory(vec![], dest_ptr_ptr, dest_len_ptr);

    // Assert that we can write the empty vector.
    assert!(write_status.is_ok());

    // Get dest_len from dest_len_ptr.
    let dest_len: AbiPointerOffset = wasm_state.read_u32_from_wasm_memory(dest_len_ptr).unwrap();

    // Assert that we write a vector of length 0.
    assert_eq!(dest_len, 0);

    let dest_ptr: AbiPointer = wasm_state.read_u32_from_wasm_memory(dest_ptr_ptr).unwrap();

    // Assert that reponse_ptr holds expected empty vector.
    assert!(wasm_state
        .read_buffer_from_wasm_memory(dest_ptr, dest_len)
        .unwrap()
        .is_empty());
}

#[test]
fn test_alloc_and_write() {
    let mut wasm_state = create_test_wasm_state();
    let bfr = vec![42];
    // Guess some memory addresses in linear Wasm memory to write to.
    let dest_ptr_ptr: AbiPointer = 100;
    let dest_len_ptr: AbiPointer = 150;
    let write_status =
        wasm_state.alloc_and_write_buffer_to_wasm_memory(bfr.clone(), dest_ptr_ptr, dest_len_ptr);
    assert!(write_status.is_ok());

    // Get dest_len from dest_len_ptr.
    let dest_len: AbiPointerOffset = wasm_state.read_u32_from_wasm_memory(dest_len_ptr).unwrap();

    // Assert that we write a vector of correct length.
    assert_eq!(dest_len, bfr.len() as u32);

    let dest_ptr: AbiPointer = wasm_state.read_u32_from_wasm_memory(dest_ptr_ptr).unwrap();

    // Assert that reponse_ptr holds expected empty vector.
    assert_eq!(
        wasm_state
            .read_buffer_from_wasm_memory(dest_ptr, dest_len)
            .unwrap(),
        bfr
    );
}

#[test]
fn test_write_read_buffer_in_wasm_memory() {
    let mut wasm_state = create_test_wasm_state();
    // Guess some memory addresses in linear Wasm memory to write to.
    let dest_ptr_ptr: AbiPointer = 100;
    let dest_len_ptr: AbiPointer = 150;
    let buffer = vec![42, 21];

    let write_status = wasm_state.alloc_and_write_buffer_to_wasm_memory(
        buffer.clone(),
        dest_ptr_ptr,
        dest_len_ptr,
    );
    assert!(write_status.is_ok());

    // Get dest_len from dest_len_ptr and dest_prt from dest_ptr_ptr.
    let dest_len: AbiPointerOffset = wasm_state.read_u32_from_wasm_memory(dest_len_ptr).unwrap();
    let dest_ptr: AbiPointer = wasm_state.read_u32_from_wasm_memory(dest_ptr_ptr).unwrap();

    let read_buffer = wasm_state
        .read_buffer_from_wasm_memory(dest_ptr, dest_len)
        .unwrap();
    assert_eq!(read_buffer, buffer);
}

#[test]
fn test_read_empty_buffer_in_wasm_memory() {
    let wasm_state = create_test_wasm_state();
    // Guess some memory addresses in linear Wasm memory to write to.
    let dest_len_ptr: AbiPointer = 150;
    let buffer: vec::Vec<u8> = vec![];

    wasm_state
        .write_u32_to_wasm_memory(dest_len_ptr, 0)
        .unwrap();

    // Get dest_len from dest_len_ptr.
    let dest_len: AbiPointerOffset = wasm_state.read_u32_from_wasm_memory(dest_len_ptr).unwrap();

    // If dest_len is 0, then dest_ptr is irrelevant, so we set it 0, too.
    let dest_ptr = 0;
    let read_buffer = wasm_state
        .read_buffer_from_wasm_memory(dest_ptr, dest_len)
        .unwrap();
    assert_eq!(read_buffer, buffer);
}

#[test]
fn test_invoke_extension() {
    let mut wasm_state = create_test_wasm_state();

    // Assumes we have a Testing extension in our test wasm_state.
    let message = "Hello!".to_owned();
    let request = bincode::serialize(&TestingRequest::Echo(message.clone()))
        .expect("couldn't serialize request");

    // Guess some memory addresses in linear Wasm memory to write the request to.
    let request_ptr: AbiPointer = 100;
    let result = wasm_state.write_buffer_to_wasm_memory(&request, request_ptr);
    assert!(result.is_ok());

    // Guess some memory addresses in linear Wasm memory to write the response to.
    let response_ptr_ptr: AbiPointer = 200;
    let response_len_ptr: AbiPointer = 250;

    let result = wasm_state.invoke_extension(
        ExtensionHandle::TestingHandle as i32,
        request_ptr,
        request.len() as u32,
        response_ptr_ptr,
        response_len_ptr,
    );
    assert!(result.is_ok());

    let expected_response =
        bincode::serialize(&TestingResponse::Echo(message)).expect("couldn't serialize response");

    // Get response_len from response_len_ptr.
    let response_len: AbiPointerOffset = wasm_state
        .read_u32_from_wasm_memory(response_len_ptr)
        .unwrap();

    // Assert that response_len holds length of expected response.
    assert_eq!(response_len as usize, expected_response.len());

    // Get response_ptr from response_ptr_ptr.
    let response_ptr: AbiPointer = wasm_state
        .read_u32_from_wasm_memory(response_ptr_ptr)
        .unwrap();

    // Assert that reponse_ptr holds expected response.
    assert_eq!(
        wasm_state
            .read_buffer_from_wasm_memory(response_ptr, response_len)
            .unwrap(),
        expected_response
    );
}

fn create_test_wasm_state() -> WasmState<TestingLogger> {
    let logger = TestingLogger::for_test();

    let testing_factory = TestingFactory::new_boxed_extension_factory(logger.clone())
        .expect("couldn't create TestingFactory");

    let wasm_module_path = oak_functions_test_utils::build_rust_crate_wasm("echo").unwrap();
    let wasm_module_bytes = std::fs::read(wasm_module_path).unwrap();

    let wasm_handler = WasmHandler::create(&wasm_module_bytes, vec![testing_factory], logger)
        .expect("couldn't create WasmHandler");
    wasm_handler
        .init_wasm_state(b"".to_vec())
        .expect("couldn't create WasmState")
}
