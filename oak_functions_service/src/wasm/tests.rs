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

extern crate test;

use alloc::{rc::Rc, sync::Arc, vec::Vec};
use core::cell::Cell;

use oak_functions_abi::Request;

use super::{
    ALLOC_FUNCTION_NAME, MEMORY_NAME, OakLinker, UserState, WasmApiFactory, WasmHandler,
    api::StdWasmApiFactory,
};
use crate::{
    Handler,
    logger::StandaloneLogger,
    lookup::LookupDataManager,
    wasm::{AbiPointer, AbiPointerOffset},
};

#[test]
fn test_read_write_u32_in_wasm_memory() {
    let mut test_state = create_test_state();
    // Guess some memory address in linear Wasm memory to write to.
    let address: AbiPointer = 100;
    let value: u32 = 32;
    write_u32(&mut test_state, value, address);
    let read_value = read_u32(&test_state, address);
    assert_eq!(read_value, value);
}

#[test]
fn test_alloc_and_write_empty() {
    let mut test_state = create_test_state();
    // Guess some memory addresses in linear Wasm memory to write to.
    let dest_ptr_ptr: AbiPointer = 100;
    let dest_len_ptr: AbiPointer = 150;
    alloc_and_write(&mut test_state, dest_ptr_ptr, dest_len_ptr, alloc::vec![]);
    // Get dest_len from dest_len_ptr.
    let dest_len: AbiPointerOffset = read_u32(&test_state, dest_len_ptr);
    // Assert that we write a vector of length 0.
    assert_eq!(dest_len, 0);
    let dest_ptr: AbiPointer = read_u32(&test_state, dest_ptr_ptr);
    // Reading the empty vector from response_ptr.
    let buf = read_buffer(&test_state, dest_ptr, dest_len);
    // Assert that reponse_ptr holds expected empty vector.
    assert!(buf.is_empty());
}

#[test]
fn test_alloc_and_write_buffer() {
    let mut test_state = create_test_state();
    let buffer = alloc::vec![42];
    // Guess some memory addresses in linear Wasm memory to write to.
    let dest_ptr_ptr: AbiPointer = 100;
    let dest_len_ptr: AbiPointer = 150;
    alloc_and_write(&mut test_state, dest_ptr_ptr, dest_len_ptr, buffer.clone());
    // Get dest_len from dest_len_ptr.
    let dest_len: AbiPointerOffset = read_u32(&test_state, dest_len_ptr);
    // Assert that we write a vector of correct length.
    assert_eq!(dest_len, buffer.len() as u32);
    let dest_ptr: AbiPointer = read_u32(&test_state, dest_ptr_ptr);
    // Assert that reponse_ptr holds expected empty vector.
    assert_eq!(read_buffer(&test_state, dest_ptr, dest_len), buffer);
}

#[test]
fn test_write_read_buffer_in_wasm_memory() {
    let mut test_state = create_test_state();
    // Guess some memory addresses in linear Wasm memory to write to.
    let dest_ptr_ptr: AbiPointer = 100;
    let dest_len_ptr: AbiPointer = 150;
    let buffer = alloc::vec![42, 21];
    alloc_and_write(&mut test_state, dest_ptr_ptr, dest_len_ptr, buffer.clone());
    // Get dest_len from dest_len_ptr and dest_prt from dest_ptr_ptr.
    let dest_len: AbiPointerOffset = read_u32(&test_state, dest_len_ptr);
    let dest_ptr: AbiPointer = read_u32(&test_state, dest_ptr_ptr);
    let read_buffer = read_buffer(&test_state, dest_ptr, dest_len);
    assert_eq!(read_buffer, buffer);
}

#[test]
fn test_read_empty_buffer_in_wasm_memory() {
    let mut test_state = create_test_state();
    // Guess some memory addresses in linear Wasm memory to write to.
    let dest_len_ptr: AbiPointer = 150;
    let buffer: Vec<u8> = alloc::vec![];
    write_u32(&mut test_state, dest_len_ptr, 0);
    // Get dest_len from dest_len_ptr.
    let dest_len: AbiPointerOffset = read_u32(&test_state, dest_len_ptr);
    // If dest_len is 0, then dest_ptr is irrelevant, so we set it 0, too.
    let dest_ptr = 0;
    let read_buffer = read_buffer(&test_state, dest_ptr, dest_len);
    assert_eq!(read_buffer, buffer);
}

#[test]
fn test_read_request() {
    let mut test_state = create_test_state();
    // Instead of calling read_request, we mimick the functionality here. This is
    // not pretty, but the best I can do for now.
    let request_bytes = test_state.request.clone();
    // Guess some memory addresses in linear Wasm memory to write to.
    let dest_ptr_ptr: AbiPointer = 100;
    let dest_len_ptr: AbiPointer = 150;
    alloc_and_write(&mut test_state, dest_ptr_ptr, dest_len_ptr, request_bytes);

    // Actually read the request back.
    let req_ptr = read_u32(&test_state, dest_ptr_ptr);
    let req_len = read_u32(&test_state, dest_len_ptr);
    let request_bytes = read_buffer(&test_state, req_ptr, req_len);

    assert_eq!(request_bytes, test_state.request.clone());
}

#[test]
fn test_invoke() {
    let test_state = create_test_state();
    let data = b"Hello, world!";
    let response = test_state.wasm_handler.handle_invoke(Request { body: data.to_vec() }).unwrap();
    assert_eq!(response.body, data.to_vec());
}

struct TestState {
    instance: wasmi::Instance,
    store: wasmi::Store<UserState>,
    wasm_handler: WasmHandler,
    request: Vec<u8>,
}

fn create_test_state() -> TestState {
    let logger = Arc::new(StandaloneLogger);
    let lookup_data_manager =
        Arc::new(LookupDataManager::<1>::for_test(Vec::default(), logger.clone()));
    let api_factory =
        Arc::new(StdWasmApiFactory { lookup_data_manager: lookup_data_manager.clone() });

    let wasm_module_path = "oak_functions/examples/echo/echo.wasm";

    let wasm_module_bytes = std::fs::read(wasm_module_path).unwrap();

    let wasm_handler =
        WasmHandler::create(&wasm_module_bytes, api_factory.clone(), logger.clone(), None)
            .expect("couldn't create WasmHandler");

    let request = Vec::new();
    let response = Rc::new(Cell::new(Vec::new()));
    let mut wasm_api = api_factory.create_wasm_api(request.clone(), response.clone());

    let user_state = UserState::new(wasm_api.transport(), logger.clone());

    let module = wasm_handler.wasm_module.clone();
    let mut store = wasmi::Store::new(module.engine(), user_state);
    let linker = OakLinker::new(module.engine());
    let instance =
        linker.instantiate(&mut store, module).expect("couldn't instantiate Wasm module");

    TestState { instance, store, wasm_handler, request: request.clone() }
}

// Read the u32 value at the `address` from the Wasm memory.
// Only needed in tests.
fn read_u32(test_state: &TestState, address: AbiPointer) -> u32 {
    let address = read_buffer(test_state, address, 4);
    u32::from_le_bytes(address.try_into().unwrap())
}

// Mirrors the implementation `read_buffer` with less error handling. I have
// found no other way to unit-test whether our use of the wasmi API is correct,
// as we cannot create a test `Caller`.
fn read_buffer(test_state: &TestState, buf_ptr: AbiPointer, buf_len: AbiPointerOffset) -> Vec<u8> {
    let mut buf = alloc::vec![0; buf_len as usize];
    let buf_ptr = buf_ptr.try_into().unwrap();
    let memory = test_state
        .instance
        .get_export(&test_state.store, MEMORY_NAME)
        .unwrap()
        .into_memory()
        .unwrap();

    memory.read(&test_state.store, buf_ptr, &mut buf).unwrap();
    buf
}

// Mirrors the implementation `alloc_and_write` with less error handling. I have
// found no other way to unit-test whether our use of the wasmi API is correct,
// as we cannot create a test `Caller`.
fn alloc_and_write(
    test_state: &mut TestState,
    buf_ptr_ptr: AbiPointer,
    buf_ptr_len: AbiPointer,
    buf: Vec<u8>,
) {
    let len = buf.len() as i32;

    let alloc = test_state
        .instance
        .get_export(&mut test_state.store, ALLOC_FUNCTION_NAME)
        .unwrap()
        .into_func()
        .unwrap()
        .typed(&test_state.store)
        .unwrap();

    let dest_ptr = alloc.call(&mut test_state.store, len).unwrap();

    write_buffer(test_state, &buf, dest_ptr);
    write_u32(test_state, dest_ptr, buf_ptr_ptr);
    write_u32(test_state, len as u32, buf_ptr_len)
}

// Mirrors the implementation `write_buffer` with less error handling. I have
// found no other way to unit-test whether our use of the wasmi API is correct,
// as we cannot create a test `Caller`.
fn write_buffer(test_state: &mut TestState, source: &[u8], dest: AbiPointer) {
    let dest =
        dest.try_into().expect("failed to convert AbiPointer to usize as required by wasmi API");

    // Get memory.
    let memory = test_state
        .instance
        .get_export(&test_state.store, MEMORY_NAME)
        .unwrap()
        .into_memory()
        .unwrap();

    memory.write(&mut test_state.store, dest, source).unwrap()
}

// Mirrors the implementation `write_u32` with less error handling. I have found
// no other way to unit-test whether our use of the wasmi API is correct, as we
// cannot create a test `Caller`.
fn write_u32(test_state: &mut TestState, value: u32, address: AbiPointer) {
    let value_bytes = value.to_le_bytes();
    write_buffer(test_state, &value_bytes, address);
}
