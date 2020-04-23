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

use super::*;
use crate::RuntimeProxy;
use std::collections::HashMap;
use wat::{parse_file, parse_str};

fn start_node<S: AsRef<[u8]>>(buffer: S, entrypoint: &str) -> Result<(), OakStatus> {
    let mut configuration = crate::runtime::Configuration {
        nodes: HashMap::new(),
        entry_module: "test_module".to_string(),
        entrypoint: entrypoint.to_string(),
    };
    let module = wasmi::Module::from_buffer(buffer).unwrap();
    configuration.nodes.insert(
        "test_module".to_string(),
        crate::node::Configuration::WasmNode {
            module: Arc::new(module),
        },
    );
    let proxy = RuntimeProxy::create_runtime(configuration);
    let (_write_handle, read_handle) = proxy.channel_create(&Label::public_trusted());

    let result = proxy.node_create(
        "test_module",
        entrypoint,
        &oak_abi::label::Label::public_trusted(),
        read_handle,
    );
    proxy
        .channel_close(read_handle)
        .expect("could not close channel");

    // Ensure that the runtime can terminate correctly, regardless of what the node does.
    proxy.stop_runtime();

    result
}

#[test]
fn wasm_starting_module_without_content_fails() {
    // Loads an empty module that does not have the necessary entry point, so it should fail
    // immediately.
    let binary = parse_file("../../testdata/empty.wat").unwrap();

    // An empty module is equivalent to: [0x00, 0x61, 0x73, 0x6d, 0x01, 0x00, 0x00, 0x00]
    // From https://docs.rs/wasmi/0.6.2/wasmi/struct.Module.html#method.from_buffer:
    // Minimal module:
    // \0asm - magic
    // 0x01 - version (in little-endian)
    assert_eq!(binary, vec![0x00, 0x61, 0x73, 0x6d, 0x01, 0x00, 0x00, 0x00]);
    let result = start_node(binary, "oak_main");
    assert_eq!(Some(OakStatus::ErrInvalidArgs), result.err());
}

#[test]
fn wasm_starting_minimal_module_succeeds() {
    let binary = parse_file("../../testdata/minimal.wat").unwrap();
    let result = start_node(binary, "oak_main");
    assert_eq!(true, result.is_ok());
}

#[test]
fn wasm_starting_module_missing_an_export_fails() {
    let binary = parse_file("../../testdata/missing.wat").unwrap();
    let result = start_node(binary, "oak_main");
    assert_eq!(Some(OakStatus::ErrInvalidArgs), result.err());
}

#[test]
fn wasm_starting_module_with_wrong_export_fails() {
    let binary = parse_file("../../testdata/minimal.wat").unwrap();
    let result = start_node(binary, "oak_other_main");
    assert_eq!(Some(OakStatus::ErrInvalidArgs), result.err());
}

#[test]
fn wasm_starting_module_with_wrong_signature_fails() {
    let binary = parse_file("../../testdata/wrong.wat").unwrap();
    let result = start_node(binary, "oak_main");
    assert_eq!(Some(OakStatus::ErrInvalidArgs), result.err());
}

#[test]
fn wasm_starting_module_with_wrong_signature_2_fails() {
    // As a source of inspiration for writing tests in future, this test intentionally parses
    // the module from a string literal as opposed to loading from file.

    // Wrong signature: oak_main does not take any parameters
    let wat = r#"
    (module
        (func $oak_main)
        (memory (;0;) 18)
        (export "memory" (memory 0))
        (export "oak_main" (func $oak_main)))
    "#;
    let binary = parse_str(wat).unwrap();
    let result = start_node(binary, "oak_main");
    assert_eq!(Some(OakStatus::ErrInvalidArgs), result.err());
}

#[test]
fn wasm_starting_module_with_wrong_signature_3_fails() {
    // Wrong signature: oak_main has the correct input parameter, but returns i32
    let wat = r#"
    (module
        (type (;0;) (func (param i64) (result i32)))
        (func $oak_main (type 0)
          i32.const 42)
        (memory (;0;) 18)
        (export "memory" (memory 0))
        (export "oak_main" (func $oak_main)))
    "#;
    let binary = parse_str(wat).unwrap();
    let result = start_node(binary, "oak_main");
    assert_eq!(Some(OakStatus::ErrInvalidArgs), result.err());
}
