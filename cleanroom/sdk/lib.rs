// Copyright 2026 The Project Oak Authors
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

//! # Cleanroom SDK
//!
//! Ergonomic wrappers for writing WebAssembly modules that run inside
//! the [cleanroom](../README.md) sandboxed runner.
//!
//! This crate generates the WIT bindings for the `oak:cleanroom/ifc`
//! interface and re-exports them as idiomatic Rust functions.  Module
//! authors depend on this crate instead of calling `wit_bindgen`
//! directly.
//!
//! ## Usage
//!
//! ```ignore
//! use std::io;
//!
//! fn main() -> io::Result<()> {
//!     let secret = cleanroom_sdk::get_cell("api_key")
//!         .ok_or_else(|| io::Error::new(io::ErrorKind::NotFound, "missing cell"))?;
//!
//!     let redacted = format!("{}****", &secret[..4]);
//!
//!     cleanroom_sdk::declassify(&["secret_category"]);
//!     println!("{redacted}");
//!     Ok(())
//! }
//! ```

// Generate the WIT bindings once, here in the SDK crate.
wit_bindgen::generate!({
    path: "../../cleanroom/wit",
    world: "runner",
});

/// Reads a named cell from the host cell store.
///
/// If the cell exists, the module's computation label is
/// automatically tainted with the cell's IFC label.  Returns `None`
/// if the cell is not defined.
pub fn get_cell(name: &str) -> Option<String> {
    oak::cleanroom::ifc::get_cell(name)
}

/// Returns the current IFC label of the module's computation.
///
/// Each entry in the returned list is a category name (e.g.
/// `"secret_category"`).  An empty list means the computation is
/// public (fully declassified).
pub fn get_label() -> Vec<String> {
    oak::cleanroom::ifc::get_label()
}

/// Explicitly declassifies the given categories.
///
/// Returns `true` if the module has sufficient privilege to
/// declassify all requested categories.  On failure, the
/// computation label is unchanged.
///
/// Category names should match the labels defined in the policy
/// (e.g. `"secret_category"`, `"user_location"`).
pub fn declassify(categories: &[&str]) -> bool {
    let owned: Vec<String> = categories.iter().map(|s| s.to_string()).collect();
    oak::cleanroom::ifc::declassify(&owned)
}

/// Reads a file from the host filesystem using the custom ABI.
///
/// This does NOT use standard WASI filesystem calls.
pub fn read_file(path: &str) -> std::result::Result<Vec<u8>, String> {
    oak::cleanroom::fs::read_file(path)
}

/// Writes a file to the host filesystem using the custom ABI.
///
/// This does NOT use standard WASI filesystem calls.
pub fn write_file(path: &str, data: &[u8]) -> std::result::Result<(), String> {
    oak::cleanroom::fs::write_file(path, data)
}

/// Deletes a file from the host filesystem using the custom ABI.
///
/// This does NOT use standard WASI filesystem calls.
pub fn delete_file(path: &str) -> std::result::Result<(), String> {
    oak::cleanroom::fs::delete_file(path)
}

/// Lists directory contents on the host filesystem using the custom ABI.
///
/// This does NOT use standard WASI filesystem calls. Returns a list of file
/// names.
pub fn list_directory(path: &str) -> std::result::Result<Vec<String>, String> {
    oak::cleanroom::fs::list_directory(path)
}
