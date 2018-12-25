//
// Copyright 2018 The Project Oak Authors
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

// See https://rustwasm.github.io/book/reference/js-ffi.html
#[link(wasm_import_module = "oak")]
extern "system" {
    fn oak_print(s: &str);
    fn oak_get_time() -> u64;
    fn oak_read(id: u32, buf: &mut [u8]) -> usize;
    fn oak_write(id: u32, buf: &[u8]) -> usize;
}

pub fn print(s: &str) {
    unsafe { oak_print(s) }
}

pub fn get_time() -> std::time::SystemTime {
    let ns = unsafe { oak_get_time() };
    std::time::UNIX_EPOCH + std::time::Duration::from_nanos(ns)
}

pub struct OakReader {
    id: u32,
}

impl std::io::Read for OakReader {
    fn read(&mut self, buf: &mut [u8]) -> std::io::Result<usize> {
        Ok(unsafe { oak_read(self.id, buf) })
    }
}

pub fn get_input(id: u32) -> OakReader {
    OakReader { id: id }
}

pub struct OakWriter {
    id: u32,
}

impl std::io::Write for OakWriter {
    fn write(&mut self, buf: &[u8]) -> std::io::Result<usize> {
        Ok(unsafe { oak_write(self.id, buf) })
    }
    fn flush(&mut self) -> std::io::Result<()> {
        Ok(())
    }
}

pub fn get_output(id: u32) -> OakWriter {
    OakWriter { id: id }
}
