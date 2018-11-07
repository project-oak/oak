extern crate wasm_bindgen;

use wasm_bindgen::prelude::*;

#[wasm_bindgen]
extern "C" {
    fn oak_print(s: &str);
    fn oak_get_time() -> u64;
}

pub fn print(s: &str) {
    oak_print(s)
}

pub fn get_time() -> std::time::SystemTime {
    let ns = oak_get_time();
    std::time::UNIX_EPOCH + std::time::Duration::from_nanos(ns)
}

pub struct OakReader {}

impl std::io::Read for OakReader {
    fn read(&mut self, buf: &mut [u8]) -> std::io::Result<usize> {
        Ok(0)
    }
}

pub fn get_input(n: u32) -> OakReader {
    OakReader {}
}

pub struct OakWriter {}

impl std::io::Write for OakWriter {
    fn write(&mut self, buf: &[u8]) -> std::io::Result<usize> {
        Ok(0)
    }
    fn flush(&mut self) -> std::io::Result<()> {
        Ok(())
    }
}

pub fn get_output(n: u32) -> OakWriter {
    OakWriter {}
}
