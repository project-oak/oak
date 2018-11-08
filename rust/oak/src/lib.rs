extern crate wasm_bindgen;

use wasm_bindgen::prelude::*;

#[wasm_bindgen]
extern "C" {
    fn oak_print(s: &str);
    fn oak_get_time() -> u64;
    fn oak_read(id: u32, buf: &mut [u8]) -> usize;
    fn oak_write(id: u32, buf: &[u8]) -> usize;
}

pub fn print(s: &str) {
    oak_print(s)
}

pub fn get_time() -> std::time::SystemTime {
    let ns = oak_get_time();
    std::time::UNIX_EPOCH + std::time::Duration::from_nanos(ns)
}

pub struct OakReader {
    id: u32,
}

impl std::io::Read for OakReader {
    fn read(&mut self, buf: &mut [u8]) -> std::io::Result<usize> {
        Ok(oak_read(self.id, buf))
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
        Ok(oak_write(self.id, buf))
    }
    fn flush(&mut self) -> std::io::Result<()> {
        Ok(())
    }
}

pub fn get_output(id: u32) -> OakWriter {
    OakWriter { id: id }
}
