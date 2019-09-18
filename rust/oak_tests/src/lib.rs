extern crate protobuf;

use oak::proto::oak_api::OakStatus;
use protobuf::ProtobufEnum;
use std::cell::RefCell;
use std::collections::VecDeque;

#[cfg(test)]
mod tests;

struct MockChannel {
    /// If read_status is set, this status value will be returned for any read
    /// operations on the mock channel (and |messages| will be left
    /// undisturbed).
    pub read_status: Option<i32>,
    /// If write_status is set, this status value will be returned for any write
    /// operations on the mock channel (and |messages| will be left
    /// undisturbed).
    pub write_status: Option<i32>,
    /// Pending messages on the channel
    pub messages: VecDeque<Vec<u8>>,
}

impl MockChannel {
    fn new() -> MockChannel {
        MockChannel {
            read_status: None,
            write_status: None,
            messages: VecDeque::new(),
        }
    }
    fn write_message(&mut self, buf: *const u8, size: usize) -> i32 {
        if let Some(status) = self.write_status {
            return status;
        }
        let mut msg = Vec::with_capacity(size);
        unsafe {
            std::ptr::copy_nonoverlapping(buf, msg.as_mut_ptr(), size);
            msg.set_len(size);
        }
        self.messages.push_back(msg);
        OakStatus::OK.value()
    }
    fn read_message(&mut self, buf: *mut u8, size: usize, actual_size: *mut u32) -> i32 {
        if let Some(status) = self.read_status {
            return status;
        }
        let msg = self.messages.pop_front();
        if msg.is_none() {
            unsafe { *actual_size = 0 }
            return OakStatus::OK.value();
        }
        let msg = msg.unwrap();

        let len = msg.len();
        unsafe { *actual_size = len as u32 }
        if len > size {
            self.messages.push_front(msg);
            return OakStatus::ERR_BUFFER_TOO_SMALL.value();
        }
        unsafe {
            std::ptr::copy_nonoverlapping(msg.as_ptr(), buf, len);
        }
        OakStatus::OK.value()
    }
}

// Test-only mock channel which is used to service any calls to channel_read
// or channel_write, regardless of channel handle.
thread_local! {
    static CHANNEL: RefCell<MockChannel> = RefCell::new(MockChannel::new());
}

// Implementations of the Oak API host functions in Rust for testing.
#[no_mangle]
pub unsafe extern "C" fn wait_on_channels(buf: *mut u8, count: u32) -> i32 {
    // Pretend all channels are readable.
    for i in 0..(count as usize) {
        let p = buf.add(i * oak::SPACE_BYTES_PER_HANDLE + (oak::SPACE_BYTES_PER_HANDLE - 1));
        *p = 1;
    }
    OakStatus::OK.value()
}

#[no_mangle]
pub extern "C" fn channel_write(
    _handle: u64,
    buf: *const u8,
    size: usize,
    _handle_buf: *const u8,
    _handle_count: usize,
) -> i32 {
    CHANNEL.with(|channel| channel.borrow_mut().write_message(buf, size))
}

#[no_mangle]
pub extern "C" fn channel_read(
    _handle: u64,
    buf: *mut u8,
    size: usize,
    actual_size: *mut u32,
    _handle_buf: *mut u8,
    _handle_count: usize,
    _actual_handle_count: *mut u32,
) -> i32 {
    CHANNEL.with(|channel| channel.borrow_mut().read_message(buf, size, actual_size))
}

#[no_mangle]
pub extern "C" fn channel_close(_handle: u64) -> i32 {
    OakStatus::OK.value()
}

#[no_mangle]
pub extern "C" fn channel_find(_buf: *const u8, _size: usize) -> u64 {
    1
}

// Convenience helpers for tests
pub fn last_message_as_string() -> String {
    CHANNEL.with(|channel| match channel.borrow().messages.front() {
        Some(msg) => unsafe { std::str::from_utf8_unchecked(msg).to_string() },
        None => "".to_string(),
    })
}
pub fn set_read_status(status: Option<i32>) {
    CHANNEL.with(|channel| channel.borrow_mut().read_status = status)
}
pub fn set_write_status(status: Option<i32>) {
    CHANNEL.with(|channel| channel.borrow_mut().write_status = status)
}
pub fn reset_channels() {
    CHANNEL.with(|channel| *channel.borrow_mut() = MockChannel::new())
}
