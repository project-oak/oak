use std::cell::RefCell;

#[cfg(test)]
mod tests;

// Create a test-only implementation of channel_read and channel_write which
// holds a single message (and which ignores channel handle).  A non-None status
// value (set with set_status()) will be returned on any channel operation.
thread_local! {
    static MESSAGE: RefCell<Vec<u8>> = RefCell::new(Vec::new());
    static STATUS: RefCell<Option<i32>> = RefCell::new(None);
}

#[no_mangle]
pub extern "C" fn channel_write(_handle: u64, buf: *const u8, size: usize) -> i32 {
    if let Some(status) = get_status() {
        return status;
    }
    MESSAGE.with(|msg| {
        let mut new_msg = Vec::with_capacity(size);
        unsafe {
            std::ptr::copy_nonoverlapping(buf, new_msg.as_mut_ptr(), size);
            new_msg.set_len(size);
        }
        *msg.borrow_mut() = new_msg;
    });
    STATUS_OK
}

#[no_mangle]
pub extern "C" fn channel_read(
    _handle: u64,
    buf: *mut u8,
    size: usize,
    actual_size: *mut u32,
) -> i32 {
    if let Some(status) = get_status() {
        return status;
    }
    MESSAGE.with(|msg| {
        let len = msg.borrow().len();
        unsafe { *actual_size = len as u32 }
        if len > size {
            return STATUS_ERR_BUFFER_TOO_SMALL;
        }
        unsafe {
            std::ptr::copy_nonoverlapping(msg.borrow().as_ptr(), buf, len);
        }
        STATUS_OK
    })
}

pub fn last_message() -> String {
    MESSAGE.with(|msg| unsafe { std::str::from_utf8_unchecked(&*msg.borrow()).to_string() })
}

// Set the status for future channel operations.
pub fn set_status(next: Option<i32>) {
    STATUS.with(|status| *status.borrow_mut() = next)
}

fn get_status() -> Option<i32> {
    STATUS.with(|status| *status.borrow())
}

// Keep in sync with /oak/server/status.h
pub const STATUS_OK: i32 = 0;
pub const STATUS_ERR_BUFFER_TOO_SMALL: i32 = 4;
