use std::cell::RefCell;

#[cfg(test)]
mod tests;

// Create a test-only implementation of channel_write to receive logged data.
thread_local! {
    static MESSAGE: RefCell<Vec<u8>> = RefCell::new(Vec::new());
}

#[no_mangle]
pub extern "C" fn channel_write(_handle: u64, buf: *const u8, size: usize) -> i32 {
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

pub fn last_message() -> String {
    MESSAGE.with(|msg| unsafe { std::str::from_utf8_unchecked(&*msg.borrow()).to_string() })
}

// Keep in sync with /oak/server/status.h
const STATUS_OK: i32 = 0;
