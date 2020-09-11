use core::cell::RefCell;
use oak::io::Encodable;
use oak_abi::{
    proto::oak::{ChannelReadStatus, OakStatus},
    Handle,
};
use std::collections::{HashMap, VecDeque};

#[repr(packed)]
pub struct HandleWithStatus {
    handle: Handle,
    status: u8,
}

impl HandleWithStatus {
    pub fn handle(&self) -> Handle {
        self.handle
    }

    pub fn set_status(&mut self, status: ChannelReadStatus) {
        self.status = status as i32 as u8;
    }
}

#[no_mangle]
pub extern "C" fn wait_on_channels(buf: *mut u8, count: u32) -> u32 {
    let handles =
        unsafe { core::slice::from_raw_parts_mut(buf as *mut HandleWithStatus, count as usize) };
    WAIT_ON_CHANNELS_HANDLER.with(|handler| {
        (handler
            .borrow_mut()
            .as_mut()
            .expect("no wait_on_channels handler configured"))(handles)
    }) as i32 as u32
}

std::thread_local! {
    static WAIT_ON_CHANNELS_HANDLER: RefCell<Option<Box<dyn FnMut(&mut [HandleWithStatus]) -> OakStatus>>> = RefCell::new(None);
}

pub fn set_wait_on_channels_handler<F: 'static + FnMut(&mut [HandleWithStatus]) -> OakStatus>(
    handler: F,
) {
    WAIT_ON_CHANNELS_HANDLER.with(|cell| cell.replace(Some(Box::new(handler))));
}

#[no_mangle]
pub extern "C" fn channel_read(
    handle: Handle,
    buf: *mut u8,
    size: usize,
    actual_size: *mut u32,
    _handle_buf: *mut u8,
    _handle_count: u32,
    actual_handle_count: *mut u32,
) -> u32 {
    READY_DATA.with(|ready_data| {
        let mut ready_data = ready_data.borrow_mut();
        let data_queue = ready_data.entry(handle).or_default();
        let status = match data_queue.front() {
            None => OakStatus::ErrChannelEmpty,
            Some(Err(status)) => *status,
            Some(Ok(data)) if data.len() > size => {
                unsafe { *actual_size = data.len() as u32 };
                OakStatus::ErrBufferTooSmall
            }
            Some(Ok(data)) => {
                unsafe {
                    let buf = core::slice::from_raw_parts_mut(buf, data.len());
                    buf.copy_from_slice(&data);
                    *actual_size = data.len() as u32;
                    *actual_handle_count = 0;
                };
                let _ = data_queue.pop_front();
                OakStatus::Ok
            }
        };
        status as i32 as u32
    })
}

std::thread_local! {
    static READY_DATA: RefCell<HashMap<Handle, VecDeque<Result<Vec<u8>, OakStatus>>>> = RefCell::new(HashMap::new());
}

pub fn add_ready_data<T: Encodable>(handle: Handle, data: &T) {
    let msg = data.encode().expect("Failed to encode ready data");
    READY_DATA.with(|ready_data| {
        ready_data
            .borrow_mut()
            .entry(handle)
            .or_default()
            .push_back(Ok(msg.bytes))
    });
}

// Note: this status is added into the queue of ready data, so any previously add ready data must
// first be read before this status will be returned. The channel status is never removed, any
// future reads will always return this error status.
pub fn set_error(handle: Handle, status: OakStatus) {
    assert_ne!(status, OakStatus::Ok);
    READY_DATA.with(|ready_data| {
        ready_data
            .borrow_mut()
            .entry(handle)
            .or_default()
            .push_back(Err(status))
    });
}
