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

/// Tests the linear-handles feature in `oak_io`.
// Note: This environment is very bare. the Oak SDK does not support linear handles, so we can
// only use the ABI and `oak_io`
use oak_abi::proto::oak::label::Label;
use oak_io::{
    handle::{ReadHandle, WriteHandle},
    OakStatus,
};

fn run_tests() {
    test_cloned_handles_are_valid_and_distinct();

    test_original_and_clone_are_connected();

    test_drop_closes_handle();
}

// clippy analysis is performed on the workspace level, where the linear-handles feature is
// disabled. This results in false positives for these errors, which we thus suppress.
#[allow(clippy::clone_on_copy)]
fn test_cloned_handles_are_valid_and_distinct() {
    let (w, r) = channel_create().expect("Failed to create channel");
    let w2 = w.clone();
    let r2 = r.clone();

    // Check that the handles are not invalid
    assert!(w2.handle != oak_abi::INVALID_HANDLE);
    assert!(r2.handle != oak_abi::INVALID_HANDLE);
    // Check that the handles are distinct from the original ones
    assert!(w.handle != w2.handle);
    assert!(r.handle != r2.handle);
}

// Writes from the cloned handle should be readable from the original, and vice versa
#[allow(clippy::clone_on_copy)]
fn test_original_and_clone_are_connected() {
    let (w, r) = channel_create().expect("Failed to create channel");
    let w2 = w.clone();
    let r2 = r.clone();

    // Write from original, read from clone
    channel_write(&w, "msg1").expect("Failed to write to w");
    let msg1 = channel_read(&r2).expect("Failed to read from r2");
    assert_eq!(msg1, "msg1");

    // Write from clone, read from original
    channel_write(&w2, "msg2").expect("Failed to write to w2");
    let msg2 = channel_read(&r).expect("Failed to read from r");
    assert_eq!(msg2, "msg2");
}

#[allow(clippy::drop_copy)]
fn test_drop_closes_handle() {
    let (w, r) = channel_create().expect("Failed to create channel");
    assert_eq!(channel_read(&r), Err(OakStatus::ErrChannelEmpty));

    // Explicitly drop the handle
    core::mem::drop(w);

    // Channel is now orphaned
    assert_eq!(channel_read(&r), Err(OakStatus::ErrChannelClosed));
}

#[no_mangle]
pub extern "C" fn linear_handles_oak_main(init_handle: u64) {
    let _ = std::panic::catch_unwind(|| {
        // Set up a panic handler that reports errors to the parent node
        std::panic::set_hook(Box::new(move |panic_info| {
            let message = if let Some(s) = panic_info.payload().downcast_ref::<&str>() {
                s.to_owned()
            } else if let Some(s) = panic_info.payload().downcast_ref::<String>() {
                s
            } else {
                "<no message available>"
            };
            let location = if let Some(location) = panic_info.location() {
                format!("{}:{}", location.file(), location.line())
            } else {
                "<location unavailable>".to_string()
            };
            write_result(
                init_handle,
                &format!(
                    "panic in linear handles module at ({}), message: {}",
                    location, message
                ),
            );
        }));
        run_tests();

        write_result(init_handle, "OK");
    });
}

fn write_result(init_handle: u64, msg: &str) {
    let buf = msg.as_bytes();
    let mut _actual_size = 0u32;
    let mut _actual_handle_count = 0u32;
    let mut result_handle = 0u64;

    unsafe {
        oak_abi::channel_read(
            init_handle,
            core::ptr::null_mut::<u8>(),
            0,
            &mut _actual_size as *mut u32,
            &mut result_handle as *mut u64 as *mut u8,
            1,
            &mut _actual_handle_count as *mut u32,
        );

        oak_abi::channel_write(
            result_handle,
            buf.as_ptr() as *const u8,
            buf.len(),
            core::ptr::null::<u8>(),
            0,
        );
    }
}

fn channel_read(r: &ReadHandle) -> Result<String, OakStatus> {
    const BUF_LEN: usize = 256;
    let mut buf = [0u8; BUF_LEN];
    let mut actual_size = 0u32;
    let mut _actual_handle_count = 0u32;

    let result = unsafe {
        oak_abi::channel_read(
            r.handle,
            &mut buf[0] as *mut u8,
            BUF_LEN,
            &mut actual_size as *mut u32,
            core::ptr::null_mut::<u8>(),
            0,
            &mut _actual_handle_count as *mut u32,
        )
    };
    let result = OakStatus::from_i32(result as i32).unwrap();
    match result {
        OakStatus::Ok => Ok(String::from_utf8_lossy(&buf[..(actual_size as usize)]).into_owned()),
        e => Err(e),
    }
}

fn channel_write(w: &WriteHandle, msg: &str) -> Result<(), OakStatus> {
    let result = unsafe {
        oak_abi::channel_write(
            w.handle,
            msg.as_ptr() as *const u8,
            msg.len(),
            core::ptr::null::<u8>(),
            0,
        )
    };
    let result = OakStatus::from_i32(result as i32).unwrap();
    match result {
        OakStatus::Ok => Ok(()),
        e => Err(e),
    }
}

fn channel_create() -> Result<(WriteHandle, ReadHandle), OakStatus> {
    let mut w = WriteHandle {
        handle: oak_abi::INVALID_HANDLE,
    };
    let mut r = ReadHandle {
        handle: oak_abi::INVALID_HANDLE,
    };
    let name_bytes = "test_channel".as_bytes();
    let label_bytes = Label::public_untrusted().serialize();
    let result = unsafe {
        oak_abi::channel_create(
            &mut w.handle as *mut u64,
            &mut r.handle as *mut u64,
            name_bytes.as_ptr(),
            name_bytes.len(),
            label_bytes.as_ptr(),
            label_bytes.len(),
        )
    };
    let result = OakStatus::from_i32(result as i32).unwrap();
    match result {
        OakStatus::Ok => Ok((w, r)),
        e => Err(e),
    }
}
