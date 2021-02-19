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

/// Tests the linear-handles feature in `oak`.
use oak::{Label, OakStatus, ReadHandle, WriteHandle};

fn run_tests() {
    test_cloned_handles_are_valid_and_distinct();

    test_original_and_clone_are_connected();

    test_drop_closes_handle();
}

// clippy analysis is performed on the workspace level, where the linear-handles feature is
// disabled. This results in false positives for these errors, which we thus suppress.
#[allow(clippy::clone_on_copy)]
fn test_cloned_handles_are_valid_and_distinct() {
    let (w, r) =
        oak::channel_create("test", &Label::public_untrusted()).expect("Failed to create channel");
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
    let (w, r) =
        oak::channel_create("test", &Label::public_untrusted()).expect("Failed to create channel");
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
    let (w, r) =
        oak::channel_create("test", &Label::public_untrusted()).expect("Failed to create channel");
    assert_eq!(channel_read(&r), Err(OakStatus::ErrChannelEmpty));

    // Explicitly drop the handle
    core::mem::drop(w);

    // Channel is now orphaned
    assert_eq!(channel_read(&r), Err(OakStatus::ErrChannelClosed));
}

#[no_mangle]
pub extern "C" fn linear_handles_oak_main(init_handle: u64) {
    let log_sender = oak::logger::create().unwrap();
    oak::logger::init(log_sender, log::Level::Debug).unwrap();
    oak::set_panic_hook();

    run_tests();

    write_result(init_handle, "OK");
}

// Writes the test result to the abitest frontend
fn write_result(init_handle: u64, msg: &str) {
    let mut buf = Vec::new();
    let mut handles = Vec::new();

    oak::channel_read(
        &ReadHandle {
            handle: init_handle,
        },
        &mut buf,
        &mut handles,
    )
    .unwrap();
    // Expect exactly one handle (to write the result to)
    assert_eq!(handles.len(), 1);

    let result_handle = WriteHandle { handle: handles[0] };
    channel_write(&result_handle, msg).expect("Failed to write result message");
}

// Convenience functions to send and receive strings over a channel.

fn channel_read(r: &ReadHandle) -> Result<String, OakStatus> {
    let mut buf = Vec::new();
    let mut handles = Vec::new();
    oak::channel_read(r, &mut buf, &mut handles)?;
    let s = String::from_utf8_lossy(&buf[..]).into_owned();
    Ok(s)
}

fn channel_write(w: &WriteHandle, msg: &str) -> Result<(), OakStatus> {
    oak::channel_write(w, msg.as_bytes(), &[])
}
