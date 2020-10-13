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

mod dummy_data;
mod fake_runtime;

use dummy_data::DummyData;
use fake_runtime::{add_ready_data, set_error, set_wait_on_channels_handler};
use futures::prelude::*;
use log::LevelFilter;
use oak::{
    io::{Decodable, Receiver},
    ChannelReadStatus, OakError, OakStatus, ReadHandle,
};
use oak_abi::Handle;
use oak_async::{block_on, ChannelRead, ChannelReadStream, ReceiverAsync};

// Dummy handle values.
const HANDLE_0: Handle = 123;
const HANDLE_1: Handle = 456;

fn init() {
    fake_runtime::init();
    let _ = env_logger::builder()
        .is_test(true)
        .filter_level(LevelFilter::Trace)
        .try_init();
}

#[test]
fn block_on_resolve_immediate() {
    init();
    let result = block_on(async { 42 }).expect("block_on failed");

    assert_eq!(result, 42);
}

#[test]
fn block_on_channel_read_immediate_ready() {
    init();
    add_ready_data(1, &DummyData::new("data"));
    let read_result: Result<DummyData, OakError> =
        block_on(do_channel_read(1)).expect("block_on failed");

    assert_eq!(
        read_result.expect("Read returned error"),
        DummyData::new("data")
    )
}

#[test]
fn block_on_channel_read_ready_after_wait() {
    init();
    set_wait_on_channels_handler(|handles| {
        assert_eq!(handles.len(), 1);
        assert_eq!(handles[0].handle(), HANDLE_0);
        add_ready_data(HANDLE_0, &DummyData::new("data"));
        handles[0].set_status(ChannelReadStatus::ReadReady);
        OakStatus::Ok
    });

    let read_result: Result<DummyData, OakError> =
        block_on(do_channel_read(HANDLE_0)).expect("block_on failed");

    assert_eq!(
        read_result.expect("Read returned error"),
        DummyData::new("data")
    )
}

#[test]
fn block_on_multiple_readers_sequentially() {
    init();
    set_wait_on_channels_handler(|handles| {
        assert_eq!(handles.len(), 1);
        let data = match handles[0].handle() {
            HANDLE_0 => "Hello",
            HANDLE_1 => "world!",
            c => panic!("Unexpected waiting channel {}", c),
        };
        add_ready_data(handles[0].handle(), &DummyData::new(data));
        handles[0].set_status(ChannelReadStatus::ReadReady);
        OakStatus::Ok
    });

    let result = block_on(async {
        let a: DummyData = do_channel_read(HANDLE_0)
            .await
            .expect("Failed to read channel HANDLE_0");
        let b: DummyData = do_channel_read(HANDLE_1)
            .await
            .expect("Failed to read channel HANDLE_1");

        [a.0, b.0].join(", ")
    })
    .expect("block_on failed");

    assert_eq!(result, "Hello, world!");
}

#[test]
fn block_on_multiple_readers_parallel() {
    init();
    set_wait_on_channels_handler(|handles| {
        for handle in handles.iter_mut() {
            let data = match handle.handle() {
                HANDLE_0 => "Hello",
                HANDLE_1 => "world!",
                c => panic!("Unexpected waiting channel {}", c),
            };
            add_ready_data(handle.handle(), &DummyData::new(data));
            handle.set_status(ChannelReadStatus::ReadReady);
        }
        OakStatus::Ok
    });

    let (a, b): (Result<DummyData, OakError>, Result<DummyData, OakError>) = block_on(
        futures::future::join(do_channel_read(HANDLE_0), do_channel_read(HANDLE_1)),
    )
    .expect("block_on failed");

    assert_eq!(
        a.expect("Read from channel HANDLE_0 failed"),
        DummyData::new("Hello")
    );

    assert_eq!(
        b.expect("Read from channel HANDLE_1 failed"),
        DummyData::new("world!")
    );
}

#[test]
fn block_on_drop_channel_read_immediately() {
    init();
    block_on(async {
        // The future is immediately dropped, so never polled
        let _ = do_channel_read::<DummyData>(1);
    })
    .expect("block_on failed");
}

#[test]
fn block_on_drop_channel_read_after_wait() {
    init();
    set_wait_on_channels_handler(|handles| {
        std::thread::sleep(std::time::Duration::from_secs(1));
        for handle in handles.iter_mut() {
            match handle.handle() {
                HANDLE_0 => {
                    handle.set_status(ChannelReadStatus::NotReady);
                }
                HANDLE_1 => {
                    add_ready_data(HANDLE_1, &DummyData::new("hello"));
                    handle.set_status(ChannelReadStatus::ReadReady);
                }
                c => panic!("Unexpected waiting channel {}", c),
            };
        }
        OakStatus::Ok
    });

    let result: Result<DummyData, OakError> = block_on(async {
        futures::future::select(do_channel_read(HANDLE_0), do_channel_read(HANDLE_1))
            .await
            .factor_first()
            // Note: It is important that we extract the result inside the async block. Doing this
            // outside the async scope will block indefinitely, because it will try and move the
            // unresolved ChannelRead on HANDLE_0 outside of the async block, but for block_on to
            // terminate that ChannelRead must be `Drop`ed first (to remove it from the waiting
            // set).
            .0
    })
    .expect("block_on failed");

    assert_eq!(
        result.expect("Channel read failed"),
        DummyData::new("hello")
    );
}

#[test]
fn block_on_channel_read_propagate_immediate_error() {
    init();
    set_error(HANDLE_0, OakStatus::ErrBadHandle);

    let result: Result<DummyData, _> =
        block_on(do_channel_read(HANDLE_0)).expect("block_on failed");

    match result {
        Err(OakError::OakStatus(OakStatus::ErrBadHandle)) => { /* The expected error */ }
        e => panic!("Unexpected error: {:?}", e),
    }
}

#[test]
fn block_on_channel_read_propagate_error_after_wait() {
    init();
    set_wait_on_channels_handler(|handles| {
        assert_eq!(handles.len(), 1);
        assert_eq!(handles[0].handle(), HANDLE_0);
        handles[0].set_status(ChannelReadStatus::PermissionDenied);
        set_error(HANDLE_0, OakStatus::ErrPermissionDenied);
        OakStatus::Ok
    });

    let result: Result<DummyData, _> =
        block_on(do_channel_read(HANDLE_0)).expect("block_on failed");

    match result {
        Err(OakError::OakStatus(OakStatus::ErrPermissionDenied)) => { /* The expected error */ }
        e => panic!("Unexpected error: {:?}", e),
    }
}

#[test]
fn block_on_wait_many_times() {
    init();

    let mut counter = 0;
    set_wait_on_channels_handler(move |handles| {
        log::debug!("wait_on_channels counter: {}", counter);
        assert_eq!(handles.len(), 1);
        assert_eq!(handles[0].handle(), HANDLE_0);
        if counter >= 100 {
            handles[0].set_status(ChannelReadStatus::ReadReady);
            add_ready_data(HANDLE_0, &DummyData::new("data"));
        } else {
            handles[0].set_status(ChannelReadStatus::NotReady);
        }
        counter += 1;
        OakStatus::Ok
    });

    let result: Result<DummyData, _> =
        block_on(do_channel_read(HANDLE_0)).expect("block_on failed");

    assert_eq!(result.expect("channel read failed"), DummyData::new("data"));
}

#[test]
fn many_reads_parallel() {
    init();

    set_wait_on_channels_handler(move |handles| {
        for (i, handle) in handles.iter_mut().enumerate() {
            // Every wait_on_channels call we send data to half the waiting channels
            if i % 2 == 0 {
                add_ready_data(
                    handle.handle(),
                    &DummyData::new(&format!("handle: {:0>4}", handle.handle())),
                );
                handle.set_status(ChannelReadStatus::ReadReady);
            } else {
                handle.set_status(ChannelReadStatus::NotReady);
            }
        }
        OakStatus::Ok
    });

    let results: Result<Vec<DummyData>, OakError> = block_on(futures::future::try_join_all(
        (0..1000).map(do_channel_read),
    ))
    .expect("block_on failed");

    let mut data: Vec<String> = results
        .expect("One of the channel reads failed")
        .into_iter()
        .map(|d| d.0)
        .collect();
    data.sort();
    for (i, s) in data.iter().enumerate() {
        assert_eq!(s, &format!("handle: {:0>4}", i));
    }
    assert_eq!(data.len(), 1000);
}

// Stream functionality relies heavily on the implementation of `Future`, so we only need minimal
// tests for the `Stream` impl.
#[test]
fn stream_read_multiple() {
    init();

    let mut data_sent_count = 0;
    set_wait_on_channels_handler(move |handles| {
        assert_eq!(handles.len(), 1);
        assert_eq!(handles[0].handle(), HANDLE_0);
        if data_sent_count < 10 {
            handles[0].set_status(ChannelReadStatus::ReadReady);
            add_ready_data(
                handles[0].handle(),
                &DummyData::new(&data_sent_count.to_string()),
            );
            data_sent_count += 1;
        } else {
            handles[0].set_status(ChannelReadStatus::Orphaned);
            set_error(handles[0].handle(), OakStatus::ErrChannelClosed);
        }
        OakStatus::Ok
    });
    let reference_data: Vec<DummyData> = (0..10).map(|n| DummyData::new(&n.to_string())).collect();

    let data_received: Vec<DummyData> = block_on(do_channel_read_stream(HANDLE_0).try_collect())
        .expect("block_on failed")
        .expect("Failed to read from stream");

    assert_eq!(data_received, reference_data);
}

#[test]
fn stream_nothing() {
    init();

    set_wait_on_channels_handler(move |handles| {
        assert_eq!(handles.len(), 1);
        assert_eq!(handles[0].handle(), HANDLE_0);

        handles[0].set_status(ChannelReadStatus::Orphaned);
        set_error(handles[0].handle(), OakStatus::ErrChannelClosed);

        OakStatus::Ok
    });

    let data_received: Vec<DummyData> = block_on(do_channel_read_stream(HANDLE_0).try_collect())
        .expect("block_on failed")
        .expect("Failed to read from stream");

    assert_eq!(data_received, vec![]);
}

fn do_channel_read<T: Decodable + Send>(handle: Handle) -> ChannelRead<T> {
    Receiver::new(ReadHandle { handle }).receive_async()
}

fn do_channel_read_stream<T: Decodable + Send>(handle: Handle) -> ChannelReadStream<T> {
    Receiver::new(ReadHandle { handle }).receive_stream()
}
