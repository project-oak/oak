mod dummy_data;
mod fake_runtime;

use dummy_data::DummyData;
use fake_runtime::{add_ready_data, set_wait_on_channels_handler};
use oak::{
    io::{Decodable, Receiver},
    ChannelReadStatus, OakError, OakStatus, ReadHandle,
};
use oak_abi::Handle;
use oak_async::{block_on, ChannelRead, ReceiverAsync};

#[test]
fn block_on_resolve_immediate() {
    let result = block_on(async { 42 }).expect("block_on failed");

    assert_eq!(result, 42);
}

#[test]
fn block_on_channel_read_immediate_ready() {
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
    set_wait_on_channels_handler(|handles| {
        assert_eq!(handles.len(), 1);
        assert_eq!(handles[0].handle(), 123);
        add_ready_data(123, &DummyData::new("data"));
        handles[0].set_status(ChannelReadStatus::ReadReady);
        OakStatus::Ok
    });

    let read_result: Result<DummyData, OakError> =
        block_on(do_channel_read(123)).expect("block_on failed");

    assert_eq!(
        read_result.expect("Read returned error"),
        DummyData::new("data")
    )
}

#[test]
fn block_on_multiple_readers_sequentially() {
    set_wait_on_channels_handler(|handles| {
        assert_eq!(handles.len(), 1);
        let data = match handles[0].handle() {
            123 => "Hello",
            456 => "world!",
            c => panic!("Unexpected waiting channel {}", c),
        };
        add_ready_data(handles[0].handle(), &DummyData::new(data));
        handles[0].set_status(ChannelReadStatus::ReadReady);
        OakStatus::Ok
    });

    let result = block_on(async {
        let a: DummyData = do_channel_read(123)
            .await
            .expect("Failed to read channel 123");
        let b: DummyData = do_channel_read(456)
            .await
            .expect("Failed to read channel 456");

        [a.0, b.0].join(", ")
    })
    .expect("block_on failed");

    assert_eq!(result, "Hello, world!");
}

#[test]
fn block_on_multiple_readers_parallel() {
    set_wait_on_channels_handler(|handles| {
        for handle in handles.iter_mut() {
            let data = match handle.handle() {
                123 => "Hello",
                456 => "world!",
                c => panic!("Unexpected waiting channel {}", c),
            };
            add_ready_data(handle.handle(), &DummyData::new(data));
            handle.set_status(ChannelReadStatus::ReadReady);
        }
        OakStatus::Ok
    });

    let (a, b): (Result<DummyData, OakError>, Result<DummyData, OakError>) = block_on(
        futures::future::join(do_channel_read(123), do_channel_read(456)),
    )
    .expect("block_on failed");

    assert_eq!(
        a.expect("Read from channel 123 failed"),
        DummyData::new("Hello")
    );

    assert_eq!(
        b.expect("Read from channel 456 failed"),
        DummyData::new("world!")
    );
}

//
// - Multiple readers
// - Dropped reads
// - Read errors
// - Only ready after many waits

fn do_channel_read<T: Decodable + Send>(handle: Handle) -> ChannelRead<T> {
    Receiver::new(ReadHandle { handle }).receive_async()
}
