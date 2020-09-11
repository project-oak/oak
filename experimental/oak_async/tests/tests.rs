mod dummy_data;
mod fake_runtime;

use dummy_data::DummyData;
use fake_runtime::{add_ready_data, set_error, set_wait_on_channels_handler};
use log::LevelFilter;
use oak::{
    io::{Decodable, Receiver},
    ChannelReadStatus, OakError, OakStatus, ReadHandle,
};
use oak_abi::Handle;
use oak_async::{block_on, ChannelRead, ReceiverAsync};

fn init() {
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
    init();
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
    init();
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
                123 => {
                    handle.set_status(ChannelReadStatus::NotReady);
                }
                456 => {
                    add_ready_data(456, &DummyData::new("hello"));
                    handle.set_status(ChannelReadStatus::ReadReady);
                }
                c => panic!("Unexpected waiting channel {}", c),
            };
        }
        OakStatus::Ok
    });

    let result: Result<DummyData, OakError> = block_on(async {
        futures::future::select(do_channel_read(123), do_channel_read(456))
            .await
            .factor_first()
            // Note: It is important that we extract the result inside the async block. Doing this
            // outside the async scope will block indefinitely, because it will try and move the
            // unresolved ChannelRead on 123 outside of the async block, but for block_on to
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
    set_error(666, OakStatus::ErrBadHandle);

    let result: Result<DummyData, _> = block_on(do_channel_read(666)).expect("block_on failed");

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
        assert_eq!(handles[0].handle(), 666);
        handles[0].set_status(ChannelReadStatus::PermissionDenied);
        set_error(666, OakStatus::ErrPermissionDenied);
        OakStatus::Ok
    });

    let result: Result<DummyData, _> = block_on(do_channel_read(666)).expect("block_on failed");

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
        assert_eq!(handles[0].handle(), 123);
        if counter >= 100 {
            handles[0].set_status(ChannelReadStatus::ReadReady);
            add_ready_data(123, &DummyData::new("data"));
        } else {
            handles[0].set_status(ChannelReadStatus::NotReady);
        }
        counter += 1;
        OakStatus::Ok
    });

    let result: Result<DummyData, _> = block_on(do_channel_read(123)).expect("block_on failed");

    assert_eq!(result.expect("channel read failed"), DummyData::new("data"));
}

#[test]
fn many_reads_parallel() {
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
        (0..1000).into_iter().map(do_channel_read),
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

fn do_channel_read<T: Decodable + Send>(handle: Handle) -> ChannelRead<T> {
    Receiver::new(ReadHandle { handle }).receive_async()
}
