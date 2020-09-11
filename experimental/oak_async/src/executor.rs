//! Async executor for Oak Nodes.

use core::{cell::RefCell, future::Future, task::Waker};
use futures::{executor::LocalPool, task::LocalSpawnExt};
use log::{debug, trace};
use oak::{ChannelReadStatus, Handle, OakStatus, ReadHandle};
use std::collections::HashMap;

// thread local so `cargo test` can run tests in parallel.
// Oak nodes are single-threaded.
std::thread_local! {
    static EXECUTOR: RefCell<Executor> = RefCell::new(Executor::default());
}

type ReaderId = usize;

struct WaitingReader {
    handle: Handle,
    waker: Waker,
}

#[derive(Default)]
pub struct Executor {
    reader_id_counter: ReaderId,
    // Why not HashMap<Handle, Vec<Waker>>? When a future asks to be removed from the waiting list
    // (i.e. when it is dropped), we need to be able to remove their Waker from the map.
    waiting_readers: HashMap<ReaderId, WaitingReader>,
}

impl Executor {
    pub fn add_waiting_reader(&mut self, reader_id: usize, handle: ReadHandle, waker: &Waker) {
        trace!(
            "Add waiting reader {} waiting on handle {}",
            reader_id,
            handle.handle
        );
        let _ = self.waiting_readers.insert(
            reader_id,
            WaitingReader {
                handle: handle.handle,
                waker: waker.clone(),
            },
        );
    }

    pub fn remove_waiting_reader(&mut self, id: usize) {
        trace!("Remove waiting reader {}", id);
        if self.waiting_readers.remove(&id).is_none() {
            // This is usually not an error. If a Future is dropped as a result of it being woken up
            // and then resolving, we expect the reader_id to not be present in the waiting set.
            debug!(
                "Attempted to remove waiting reader {}, but no such reader was in the waiting set",
                id
            )
        }
    }

    pub fn new_id(&mut self) -> usize {
        let id = self.reader_id_counter;
        self.reader_id_counter += 1;
        id
    }

    pub fn none_waiting(&self) -> bool {
        self.waiting_readers.is_empty()
    }

    pub fn pending_handles(&self) -> HashMap<Handle, ReaderId> {
        self.waiting_readers
            .iter()
            .map(|(reader_id, waiting_reader)| (waiting_reader.handle, *reader_id))
            .collect()
    }

    pub fn wake_reader(&mut self, reader_id: usize) {
        self.waiting_readers
            .remove(&reader_id)
            .unwrap()
            .waker
            .wake();
    }
}

pub fn with_executor<F: FnOnce(&mut Executor) -> R, R>(f: F) -> R {
    EXECUTOR.with(|executor| f(&mut executor.borrow_mut()))
}

pub fn block_on<F: Future + 'static>(f: F) -> Result<F::Output, OakStatus> {
    let mut pool = LocalPool::new();
    let spawner = pool.spawner();
    let main_join_handle = spawner
        .spawn_local_with_handle(f)
        .expect("Failed to spawn main future");
    loop {
        pool.run_until_stalled();

        // We could not make more progress but no handles are waiting: we should be done!
        if with_executor(|e| e.none_waiting()) {
            break;
        }

        // O(n log(n)) where n = executor.pending_handles.len().
        // Dominated by `pending_handles()` which makes a unique mapping of Handle -> ReaderId.
        with_executor(|executor| -> Result<(), OakStatus> {
            let pending_handles = executor.pending_handles();
            let (read_handles, reader_ids): (Vec<ReadHandle>, Vec<ReaderId>) = pending_handles
                .into_iter()
                .map(|(handle, reader_id)| (ReadHandle { handle }, reader_id))
                .unzip();

            trace!(
                "{} readers ({:?}) waiting on handles: {:?}",
                reader_ids.len(),
                reader_ids,
                read_handles
            );

            let channel_statuses = oak::wait_on_channels(&read_handles)?;
            for (status, reader_id) in channel_statuses.into_iter().zip(reader_ids) {
                match status {
                    ChannelReadStatus::NotReady => { /* Nothing */ }
                    ChannelReadStatus::ReadReady => {
                        trace!(
                            "Waking reader with id {} because channel was ReadReady",
                            reader_id
                        );
                        executor.wake_reader(reader_id);
                    }
                    err => {
                        debug!(
                            "Channel wait returned error for reader id {}: {:?}",
                            reader_id, err
                        );
                        // Wake the future so it can deal with the error
                        executor.wake_reader(reader_id);
                    }
                }
            }

            Ok(())
        })?;
    }

    Ok(pool.run_until(main_join_handle))
}
