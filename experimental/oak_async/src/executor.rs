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

//! Async executor for Oak Nodes.

use core::{cell::RefCell, future::Future, task::Waker};
use futures::{executor::LocalPool, task::LocalSpawnExt};
use log::{debug, trace};
use oak::{ChannelReadStatus, Handle, OakStatus, ReadHandle};
use std::collections::HashMap;

// thread local so `cargo test` can run tests in parallel.
//
// Oak nodes are single-threaded. When wasm gains support for multithreading,
// it is likely we will still have this thread local variable, but the inner
// value will be backed by an Arc so the actual object is global.
// When a new thread is created it will inherit the executor from its parent.
// That way tests will still work, it would even be possible to run multiple
// executors in different threads, each with their own threadpool.
//
// It is worth noting Tokio, a multi-threaded executor, also uses a thread local
// variable to store the handle to an executor:
// https://github.com/tokio-rs/tokio/blob/7ec6d88b21ea3e5531176f526a51dae0a4513025/tokio/src/runtime/context.rs#L7
std::thread_local! {
    static EXECUTOR: RefCell<Executor> = RefCell::new(Executor::default());
}

pub type ReaderId = u64;

struct WaitingReader {
    handle: Handle,
    waker: Waker,
}

/// Global executor context.
///
/// [`with_executor`] provides a way to get a handle to the global executor instance.
#[derive(Default)]
pub struct Executor {
    /// Used to assign a unique id to each reader. It is incremented by every newly created reader
    next_reader_id: ReaderId,
    /// Set of readers waiting for data. All handles in this map are polled in `wait_on_channels`.
    // Why not HashMap<Handle, Vec<Waker>>? When a future asks to be removed from the waiting list
    // (i.e. when it is dropped), we need to be able to remove their Waker from the map.
    waiting_readers: HashMap<ReaderId, WaitingReader>,
}

impl Executor {
    pub fn add_waiting_reader(&mut self, reader_id: ReaderId, handle: ReadHandle, waker: &Waker) {
        trace!(
            "Add waiting reader {} waiting on handle {}",
            reader_id,
            handle.handle
        );
        self.waiting_readers.insert(
            reader_id,
            WaitingReader {
                handle: handle.handle,
                waker: waker.clone(),
            },
        );
    }

    pub fn remove_waiting_reader(&mut self, reader_id: ReaderId) {
        trace!("Remove waiting reader {}", reader_id);
        if self.waiting_readers.remove(&reader_id).is_none() {
            // This is usually not an error. If a Future is dropped as a result of it being woken up
            // and then resolving, we expect the reader_id to not be present in the waiting set.
            debug!(
                "Attempted to remove waiting reader {}, but no such reader was in the waiting set",
                reader_id
            )
        }
    }

    pub fn new_id(&mut self) -> ReaderId {
        let id = self.next_reader_id;
        // Collisions are technically possible, but only if one read is very slow and many async
        // reads (2^64) are requested in quick succession.
        self.next_reader_id = self.next_reader_id.wrapping_add(1);
        id
    }

    pub fn none_waiting(&self) -> bool {
        self.waiting_readers.is_empty()
    }

    /// Returns all handles for which reads are pending, and the id of one of the readers for that
    /// channel.
    ///
    /// The `Vec`s returned are guaranteed to have the same length, and a handle at index `i`
    /// corresponds to the reader id at index `i`. Having separate `Vec`s for both values makes it
    /// easy to pass the `ReadHandle`s to `wait_on_channels`, and then zip the results to the
    /// `ReaderId`s.
    pub fn pending_handles(&self) -> (Vec<ReadHandle>, Vec<ReaderId>) {
        self.waiting_readers
            .iter()
            .map(|(reader_id, waiting_reader)| (waiting_reader.handle, *reader_id))
            .collect::<HashMap<Handle, ReaderId>>()
            .into_iter()
            .map(|(handle, reader_id)| (ReadHandle { handle }, reader_id))
            .unzip()
    }

    /// Remove a reader from the waiting set and wake it
    pub fn wake_reader(&mut self, reader_id: ReaderId) {
        self.waiting_readers
            .remove(&reader_id)
            // wake_reader is only called by the executor as a result of it being added to the
            // waiting set and then receiving data. No futures can run while the executor is waiting
            // for data and then waking readers, so the reader cannot have removed itself in the
            // meantime. It follows that a failure to remove the given reader from the waiting set
            // constitutes an executor bug.
            .unwrap_or_else(|| {
                panic!(
                    "wake_reader called on reader_id {}, which is not in the waiting reader set",
                    reader_id
                )
            })
            .waker
            .wake();
    }
}

/// Runs the given closure, providing it with a handle to the current executor
pub fn with_executor<F: FnOnce(&mut Executor) -> R, R>(f: F) -> R {
    EXECUTOR.with(|executor| f(&mut executor.borrow_mut()))
}

/// Block the current thread until the provided `Future` has been `poll`ed to completion.
///
/// Returns `Err(_)` if the call to `wait_on_channels` fails.
pub fn block_on<F: Future + 'static>(f: F) -> Result<F::Output, OakStatus> {
    let mut pool = LocalPool::new();
    let spawner = pool.spawner();
    let main_join_handle = spawner
        .spawn_local_with_handle(f)
        .expect("Failed to spawn main future");
    loop {
        // Poll futures in the pool until none of them can make any progress.
        pool.run_until_stalled();

        // We could not make more progress but no handles are waiting: we should be done!
        if with_executor(|e| e.none_waiting()) {
            break;
        }

        // There are pending futures but none of them could make progress, which means they are all
        // waiting for channels to become ready.

        // O(n) where n = number of pending readers. Dominated by `executor.pending_handles()` which
        // needs to loop over all readers. All subsequent operations are on the order of the number
        // of pending handles.
        with_executor(|executor| -> Result<(), OakStatus> {
            let (read_handles, reader_ids) = executor.pending_handles();

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
