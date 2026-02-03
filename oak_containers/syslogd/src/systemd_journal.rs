//
// Copyright 2023 The Project Oak Authors
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

use core::ffi::c_size_t;
use std::{
    cmp::Ordering,
    collections::HashMap,
    ffi::{c_int, c_void},
    sync::Arc,
    time::Duration,
};

use nix::errno::Errno;
use tokio::sync::OnceCell;

use self::systemd_sys::*;

mod systemd_sys {
    use core::ffi::c_size_t;
    use std::{
        ffi::{c_int, c_void},
        marker::{PhantomData, PhantomPinned},
    };

    /// Opaque type representing the systemd journal obtained via the systemd C
    /// API.
    ///
    /// See <https://doc.rust-lang.org/nomicon/ffi.html#representing-opaque-structs> that describes this trick.
    #[repr(C)]
    pub struct sd_journal {
        _data: [u8; 0],
        _marker: PhantomData<(*mut u8, PhantomPinned)>,
    }

    #[link(name = "systemd")]
    unsafe extern "C" {
        // https://www.freedesktop.org/software/systemd/man/sd_journal_open.html
        pub fn sd_journal_open(ret: *mut *mut sd_journal, flags: c_int) -> c_int;
        pub fn sd_journal_close(j: *mut sd_journal);

        // https://www.freedesktop.org/software/systemd/man/sd_journal_seek_head.html
        pub fn sd_journal_seek_head(j: *mut sd_journal) -> c_int;

        // https://www.freedesktop.org/software/systemd/man/sd_journal_next.html
        pub fn sd_journal_next(j: *mut sd_journal) -> c_int;

        // https://www.freedesktop.org/software/systemd/man/sd_journal_get_data.html
        pub fn sd_journal_enumerate_data(
            j: *mut sd_journal,
            data: *mut *mut c_void,
            len: *mut c_size_t,
        ) -> c_int;

        // https://www.freedesktop.org/software/systemd/man/sd_journal_wait.html
        pub fn sd_journal_wait(j: *mut sd_journal, timeout_usec: u64) -> c_int;
    }
}

bitflags::bitflags! {
    pub struct JournalOpenFlags: c_int {
        const LOCAL_ONLY                = 1 << 0;
        const RUNTIME_ONLY              = 1 << 1;
        const SYSTEM                    = 1 << 2;
        const CURRENT_USER              = 1 << 3;
        const OS_ROOT                   = 1 << 4;
        const ALL_NAMESPACES            = 1 << 5;
        const INCLUDE_DEFAULT_NAMESPACE = 1 << 6;
        const TAKE_DIRECTORY_FD         = 1 << 7;
    }
}

/// Simple wrapper around libsystemd for reading entries from the systemd
/// journal.
pub struct Journal {
    journal: *mut sd_journal,
    terminate: Arc<OnceCell<()>>,
}

impl Journal {
    pub fn new(flags: JournalOpenFlags, terminate: Arc<OnceCell<()>>) -> Result<Self, Errno> {
        let mut journal = std::ptr::null_mut();
        // Safety: we pass in a valid pointer (to the pointer). The returned journal
        // value is opaque and we never directly access it.
        let ret = unsafe { sd_journal_open(&mut journal, flags.bits()) };
        if ret == 0 { Ok(Self { journal, terminate }) } else { Err(nix::errno::from_i32(ret)) }
    }

    /// Moves the cursor to before the first record in the journal.
    pub fn seek_head(&mut self) -> Result<(), Errno> {
        // Safety: `self.journal` must be valid because of Journal::new().
        let ret = unsafe { sd_journal_seek_head(self.journal) };

        if ret == 0 { Ok(()) } else { Err(nix::errno::from_i32(ret)) }
    }

    // The slice will be valid until the next call to `next()` or `next_data()`,
    // hence this is private.
    fn next_data(&mut self) -> Result<Option<&[u8]>, Errno> {
        let mut data: *mut c_void = std::ptr::null_mut();
        let mut len: c_size_t = 0;
        // Safety: `self.journal` must be valid because of `Journal::new()`; we pass in
        // pointers to valid data structures. Any value is valid for both `data`
        // and `len`.
        let ret = unsafe {
            sd_journal_enumerate_data(self.journal, &mut data as *mut *mut c_void, &mut len)
        };

        match ret.cmp(&0) {
            Ordering::Less => Err(nix::errno::from_i32(ret)),
            Ordering::Equal => Ok(None),
            // Safety: we trust systemd didn't lie to us when giving back the pointer and length.
            Ordering::Greater => {
                Ok(Some(unsafe { std::slice::from_raw_parts(data as *const u8, len) }))
            }
        }
    }

    /// Reads the next entry from the journal; returns None if there is no next
    /// entry.
    pub fn next(&mut self) -> Result<Option<HashMap<String, String>>, Errno> {
        // Safety: `self.journal` must be valid as the only way how to instantiate this
        // is via `Journal::new()`.
        let ret = unsafe { sd_journal_next(self.journal) };

        match ret.cmp(&0) {
            Ordering::Less => Err(nix::errno::from_i32(ret)),
            Ordering::Equal => Ok(None),
            Ordering::Greater => Ok({
                let mut fields: HashMap<String, String> = HashMap::new();

                // Iterate over journal fields; split at '='.
                while let Some(field) = self.next_data()? {
                    let (name, value) =
                        field.split_at(field.iter().position(|x| *x == b'=').unwrap_or(0));
                    fields.insert(
                        std::str::from_utf8(name).unwrap_or("non-string").to_string(),
                        std::str::from_utf8(&value[1..]).unwrap_or("non-string").to_string(),
                    );
                }

                Some(fields)
            }),
        }
    }

    /// Blocks until something is added to the journal.
    ///
    /// Returns false if we've been asked to terminate.
    pub fn wait(&mut self) -> Result<bool, Errno> {
        // Safety: `self.journal` must be valid as the only way how to instantiate this
        // is via `Journal::new()`.
        loop {
            let ret = unsafe {
                sd_journal_wait(self.journal, Duration::new(1, 0).as_micros().try_into().unwrap())
            };
            match ret.cmp(&0) {
                Ordering::Less => return Err(nix::errno::from_i32(ret)),
                Ordering::Greater => return Ok(true),
                Ordering::Equal => {
                    if self.terminate.initialized() {
                        return Ok(false);
                    }
                }
            }
        }
    }
}

impl Drop for Journal {
    fn drop(&mut self) {
        // Safety: `self.journal` must be valid as the only way how to instantiate this
        // is via `Journal::new()`.
        unsafe { sd_journal_close(self.journal) };
    }
}

impl Iterator for Journal {
    type Item = Result<HashMap<String, String>, Errno>;

    fn next(&mut self) -> Option<Self::Item> {
        loop {
            if let Some(result) = self.next().transpose() {
                return Some(result);
            }
            if !self.wait().unwrap() {
                return None;
            }
        }
    }
}
