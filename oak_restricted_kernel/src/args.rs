//
// Copyright 2022 The Project Oak Authors
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

extern crate alloc;

use alloc::collections::btree_map::BTreeMap;
use core::{cell::LazyCell, ffi::CStr};

use arrayvec::ArrayString;

static mut ARGS: ArrayString<512> = ArrayString::new_const();

/// Kernel arguments.
///
/// The pattern for arguments is "key1 key2=val2 key3=val3". The tokenization is
/// rather simple, so whitespace matters and there is no way to escape spaces
/// right now.
pub struct Args {
    args: LazyCell<BTreeMap<&'static str, &'static str>>,
}

impl Args {
    /// Returns the full command line argument string.
    pub fn args(&self) -> &'static str {
        // Safety: `Args::args()` can only be called after `init_args` is called.
        // Ostensibly, we could cache this in a Lazy as well, but that's
        // probably not worth it.
        #[allow(static_mut_refs)]
        unsafe {
            ARGS.as_str()
        }
    }

    // Returns the value of the given command line argument.
    pub fn get(&self, key: &str) -> Option<&str> {
        self.args.get(key).copied()
    }
}

/// Buffers kernel arguments in a static variable.
///
/// This function is intended to be called fairly early in the boot process,
/// when we don't even have memory allocation available. This also means that we
/// can't use anyhow::Result as the return value, as anyhow relies on
/// allocation.
pub fn init_args(args: &CStr) -> core::result::Result<Args, &str> {
    let args = args
        .to_str()
        .map_err(|core::str::Utf8Error { .. }| "kernel arguments are not valid UTF-8")?;
    // Safety: this is called once early in the initialization process from a single
    // thread, so there will not be any concurrent writes.
    #[allow(static_mut_refs)]
    unsafe { ARGS.try_push_str(args) }
        .map_err(|arrayvec::CapacityError { .. }| "kernel arguments too long")?;
    // Safety: we've just populated ARGS, successfully, in the line just above.
    #[allow(static_mut_refs)]
    Ok(Args { args: LazyCell::new(|| split_args(unsafe { ARGS.as_str() })) })
}

fn split_args(args: &str) -> BTreeMap<&str, &str> {
    let mut m = BTreeMap::new();
    args.split_whitespace().map(|x| x.split_once('=').unwrap_or((x, ""))).for_each(|(k, v)| {
        m.insert(k, v);
    });
    m
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn no_args() {
        let res = split_args("");
        assert_eq!(res.len(), 0);
    }

    #[test]
    fn args() {
        let res = split_args("one two=two three=three2=three3");
        assert_eq!(res.len(), 3);
        assert_eq!(res.get("one").copied().unwrap(), "");
        assert_eq!(res.get("two").copied().unwrap(), "two");
        assert_eq!(res.get("three").copied().unwrap(), "three2=three3");
    }

    #[test]
    fn broken_whitespace() {
        let res = split_args("one = two");
        assert_eq!(res.len(), 3);
        assert_eq!(res.get("one").copied().unwrap(), "");
        assert_eq!(res.get("two").copied().unwrap(), "");
        assert_eq!(res.get("").copied().unwrap(), "");
    }
}
