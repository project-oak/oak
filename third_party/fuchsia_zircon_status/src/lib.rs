// Copyright 2018 The Fuchsia Authors. All rights reserved.
// Use of this source code is governed by a BSD-style license that can be
// found in the LICENSE file.

//! Type-safe bindings for Zircon status.

use fuchsia_zircon_sys as sys;
use std::error;
use std::ffi::NulError;
use std::fmt;
use std::io;

pub use sys::zx_status_t;

// Creates associated constants of TypeName of the form
// `pub const NAME: TypeName = TypeName(path::to::value);`
// and provides a private `assoc_const_name` method and a `Debug` implementation
// for the type based on `$name`.
// If multiple names match, the first will be used in `name` and `Debug`.
macro_rules! assoc_values {
    ($typename:ident, [$($(#[$attr:meta])* $name:ident = $value:path;)*]) => {
        #[allow(non_upper_case_globals)]
        impl $typename {
            $(
                $(#[$attr])*
                pub const $name: $typename = $typename($value);
            )*

            fn assoc_const_name(&self) -> Option<&'static str> {
                match self.0 {
                    $(
                        $(#[$attr])*
                        $value => Some(stringify!($name)),
                    )*
                    _ => None,
                }
            }
        }

        impl ::std::fmt::Debug for $typename {
            fn fmt(&self, f: &mut ::std::fmt::Formatter<'_>) -> ::std::fmt::Result {
                f.write_str(concat!(stringify!($typename), "("))?;
                match self.assoc_const_name() {
                    Some(name) => f.write_str(&name)?,
                    None => ::std::fmt::Debug::fmt(&self.0, f)?,
                }
                f.write_str(")")
            }
        }
    }
}

/// Status type indicating the result of a Fuchsia syscall.
///
/// This type is generally used to indicate the reason for an error.
/// While this type can contain `Status::OK` (`ZX_OK` in C land), elements of this type are
/// generally constructed using the `ok` method, which checks for `ZX_OK` and returns a
/// `Result<(), Status>` appropriately.
#[derive(Copy, Clone, Ord, PartialOrd, Eq, PartialEq, Hash)]
#[repr(transparent)]
pub struct Status(sys::zx_status_t);
impl Status {
    /// Returns `Ok(())` if the status was `OK`,
    /// otherwise returns `Err(status)`.
    pub fn ok(raw: sys::zx_status_t) -> Result<(), Status> {
        if raw == Status::OK.0 {
            Ok(())
        } else {
            Err(Status(raw))
        }
    }

    pub fn from_raw(raw: sys::zx_status_t) -> Self {
        Status(raw)
    }

    pub fn into_raw(self) -> sys::zx_status_t {
        self.0
    }
}

assoc_values!(Status, [
    OK                     = sys::ZX_OK;
    INTERNAL               = sys::ZX_ERR_INTERNAL;
    NOT_SUPPORTED          = sys::ZX_ERR_NOT_SUPPORTED;
    NO_RESOURCES           = sys::ZX_ERR_NO_RESOURCES;
    NO_MEMORY              = sys::ZX_ERR_NO_MEMORY;
    INTERRUPTED_RETRY      = sys::ZX_ERR_INTERRUPTED_RETRY;
    INVALID_ARGS           = sys::ZX_ERR_INVALID_ARGS;
    BAD_HANDLE             = sys::ZX_ERR_BAD_HANDLE;
    WRONG_TYPE             = sys::ZX_ERR_WRONG_TYPE;
    BAD_SYSCALL            = sys::ZX_ERR_BAD_SYSCALL;
    OUT_OF_RANGE           = sys::ZX_ERR_OUT_OF_RANGE;
    BUFFER_TOO_SMALL       = sys::ZX_ERR_BUFFER_TOO_SMALL;
    BAD_STATE              = sys::ZX_ERR_BAD_STATE;
    TIMED_OUT              = sys::ZX_ERR_TIMED_OUT;
    SHOULD_WAIT            = sys::ZX_ERR_SHOULD_WAIT;
    CANCELED               = sys::ZX_ERR_CANCELED;
    PEER_CLOSED            = sys::ZX_ERR_PEER_CLOSED;
    NOT_FOUND              = sys::ZX_ERR_NOT_FOUND;
    ALREADY_EXISTS         = sys::ZX_ERR_ALREADY_EXISTS;
    ALREADY_BOUND          = sys::ZX_ERR_ALREADY_BOUND;
    UNAVAILABLE            = sys::ZX_ERR_UNAVAILABLE;
    ACCESS_DENIED          = sys::ZX_ERR_ACCESS_DENIED;
    IO                     = sys::ZX_ERR_IO;
    IO_REFUSED             = sys::ZX_ERR_IO_REFUSED;
    IO_DATA_INTEGRITY      = sys::ZX_ERR_IO_DATA_INTEGRITY;
    IO_DATA_LOSS           = sys::ZX_ERR_IO_DATA_LOSS;
    IO_OVERRUN             = sys::ZX_ERR_IO_OVERRUN;
    IO_MISSED_DEADLINE     = sys::ZX_ERR_IO_MISSED_DEADLINE;
    IO_INVALID             = sys::ZX_ERR_IO_INVALID;
    BAD_PATH               = sys::ZX_ERR_BAD_PATH;
    NOT_DIR                = sys::ZX_ERR_NOT_DIR;
    NOT_FILE               = sys::ZX_ERR_NOT_FILE;
    FILE_BIG               = sys::ZX_ERR_FILE_BIG;
    NO_SPACE               = sys::ZX_ERR_NO_SPACE;
    NOT_EMPTY              = sys::ZX_ERR_NOT_EMPTY;
    STOP                   = sys::ZX_ERR_STOP;
    NEXT                   = sys::ZX_ERR_NEXT;
    ASYNC                  = sys::ZX_ERR_ASYNC;
    PROTOCOL_NOT_SUPPORTED = sys::ZX_ERR_PROTOCOL_NOT_SUPPORTED;
    ADDRESS_UNREACHABLE    = sys::ZX_ERR_ADDRESS_UNREACHABLE;
    ADDRESS_IN_USE         = sys::ZX_ERR_ADDRESS_IN_USE;
    NOT_CONNECTED          = sys::ZX_ERR_NOT_CONNECTED;
    CONNECTION_REFUSED     = sys::ZX_ERR_CONNECTION_REFUSED;
    CONNECTION_RESET       = sys::ZX_ERR_CONNECTION_RESET;
    CONNECTION_ABORTED     = sys::ZX_ERR_CONNECTION_ABORTED;
]);

impl Status {
    pub fn into_io_error(self) -> io::Error {
        self.into()
    }

    pub fn from_result(res: Result<(), Self>) -> Self {
        res.into()
    }
}

impl From<io::ErrorKind> for Status {
    fn from(kind: io::ErrorKind) -> Self {
        use std::io::ErrorKind::*;
        match kind {
            NotFound => Status::NOT_FOUND,
            PermissionDenied => Status::ACCESS_DENIED,
            ConnectionRefused => Status::IO_REFUSED,
            ConnectionAborted => Status::PEER_CLOSED,
            AddrInUse => Status::ALREADY_BOUND,
            AddrNotAvailable => Status::UNAVAILABLE,
            BrokenPipe => Status::PEER_CLOSED,
            AlreadyExists => Status::ALREADY_EXISTS,
            WouldBlock => Status::SHOULD_WAIT,
            InvalidInput => Status::INVALID_ARGS,
            TimedOut => Status::TIMED_OUT,
            Interrupted => Status::INTERRUPTED_RETRY,
            UnexpectedEof | WriteZero | ConnectionReset | NotConnected | Other | _ => Status::IO,
        }
    }
}

impl From<Status> for io::ErrorKind {
    fn from(status: Status) -> io::ErrorKind {
        use std::io::ErrorKind::*;
        match status {
            Status::INTERRUPTED_RETRY => Interrupted,
            Status::BAD_HANDLE => BrokenPipe,
            Status::TIMED_OUT => TimedOut,
            Status::SHOULD_WAIT => WouldBlock,
            Status::PEER_CLOSED => ConnectionAborted,
            Status::NOT_FOUND => NotFound,
            Status::ALREADY_EXISTS => AlreadyExists,
            Status::ALREADY_BOUND => AlreadyExists,
            Status::UNAVAILABLE => AddrNotAvailable,
            Status::ACCESS_DENIED => PermissionDenied,
            Status::IO_REFUSED => ConnectionRefused,
            Status::IO_DATA_INTEGRITY => InvalidData,

            Status::BAD_PATH | Status::INVALID_ARGS | Status::OUT_OF_RANGE | Status::WRONG_TYPE => {
                InvalidInput
            }

            Status::OK
            | Status::NEXT
            | Status::STOP
            | Status::NO_SPACE
            | Status::FILE_BIG
            | Status::NOT_FILE
            | Status::NOT_DIR
            | Status::IO_DATA_LOSS
            | Status::IO
            | Status::CANCELED
            | Status::BAD_STATE
            | Status::BUFFER_TOO_SMALL
            | Status::BAD_SYSCALL
            | Status::INTERNAL
            | Status::NOT_SUPPORTED
            | Status::NO_RESOURCES
            | Status::NO_MEMORY
            | _ => Other,
        }
    }
}

impl fmt::Display for Status {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self.assoc_const_name() {
            Some(name) => name.fmt(f),
            None => write!(f, "Unknown zircon status code: {}", self.0),
        }
    }
}

impl error::Error for Status {}

impl From<io::Error> for Status {
    fn from(err: io::Error) -> Status {
        err.kind().into()
    }
}

impl From<Status> for io::Error {
    fn from(status: Status) -> io::Error {
        io::Error::from(io::ErrorKind::from(status))
    }
}

impl From<NulError> for Status {
    fn from(_error: NulError) -> Status {
        Status::INVALID_ARGS
    }
}

impl From<Result<(), Status>> for Status {
    fn from(res: Result<(), Status>) -> Status {
        match res {
            Ok(()) => Self::OK,
            Err(status) => status,
        }
    }
}

#[cfg(test)]
mod test {
    use super::Status;

    #[test]
    fn status_debug_format() {
        let cases = [
            ("Status(OK)", Status::OK),
            ("Status(BAD_SYSCALL)", Status::BAD_SYSCALL),
            ("Status(NEXT)", Status::NEXT),
            ("Status(-5050)", Status(-5050)),
        ];
        for &(expected, value) in &cases {
            assert_eq!(expected, format!("{:?}", value));
        }
    }
}
